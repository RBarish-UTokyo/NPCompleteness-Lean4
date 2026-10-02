#!/usr/bin/env python3
"""Generate the independent, Init-only NP-completeness target.

This is a layout-aware extractor for the named declarations in this project,
not a general Lean parser or a replacement for the official Comparator.
Each declaration is copied with the documentation comment that immediately
precedes it in the source, so the Challenge and the library share docstrings.
Other comments are dropped. `--check` detects drift without changing a file.
In particular, keep `step` before `run`: Lean reuses its generated matcher when
elaborating `run`, and the independent statement must reproduce those
auxiliary declaration names too.
"""
from __future__ import annotations

import argparse
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[1]


def without_comments(source: str) -> str:
    """Remove nested Lean comments, preserving newlines and quoted strings."""
    result: list[str] = []
    index = 0
    block_depth = 0
    in_string = False
    escaped = False
    while index < len(source):
        char = source[index]
        pair = source[index:index + 2]
        if block_depth:
            if pair == "/-":
                block_depth += 1
                result.extend("  ")
                index += 2
            elif pair == "-/":
                block_depth -= 1
                result.extend("  ")
                index += 2
            else:
                result.append("\n" if char == "\n" else " ")
                index += 1
        elif in_string:
            result.append(char)
            index += 1
            if escaped:
                escaped = False
            elif char == "\\":
                escaped = True
            elif char == '"':
                in_string = False
        elif pair == "/-":
            block_depth = 1
            result.extend("  ")
            index += 2
        elif pair == "--":
            end = source.find("\n", index)
            if end == -1:
                result.extend(" " * (len(source) - index))
                break
            result.extend(" " * (end - index))
            index = end
        else:
            result.append(char)
            index += 1
            if char == '"':
                in_string = True
    if block_depth or in_string:
        raise ValueError("Unterminated comment or string in selected source")
    return "".join(result)


BOUNDARY = re.compile(
    r"^(?:@\[[^\n]*\]\s*)?(?:(?:public|private|protected|noncomputable|unsafe)\s+)*"
    r"(?:def|abbrev|structure|inductive|theorem|lemma|instance|namespace|end|"
    r"section|open|set_option|attribute|notation|macro|syntax|example|mutual)\b",
    re.M,
)
DECLARATION = re.compile(
    r"(?:@\[[^\n]*\]\s*)?(?:(?:public|private|protected|noncomputable|unsafe)\s+)*"
    r"(?:def|abbrev|structure|inductive)\s+([\w'.]+)\b"
)


DOCSTRING_BEFORE = re.compile(r"/--(?:(?!-/).)*-/\s*\Z", re.S)


def docstring_before(original: str, start: int) -> str:
    """The documentation comment ending just before offset `start`, if any."""
    match = DOCSTRING_BEFORE.search(original, 0, start)
    return match.group(0).rstrip() + "\n" if match else ""


DERIVING = re.compile(r"\n[ \t]*deriving [^\n]*")


def declarations(path: str, names: list[str], sep: str = "\n\n") -> str:
    original = (ROOT / path).read_text(encoding="utf-8")
    # `without_comments` preserves offsets, so positions agree with `original`.
    source = without_comments(original)
    starts = [match.start() for match in BOUNDARY.finditer(source)]
    found: dict[str, str] = {}
    for start, end in zip(starts, starts[1:] + [len(source)]):
        chunk = source[start:end].strip()
        match = DECLARATION.match(chunk)
        if match is None:
            continue
        name = match.group(1)
        if name in found:
            raise ValueError(f"Ambiguous declaration {name!r} in {path}")
        # Remove trailing whitespace left by erased comments.
        body = "\n".join(line.rstrip() for line in chunk.splitlines()).strip()
        # `deriving` clauses only add instances, which the theorems do not mention.
        body = DERIVING.sub("", body)
        found[name] = docstring_before(original, start) + body
    missing = [name for name in names if name not in found]
    if missing:
        raise ValueError(f"Missing declarations in {path}: {', '.join(missing)}")
    return sep.join(found[name] for name in names)


def challenge_text() -> str:
    machine = "Complexity/Machine.lean"
    sat = "Complexity/SAT.lean"
    variants = "Complexity/SATVariants.lean"
    pair = "\n"
    parts = [
        """module

public import Init

/-!
# NP-completeness of SAT and of variants of SAT

For one machine model and concrete binary codes of CNF formulas, the theorems at the end
state that SAT, 3-SAT (at most three literals per clause), exactly-3-SAT (exactly three, on
distinct variables), (≤1,≤2)-SAT and SAT with binary variable indices are NP-complete: in NP,
and every language in NP reduces to them by a polynomial-time many-one reduction. A last
theorem states that NP, defined by verifiers, is nondeterministic polynomial time.

* Machines: deterministic single-tape Turing machines over {blank, 0, 1, separator}; time is
  the number of steps, the halting step included. `NMachine` has two transition tables.
* Polynomial bounds are `c * (n + 1) ^ k`. A computed function leaves its output from the
  head onward; an NP verifier gets instance and certificate as `pairWords x w`.
* Formulas: variables are natural numbers, a clause is a list of literals, a formula a list
  of clauses. `encode` writes indices and lengths in unary, `encodeBinary` indices in binary.
  Words coding no formula belong to none of the languages.

Only Lean core is imported. `scripts/generate_challenge.py` generates this file from the
library; `Solution.lean` proves the theorems without importing it.
-/

@[expose] public section

namespace Complexity
""",
        declarations(machine, ["Symbol", "Move", "Tape"]),
        "namespace Tape",
        declarations(machine, ["read", "write", "move", "ofInput", "bits", "output"]),
        "end Tape",
        declarations(machine, [
            "Instruction", "Machine", "Config", "initial", "step", "run", "runInput",
        ]),
        declarations("Complexity/Classes.lean", ["Word", "Language"], pair),
        declarations("Complexity/Classes.lean", [
            "powerBound", "pairWords", "Accepts",
            "PolynomialTimeMachine", "PolyTime", "InNP", "PolyRed", "NPHard", "NPComplete",
        ]),
        "end Complexity\n\nnamespace Complexity.SAT",
        declarations(sat, ["Word", "Assignment"], pair),
        declarations(sat, ["Literal"]),
        declarations(sat, ["Clause", "CNF"], pair),
        declarations(sat, [
            "evalLiteral", "evalClause", "evalCNF", "Satisfiable", "IsThreeCNF",
            "writeNat", "writeValues", "writeList", "encodeLiteral",
        ]),
        declarations(sat, ["encodeClause", "encode"], pair),
        declarations(sat, ["SAT", "ThreeSAT"]),
        declarations(variants, [
            "IsExactThreeCNF", "ExactThreeSAT", "IsLeOneLeTwoCNF", "LeOneLeTwoSAT",
            "binaryValue", "BinaryLiteral", "BinaryLiteral.toLiteral", "encodeBinaryLiteral",
            "encodeBinary", "BinarySAT",
        ]),
        "end Complexity.SAT\n\nnamespace Complexity",
        declarations("Complexity/Nondeterministic.lean", [
            "NMachine", "NMachine.run", "NondeterministicPolyTime",
        ]),
        """/-- **Cook–Levin theorem.** SAT is NP-complete. -/
theorem sat_np_complete : NPComplete SAT.SAT := by sorry

/-- 3-SAT is NP-complete. -/
theorem threeSAT_np_complete : NPComplete SAT.ThreeSAT := by sorry

/-- Exactly-3-SAT is NP-complete. -/
theorem exactThreeSAT_np_complete : NPComplete SAT.ExactThreeSAT := by sorry

/-- (≤1,≤2)-SAT is NP-complete. -/
theorem leOneLeTwoSAT_np_complete : NPComplete SAT.LeOneLeTwoSAT := by sorry

/-- SAT with binary variable indices is NP-complete. -/
theorem binarySAT_np_complete : NPComplete SAT.BinarySAT := by sorry

/-- NP, defined by verifiers, is nondeterministic polynomial time. -/
theorem inNP_iff_nondeterministicPolyTime (L : Language) :
    InNP L ↔ NondeterministicPolyTime L := by sorry

end Complexity
""",
    ]
    return "\n\n".join(part.strip() for part in parts) + "\n"


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="fail if Challenge.lean needs regeneration")
    args = parser.parse_args()
    text = challenge_text()
    destination = ROOT / "Challenge.lean"
    if args.check:
        if not destination.exists() or destination.read_text(encoding="utf-8") != text:
            print("Challenge.lean differs from its source declarations; regenerate it.", file=sys.stderr)
            return 1
        print("Challenge.lean matches its selected source declarations.")
    else:
        destination.write_text(text, encoding="utf-8")
        print("Generated Challenge.lean (independent statement; one intentional hole per theorem).")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
