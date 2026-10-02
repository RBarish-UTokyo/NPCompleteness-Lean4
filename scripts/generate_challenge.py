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


def declarations(path: str, names: list[str]) -> str:
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
        found[name] = docstring_before(original, start) + body
    missing = [name for name in names if name not in found]
    if missing:
        raise ValueError(f"Missing declarations in {path}: {', '.join(missing)}")
    return "\n\n".join(found[name] for name in names)


def challenge_text() -> str:
    machine = "Complexity/Machine.lean"
    sat = "Complexity/SAT.lean"
    parts = [
        """module

public import Init

/-!
# SAT and 3-SAT are NP-complete

This file states the Cook–Levin theorem and its 3-SAT form, for a concrete
machine model and a concrete binary encoding of CNF formulas:

* `Complexity.sat_np_complete`: SAT, the set of codes of satisfiable CNF
  formulas, is NP-complete.
* `Complexity.threeSAT_np_complete`: 3-SAT, the set of codes of satisfiable
  CNF formulas with at most three literals per clause, is NP-complete.

NP-complete means: in NP, and every language in NP reduces to it by a
polynomial-time many-one (Karp) reduction.

## Reading guide

* Machines (`Machine`, `run`): deterministic Turing machines with one two-way
  infinite tape over the alphabet {blank, 0, 1, separator} and finitely many
  control states. Each step either halts with a Boolean decision, or writes the
  scanned cell, moves the head at most one cell, and changes state. Time is the
  number of steps, the halting step included.
* Complexity (`PolynomialTimeMachine`, `PolyTime`, `InNP`, `PolyRed`, `NPHard`,
  `NPComplete`): languages are sets of binary words, and polynomial bounds
  are `c * (n + 1) ^ k`. A polynomial-time function leaves its output on the
  tape, from the head onward. NP is defined by polynomial-time verifiers and
  polynomially bounded certificates, given to the verifier as `pairWords x w`.
* Formulas (`Complexity.SAT`): variables are natural numbers, a clause is a list
  of literals, a CNF formula is a list of clauses. `encode` writes variable
  indices and list lengths in unary and a literal's sign as one bit. A word that
  is not the code of a formula belongs to neither language. 3-SAT allows clauses
  with fewer than three literals, repeated literals, and empty clauses.

Only Lean core is imported. `Solution.lean` proves both theorems without importing
this file, which `scripts/generate_challenge.py` generates from the library sources.
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
        declarations("Complexity/Classes.lean", [
            "Word", "Language", "powerBound", "pairWords", "Accepts",
            "PolynomialTimeMachine", "PolyTime", "InNP", "PolyRed", "NPHard", "NPComplete",
        ]),
        "end Complexity\n\nnamespace Complexity.SAT",
        declarations(sat, [
            "Word", "Assignment", "Literal", "Clause", "CNF", "evalLiteral", "evalClause",
            "evalCNF", "Satisfiable", "IsThreeCNF", "writeNat", "writeValues", "writeList",
            "encodeLiteral", "encodeClause", "encode", "SAT", "ThreeSAT",
        ]),
        """end Complexity.SAT

namespace Complexity

/-- **Cook–Levin theorem.** SAT is NP-complete: it is in NP, and every language
in NP reduces to it by a polynomial-time many-one reduction. -/
theorem sat_np_complete : NPComplete SAT.SAT := by
  sorry

/-- **3-SAT is NP-complete**: in NP, and every language in NP reduces to it by a
polynomial-time many-one reduction. -/
theorem threeSAT_np_complete : NPComplete SAT.ThreeSAT := by
  sorry

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
        print("Generated Challenge.lean (independent statement; two intentional theorem holes).")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
