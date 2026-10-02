#!/usr/bin/env python3
"""Generate the independent, Init-only NP-completeness target.

This is a layout-aware extractor for the named declarations in this project,
not a general Lean parser or a replacement for the official Comparator.
`--check` detects drift without changing a file. In particular, keep `step`
before `run`: Lean reuses its generated matcher when elaborating `run`, and the
independent statement must reproduce those auxiliary declaration names too.
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


def declarations(path: str, names: list[str]) -> str:
    source = without_comments((ROOT / path).read_text(encoding="utf-8"))
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
        # Remove trailing whitespace left by erased documentation comments.
        found[name] = "\n".join(line.rstrip() for line in chunk.splitlines()).strip()
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
Independent target statement for SAT and 3-SAT NP-completeness.

NP uses polynomial-length binary certificates checked by a deterministic finite
single-tape machine. Reductions are total polynomial-time machine computations.
SAT is encoded CNF satisfiability; 3-SAT means clauses of at most three literals.
The unary prefix encoding and malformed-input rejection are specified below.

The two intentional theorem holes are the submission targets. This independent
statement imports no project modules and is never imported by the proof library.
Solution.lean imports the completed proofs in a separate Lean environment.
Regenerate with `python3 scripts/generate_challenge.py` after definition edits;
`--check` checks source drift. Official comparison remains a separate check.
-/

@[expose] public section

namespace Complexity
""",
        declarations(machine, ["Symbol", "Move", "Tape"]),
        "namespace Tape",
        declarations(machine, ["read", "write", "move", "ofInput", "bits", "output", "size"]),
        "end Tape",
        declarations(machine, [
            "Instruction", "Instruction.mapState", "Machine", "Config", "initial",
            "step", "run", "runInput",
        ]),
        declarations("Complexity/Classes.lean", [
            "Word", "Language", "powerBound", "pairWords", "Accepts",
            "PolynomialTimeMachine", "PolyTime", "InP", "InNP", "PolyRed", "NPHard", "NPComplete",
        ]),
        "end Complexity\n\nnamespace Complexity.SAT",
        declarations(sat, [
            "Word", "Assignment", "Literal", "Clause", "CNF", "evalLiteral", "evalClause",
            "evalCNF", "Satisfiable", "IsThreeCNF", "Parser", "writeNat", "readNat",
            "writeValues", "readMany", "writeList", "readList", "encodeLiteral", "readLiteral",
            "encodeClause", "readClause", "encode", "readCNF", "decode", "SAT", "ThreeSAT",
        ]),
        """end Complexity.SAT

namespace Complexity

/-- Cook–Levin: encoded CNF satisfiability is NP-complete. -/
theorem sat_np_complete : NPComplete SAT.SAT := by
  sorry

/-- Encoded 3-CNF satisfiability is NP-complete. -/
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
