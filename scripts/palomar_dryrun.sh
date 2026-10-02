#!/usr/bin/env bash
# Rehearse Palomar's mechanical verification locally.
#
#   scripts/palomar_dryrun.sh [--paranoid]
#
# Runs the submission preflight, the default build (library, axiom audit,
# Solution and examples), the Challenge build, `lake check`, and the sandboxed
# `lake comparator` with NanoDa, as Palomar does. With --paranoid, Comparator
# also runs every other checker bundled with Lean (leanchecker-paranoid,
# lean4lean, con-leche and con-ron). Needs elan, python3 and bubblewrap (bwrap);
# PyYAML enables the metadata checks. Logs go to .lake/dryrun/.
set -euo pipefail

cd "$(dirname "$0")/.."
comparator_flags=()
if [[ "${1:-}" == "--paranoid" ]]; then
  comparator_flags+=(--paranoid)
elif [[ $# -gt 0 ]]; then
  echo "usage: $0 [--paranoid]" >&2
  exit 2
fi

logs=.lake/dryrun
mkdir -p "$logs"
# Comparator finds NanoDa and the other checkers on PATH; they ship with Lean.
PATH="$(lean --print-prefix)/bin:$PATH"
export PATH

step() {
  local name=$1
  shift
  echo "== $name: $*"
  if ! "$@" > "$logs/$name.log" 2>&1; then
    tail -n 40 "$logs/$name.log"
    echo "FAILED: $name (full log in $logs/$name.log)" >&2
    exit 1
  fi
  tail -n 3 "$logs/$name.log"
}

step preflight python3 scripts/check_submission.py
step build lake build
step challenge lake build Challenge
step check lake check
step comparator lake comparator --config comparator.json "${comparator_flags[@]}"
echo "All checks passed."
