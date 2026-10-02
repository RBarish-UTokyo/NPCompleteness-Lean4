# Submitting to Palomar

This page records how the repository meets the
[Palomar](https://palomar-registry.org/how-to-submit) submission standard, the submission
steps, and what submitting publishes.

## What is ready

| Requirement (Palomar submission standard) | Here |
| --- | --- |
| `lean-toolchain` pins a supported Lean release | `leanprover/lean4:v4.35.0-rc2` |
| Exactly one Lakefile, committed `lake-manifest.json` | `lakefile.toml`; no dependencies |
| Every Lean file uses `module`, at most 10,000 lines | checked by `scripts/check_submission.py` |
| Challenge at most 1,000 lines and 100 KiB (warning above 300 lines or 32 KiB) | 464 lines, about 19 KiB: Palomar will give its non-blocking size warning (over 300 lines) |
| Challenge imports resolve to Lean core or the allowlisted Mathlib or Tau Ceti | `Init` only |
| `comparator.json` with the accepted keys and axioms | eight theorems; `propext`, `Quot.sound`, `Classical.choice` |
| Exactly one licence file, matching `project.license` | `LICENSE`, Apache-2.0 |
| `formalization.yaml` (v0.4) with Palomar's mandatory fields | validated against the v0.4 schema and by the preflight |
| Narrative account: theorems, sources, limitations, AI use, review, licence | `README.md`, `formalization.yaml`, docstrings in `Challenge.lean` |
| Comparator accepts with NanoDa | `scripts/palomar_dryrun.sh`; see `docs/VERIFICATION.md` |

## Submission steps

1. Check the people and the credits. `project.authors` and `project.responsible_maintainers`
   in `formalization.yaml` name the responsible people (Palomar reserves these fields for
   humans); `python3 scripts/check_submission.py --submission` rejects placeholder names.
   Read `Challenge.lean`, and check the AI credits in `formalization.yaml` (`automation`) and
   in the README.
2. Use a public repository. Palomar fetches only public GitHub repositories. The
   repository root is the Lean project, so no project path is needed.
3. Fix the commit. Merge the work into the branch you want, push, and let the workflow
   "Verify Lean and Comparator" pass on that exact commit. Record the full 40-character SHA
   (`git rev-parse HEAD`). Any later change, even to metadata, needs a new commit and a new
   submission.
4. Submit at <https://submit.palomar-registry.org/>: the repository, the SHA, Comparator
   path `comparator.json`, and your relationship to the work (responsible author or maintainer).
   Keep the status-page link; it is the only way back to the submission.

## What becomes public, and when

From the moment of submission: the repository, the commit, and the public GitHub Actions run of
Palomar's mechanical verification, with the declared authorization relationship. The automated
editorial review stays non-public unless you register; if it finds no blocking problem you
choose between registering (permanent: the record, the redacted review and preservation forks
of the repository become public) and withdrawing.

## Expect the review to weigh

* Research interest and prior work: Palomar's editorial review asks whether the result could
  warrant a research paper and has a credible audience. The Cook–Levin theorem is central to
  complexity theory, and its mechanizations have been published (ITP 2021, the Archive of Formal
  Proofs). But several complete mechanizations exist, including Complexitylib in Lean 4 (see
  "Other formalizations" in the README); the metadata states this and claims no priority.
* Encoding choices: unary variable indices and the "at most three literals" convention are
  disclosed in `formalization.yaml` (`fidelity`) and the README.
