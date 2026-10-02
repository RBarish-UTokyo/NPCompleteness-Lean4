# Verification record

The checks below were run by Claude Opus 5.5 on Linux, from a clean build directory, with
`scripts/palomar_dryrun.sh --paranoid`. They rehearse Palomar's mechanical verification; they
are not Palomar's verification, which runs on Palomar's own runner at the submitted commit.

## What was checked

The Lean sources, Lake files and Comparator configuration had this fingerprint (recompute with
the command below; documentation changes do not affect it):

```sh
git ls-files -- '*.lean' lakefile.toml lake-manifest.json lean-toolchain comparator.json \
  | sort | xargs sha256sum | sha256sum
# b6ce2daf7b01e731c15294f0a65f46d54767406dc6d3216aac8b5a6e5d65453b
```

| File | SHA-256 |
| --- | --- |
| `Challenge.lean` (300 lines, 11,485 bytes) | `216993eec75eec83c91426d1dbc1b060f531906824aa1571e8b7595b5b7ec6ec` |
| `Solution.lean` | `c54cd2debf579c282a7cc334cad1350b27fb63a5bda67001145fba271c5c02f7` |
| `comparator.json` | `7e9fb5af786eb1502d18983d4b14685409dca3849b38f7ce7a15a5f2eefa2145` |

## Tools

Lean `leanprover/lean4:v4.35.0-rc2` (commit `11acb17ec6b07a8f9e9173e6845197929540936b`),
installed by elan, with bubblewrap and Python 3. SHA-256 of the executables used:

| Tool | SHA-256 |
| --- | --- |
| `lean` | `bf8d54e4714cc4b03d3f6bb34c83b7202b87e49c8bfcbff6895c085bb90ceb38` |
| `lake` | `8ba83c98f76562d03b8dbc33f1057151ba6cbb121679dde76b2260ccc90495e1` |
| `leanexport` | `c5bc1a10a21e22cbb3671d65987cdef2076833b14182d823ccb2153adf2fa954` |
| `leanchecker` | `9e36e955a251b1313c8eb5b7fa101282d51df109d34d8bb7c1cfdf51985aba29` |
| `leanchecker-paranoid` | `ccd20c9ba4ad795e0969b9cd2dc386e58e4d885f7dcde6ce9d32101634ccb744` |
| `lean4lean` | `baaec030a70c78562ced2c75866ab0d2410e81ce680b835179ed16570ad5ef97` |
| `nanoda_bin` | `8241c5e6baa29490aa118d382f97961b208ae730fdb96545c2abed74c9ece5a8` |
| `con-leche` | `a6380d68b4fb364189821dd4692569c11536de0a1e3aaefea06028c0d67bb193` |
| `con-ron` | `4e5616d94374cae37324dad2594f6230c2bb2297240249fc78ff508f3bc5acef` |

The digests of `lean`, `lake`, `leanexport`, `leanchecker`, `nanoda_bin` and `con-ron` are the
ones Palomar's public registry records for its own runs on this Lean release, so the same builds
of these tools were used.

## Results

| Step | Command | Result |
| --- | --- | --- |
| Preflight | `python3 scripts/check_submission.py` | passed |
| Build | `lake build` | 84 jobs, no errors and no warnings; `Audit.lean`: 3,793 `Complexity` declarations use only `propext`, `Classical.choice`, `Quot.sound` |
| Statement | `lake build Challenge` | builds; the only warnings are the two deliberate `sorry`s |
| Replay | `lake check` | Lean's kernel accepts the solution; axioms `propext`, `Quot.sound`, `Classical.choice` |
| Comparator | `lake comparator --config comparator.json --paranoid` | "Your solution is okay!" |

In the Comparator run, which builds and exports both modules inside the bubblewrap sandbox
without network access, these kernels each accepted the exported proof of both theorems:
NanoDa, Lean's kernel in paranoid mode (`leanchecker-paranoid`), lean4lean, con-leche, con-ron,
and Lean's default kernel. The whole run took about five minutes. Comparator's default mode (NanoDa and
Lean's kernel, as Palomar runs it) also passed, both on the delivered sources and on the revised
statement.

`#print axioms Complexity.sat_np_complete` and `#print axioms Complexity.threeSAT_np_complete`
both print `[propext, Classical.choice, Quot.sound]`.

## Continuous integration

The workflow `.github/workflows/verify.yml` runs the same steps on GitHub's `ubuntu-22.04`
runner. It passed on an earlier revision of these sources (before `powerBound` was rewritten
with `Nat.pow`, below), ending with "Your solution is okay!".

## Downstream reuse with Mathlib

A mock downstream project checked that later Palomar entries can reuse the statement. Its
Lakefile requires Mathlib at tag v4.35.0-rc2 and this repository as a contained path
dependency. Its `Challenge.lean` imports all of Mathlib, copies the definitions of this
`Challenge.lean` verbatim, defines a language with a Mathlib notion (`Even`), and states two
theorems with `sorry`: that 3-SAT is NP-hard, and a reduction involving the new language. Its
`Solution.lean` imports Mathlib and `Complexity` and proves both from the library.

The first attempt failed: Comparator reported that `Complexity.PolyRed` did not match. Printing
the elaborated definitions with and without Mathlib showed that only `powerBound` differed:
with Mathlib imported, `(n + 1) ^ k` on `Nat` elaborates through Mathlib's monoid instance
(`Monoid.toNPow`) instead of core's `instPowNat`. With `powerBound` written as
`c * Nat.pow (n + 1) k`, all definitions elaborate identically, and `lake comparator` on the
mock project prints "Your solution is okay!".

## Reproducing

```sh
scripts/palomar_dryrun.sh --paranoid     # logs in .lake/dryrun/
```

The GitHub workflow `.github/workflows/verify.yml` runs the same steps on every push.
