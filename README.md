# NP-completeness of SAT and its variants: the Cook–Levin theorem in Lean 4

A Lean 4 proof that **SAT, 3-SAT, exactly-3-SAT, (≤1,≤2)-SAT, SAT with binary variable
indices, planar 3-SAT and Lichtenstein's planar 3-SAT are NP-complete**, and that **NP equals
nondeterministic polynomial time**, for an
explicit Turing-machine model, with every running time proved by counting machine steps. The development uses only Lean's
core library (no Mathlib, no other package), and it is packaged for the
[Palomar registry](https://palomar-registry.org/how-to-submit): the statement is the
self-contained `Challenge.lean`, the proof is `Solution.lean`, and `comparator.json` tells
Comparator to check that they agree.

**Status.** All eight compared theorems are proved; no Lean file of the proof contains `sorry`,
and the proof depends only on the axioms `propext`, `Classical.choice` and `Quot.sound`. On the pinned Lean
release (v4.35.0-rc2), a rehearsal of Palomar's mechanical verification passes: `lake build`,
`lake check`, and the sandboxed `lake comparator --paranoid`, in which Lean's kernel and the
independent checkers leanchecker (paranoid mode), lean4lean, NanoDa, con-leche and con-ron all
accept the proof ("Your solution is okay!"). [docs/VERIFICATION.md](docs/VERIFICATION.md)
records these runs. The repository has not been submitted to Palomar.

## AI disclosure

This development was written by AI, under human direction.

* **GPT-6 Astra** (OpenAI), working as cooperating agents in OpenAI Codex, wrote the
  mathematical development: every definition and proof of the `Complexity` library (74 modules,
  about 17,000 lines), the Challenge generator, and the first version of the documentation and
  Palomar packaging. It delivered them as an archive, together with validation records made in a
  restricted environment where the `lean` executable could not start (see
  [History](#history-of-this-repository)).
* **Claude Opus 5.5** (Anthropic), working as an agent in Claude Code, did everything after:
  the first ordinary Lake build, `lake check` and sandboxed Comparator runs; revisions of the
  statement for auditability (a docstring for every definition of `Challenge.lean`, SAT and
  3-SAT defined as images of the encoder instead of through a parser, unused definitions dropped
  from the Challenge), with the lemmas they needed; the sanity checks in
  `Examples/Sanity.lean`; fixes to the CI workflow and linter warnings; the survey of earlier
  formalizations; the metadata and this documentation. It then stated the variants of SAT and
  the nondeterministic characterization of NP, checked that every new definition elaborates
  identically when Mathlib is imported, and had separate Claude Opus 5.5 subagents prove them,
  each in its own git worktree (`Complexity/Restricted/`,
  `Complexity/Binary/`, `Complexity/NTM/`, `Complexity/Planar/`, about 23,900 lines). Each result was reviewed
  (new files only, no forbidden constructs, standard axioms, clean build) before it was merged.
* A human maintainer set the task and its constraints.

No human has reviewed the mathematics. So please don't take the theorem on anyone's authority.
The part a person has to read is the statement, `Challenge.lean`: 464 lines of elementary,
documented definitions that import nothing but Lean core (see [What it proves](#what-it-proves)).
Everything else is checked by machine, by Lean's kernel and by independently written checkers.

## What it proves

`Challenge.lean` states the eight theorems that Comparator checks, and `Solution.lean` proves
them:

```lean
theorem Complexity.sat_np_complete : NPComplete SAT.SAT
theorem Complexity.threeSAT_np_complete : NPComplete SAT.ThreeSAT
theorem Complexity.exactThreeSAT_np_complete : NPComplete SAT.ExactThreeSAT
theorem Complexity.leOneLeTwoSAT_np_complete : NPComplete SAT.LeOneLeTwoSAT
theorem Complexity.binarySAT_np_complete : NPComplete SAT.BinarySAT
theorem Complexity.planarThreeSAT_np_complete : NPComplete SAT.PlanarThreeSAT
theorem Complexity.cyclePlanarThreeSAT_np_complete : NPComplete SAT.CyclePlanarThreeSAT
theorem Complexity.inNP_iff_nondeterministicPolyTime (L : Language) :
    InNP L ↔ NondeterministicPolyTime L
```

In words: **SAT, the set of binary codes of satisfiable CNF formulas, is NP-complete, and so
are 3-SAT (at most three literals per clause), exactly-3-SAT (exactly three literals per clause,
on three distinct variables), (≤1,≤2)-SAT (two or three literals per clause, every variable
occurring at most once positively and at most twice negatively), SAT with variable indices
written in binary, planar 3-SAT (the variable–clause incidence graph is planar), and
Lichtenstein's planar 3-SAT (planar even with a cycle through the variables). NP, defined by
verifiers, is the class of languages accepted in polynomial
time by nondeterministic machines.** NP-complete means: in NP, and every language in NP reduces
to it by a polynomial-time many-one (Karp) reduction. The definitions, all in `Challenge.lean`:

* **Machines.** A `Machine` is a deterministic Turing machine with one two-way infinite tape over
  the alphabet {blank, 0, 1, separator} and finitely many control states. For each control state
  and scanned symbol it has an instruction: halt with a Boolean decision, or write a symbol, move
  the head at most one cell and change state. `run M fuel c` runs at most `fuel` steps; time is
  the number of steps, the halting step included. An input word is written on an otherwise
  blank tape, with the head on its first cell.
* **Polynomial time.** Languages are sets of binary words (`Word → Prop`), and polynomial
  bounds are written `c * (n + 1) ^ k`. `PolynomialTimeMachine M`: on every input of length `n`,
  `M` halts within `c * (n + 1) ^ k` steps. `PolyTime f`: one machine computes `f` on every
  input within such a bound, halting with decision `true` and leaving `f x` on the tape, from
  the head up to the first non-bit cell.
* **NP.** `InNP L` is the certificate (verifier) definition: there are a polynomial-time machine
  `M` and a bound `p` such that `x ∈ L` iff `M` accepts the pair `1^|x| 0 x w` for some
  certificate `w` with `|w| ≤ p(|x|)`. `PolyRed A B`: some `f` with `PolyTime f` satisfies
  `x ∈ A ↔ f x ∈ B` for all `x`. `NPHard L`: every `InNP` language reduces to `L`.
  `NPComplete L`: `InNP L ∧ NPHard L`.
* **Formulas.** Variables are natural numbers, a literal is a variable or its negation, a clause
  is a list of literals (their disjunction), and a CNF formula is a list of clauses (their
  conjunction). `SAT.encode` codes a formula as a binary word: list lengths and variable indices
  in unary, a literal's sign as one bit. `SAT.SAT` is the set of words `encode f` with `f`
  satisfiable; `SAT.ThreeSAT` adds that every clause of `f` has at most three literals.
* **Variants.** `SAT.ExactThreeSAT` requires every clause to have exactly three literals, on
  three distinct variables (`IsExactThreeCNF`). `SAT.LeOneLeTwoSAT` requires every clause to
  have two or three literals and every variable to occur in the whole formula at most once
  positively and at most twice negatively (`IsLeOneLeTwoCNF`). `SAT.BinarySAT` uses
  `encodeBinary`, which writes each variable index in binary (least significant digit first,
  leading zeros allowed) instead of unary.
* **Planarity.** As in Gonthier's formal proof of the Four Color Theorem (Coq,
  `hypermap.v`): a `Hypermap` is three functions `edge`, `node`, `face` on darts
  `Fin n` with `node (face (edge x)) = x`; its genus comes from the Euler formula,
  `(2·components + darts − (edges + nodes + faces)) / 2`, counted with `cycleCount` and
  `componentCount`; `Planar` means genus 0. `PlanarGraph es` says that the graph with edge list
  `es` has a planar embedding: a planar hypermap on its half-edges whose `edge` pairs the two
  ends of each edge and whose `node` cycles are the half-edges at each vertex.
  `SAT.PlanarThreeSAT` asks that the `incidenceGraph` of a 3-CNF formula (an edge between
  variable `v` and clause `j` for each occurrence) be planar; `SAT.CyclePlanarThreeSAT` asks
  the same of the incidence graph plus the `variableCycle` through variables `0, 1, …, n − 1`.
* **Nondeterminism.** An `NMachine` has two transition tables and may follow either at each
  step; `NMachine.run` follows a list of choices. `NondeterministicPolyTime L`: some `NMachine`
  and polynomial `p` such that, on every input `x`, every computation path halts within `p(|x|)`
  steps, and `x ∈ L` iff some path halts with decision `true` (Arora and Barak's definition).

### Conventions and limitations

These are the choices a reader should know about; `formalization.yaml` (`fidelity`) lists them
too.

* **NP by verifiers.** NP is defined by deterministic verifiers and polynomially bounded
  certificates, as in Arora and Barak (*Computational Complexity: A Modern Approach*, ch. 2),
  except that certificates have length *at most* `p(|x|)` rather than exactly (an equivalent
  choice). Its equivalence with nondeterministic machines is proved
  (`inNP_iff_nondeterministicPolyTime`), for machines with two transition tables; the
  invariance of P and NP under other machine models (multi-tape machines, RAMs) is **not**
  proved here.
* **Karp reductions.** Cook's 1971 paper used polynomial-time Turing reductions; the many-one
  form proved here is the standard modern statement, and the stronger one.
* **CNF only, with these encodings.** SAT is CNF satisfiability, not satisfiability of
  arbitrary propositional formulas. `SAT.encode` writes variable indices in unary, so a code can
  be longer than a binary one; `SAT.BinarySAT` therefore proves the binary-index version
  NP-complete too (clause and literal counts stay in unary there, but they are at most the code
  length). Concrete file formats such as DIMACS are not treated. Words that are not codes of
  formulas are in none of the languages (`Examples/Sanity.lean` checks that the empty word and a
  code followed by extra bits are rejected).
* **Clause-size conventions.** 3-SAT allows clauses with fewer than three literals, repeated
  literals and the empty clause, as in Karp's 1972 list; exactly-3-SAT is the stricter
  convention (exactly three literals on three distinct variables). The empty formula is true,
  and a formula with an empty clause is false. In (≤1,≤2)-SAT, occurrences are counted over
  the whole formula, a repeated literal counting each time.
* **Combinatorial planarity.** Planarity is the rotation-system (genus-0 hypermap)
  definition; its equivalence with drawings in the plane is classical and not proved here.
  Graphs are given by edge lists, so loops and parallel edges are allowed (a variable occurring
  twice in a clause gives two edges). In Lichtenstein's version the cycle runs through all
  variables `0, …, n − 1` in index order, including any that do not occur.
* **Output convention.** A computed function's output is read from the final head position,
  up to the first blank or separator.

`Examples/Sanity.lean` tests the definitions: it computes a code bit by bit, decides small
instances, shows that 3-SAT is a proper restriction of SAT, and proves that an NP-hard language
has both members and nonmembers (so NP-hardness is not vacuous; in particular neither the empty
language nor the set of all words is NP-hard).

## How the proof works

```
sat_np_complete                       NPCompleteness.lean
├─ sat_inNP                           Membership.lean        explicit verifier machine
└─ sat_np_hard
   └─ InNP.polyRed_sat                NPCompleteness.lean
      ├─ inNP_emitter                 CookLevinEmitter.lean  the tableau formula is correct
      │  ├─ compile_correct           CookLevin.lean         ... for every clocked verifier
      │  └─ inNP_clocked              Clock.lean             NP verifiers with explicit clocks
      └─ polyTime_emitter             StackTableauMachineBounds.lean
                                                             ... and is emitted in polynomial time
threeSAT_np_complete                  NPCompleteness.lean
├─ threeSAT_inNP                      Membership.lean
└─ InNP.polyRed_threeSAT = InNP.polyRed_sat ⬝ sat_polyRed_threeSAT
   ├─ sat_polyRed_threeSAT            StackThreeSATReduction.lean
   │  ├─ reduceWord_correct           ChainThreeSAT.lean     the clause chains are equisatisfiable
   │  └─ chainThreeSAT_polyTime       StackThreeSATReduction.lean
   └─ PolyRed.trans                   Reductions.lean
      └─ polyTime_comp                Composition.lean       machines compose
```

(Paths are relative to `Complexity/`.)

The further theorems:

```
exactThreeSAT_np_complete             RestrictedSATComplete.lean
├─ exactThreeSAT_inNP                 Restricted/ExactMembership.lean   check, then 3-SAT verifier
└─ threeSAT_polyRed_exactThreeSAT     Restricted/ExactReduction.lean    transformed Cook–Levin generator
leOneLeTwoSAT_np_complete             RestrictedSATComplete.lean
├─ leOneLeTwoSAT_inNP                 Restricted/LeMembership.lean      occurrence counts, then 3-SAT verifier
└─ exactThreeSAT_polyRed_leOneLeTwoSAT Restricted/LeReduction.lean
binarySAT_np_complete                 BinarySATComplete.lean
├─ binarySAT_inNP                     Binary/VerifierMachine.lean       one bit per occurrence, consistency
└─ sat_polyRed_binarySAT              Binary/ReductionSemantics.lean    unary-to-binary transducer
planarThreeSAT_np_complete            PlanarSATComplete.lean
├─ planarThreeSAT_inNP                Planar/VerifierMain.lean          embedding in the certificate
└─ planarThreeSAT_npHard              Planar/Reduction.lean             grid formula, cycle edges subdivided
cyclePlanarThreeSAT_np_complete       PlanarSATComplete.lean
├─ cyclePlanarThreeSAT_inNP           Planar/VerifierMain.lean
└─ cyclePlanarThreeSAT_npHard         Planar/Reduction.lean             grid formula (comb_planar)
inNP_iff_nondeterministicPolyTime     NondeterministicEquiv.lean
├─ inNP_of_nondeterministicPolyTime   NTM/Verifier.lean                 simulate with choices from the certificate
└─ nondeterministicPolyTime_of_inNP   NTM/Guesser.lean                  clock, guess, check
```

* **Membership in NP.** `SATVerifier` defines the verifiers as functions: decode the formula,
  read an assignment from the certificate, evaluate. `StackSATMachine` and
  `StackThreeSATMachine` implement them as machines with polynomial running times, and
  `Membership` concludes `InNP`, with certificates no longer than the input.
* **The tableau.** For a verifier `M` with an explicit polynomial clock (`Clock`), `FiniteRows`
  encodes a configuration as a finite-control value and two tape windows around the head, with
  explicit local transition trees; `InitialWord` constrains the first row to `1^|x| 0 x`
  followed by a free certificate; `Tableau` unrolls the rows into a finite-domain constraint
  problem, `CSPSAT` translates it into CNF with one-hot variables, and `CookLevin` proves that
  the formula is satisfiable iff some certificate makes `M` accept within its clock.
* **Running time of the reduction.** The formula is not just shown to be small: it is produced
  by a machine whose steps are counted. `CookLevinEmitter` writes the formula as a program in a
  small first-order language of clause emission, bounded loops and arithmetic on unary numbers
  (`StackTableauEmitter`, `StackTableauProgram`). That language is compiled to programs over
  finitely many Boolean stacks (`StackMachine`, `StackProgram`), which are compiled to the
  single-tape model (`TapeToStacks`, `StackSimulation`, `StackCompile`), with the cost of every
  step accounted for. `StackTableau*Bounds` bound the work space and step counts of every loop.
* **SAT to 3-SAT.** `ChainThreeSAT` replaces a clause `l₁ ∨ … ∨ lₖ` by the clauses
  `zᵢ₊₁ ∨ lᵢ ∨ ¬zᵢ` with fresh variables `zᵢ`, plus unit clauses making the first `z` true and the
  last false; malformed inputs are mapped to the code of an unsatisfiable formula.
  `StackThreeSAT` implements this as a machine and bounds its running time.
* **Composition.** `Composition` proves that `PolyTime` functions compose, by simulating both
  machines on Boolean stacks and extracting the intermediate output; `Reductions` derives
  transitivity of `PolyRed`.
* **Exactly-3-SAT and (≤1,≤2)-SAT.** Instead of a new formula-to-formula machine, these
  reductions transform the Cook–Levin formula generator itself (`Restricted/Annotate`,
  `Transform`, `Copies`): every literal occurrence gets its own copy variable, a cycle of
  2-literal implications links the copies of each variable (Tovey's construction), long clauses
  are split by implication chains, and empty and unit clauses are rewritten locally. The result
  is an equisatisfiable (≤1,≤2) formula, and padding its 2-literal clauses gives an exactly-3
  formula. Since the compiled generator runs in polynomial time for every generator program,
  both reductions hold for every NP language. Membership runs a syntactic check, written as a
  counted stack program, before the existing 3-SAT verifier (`Restricted/CheckedVerifier`).
* **Binary SAT.** `Binary/Increment` converts unary indices to binary with a binary counter;
  the transducer in `Binary/Reduction*` parses a unary-coded formula and emits its binary code.
  The verifier (`Binary/Verifier*`) takes one certificate bit per literal occurrence, checks
  that every clause has a true literal, and compares every pair of occurrences, requiring equal
  bits for equal variables (equal binary values, ignoring leading zeros).
* **Planar 3-SAT.** The verifier (`Planar/Verifier*`, `EmbedCert`, `EmbedComplete`) reads,
  besides an assignment, parsing tables for the input and a local description of an embedding;
  local checks are proved to imply `PlanarGraph`. For hardness (`Planar/Grid*`, `Reduction`),
  the Cook–Levin formula of any NP language is laid out as a grid formula in the style of
  Lichtenstein: one column of crossover cells per clause along a spine, copies of each variable
  joined between columns by nested two-literal clauses. `Planar/Comb*` proves that every formula
  drawable as a comb (variables along the spine, clauses as legs) is planar with its variable
  cycle (`comb_planar`), by computing the faces of an explicit rotation system; the plain
  version replaces each cycle edge by a clause with a fresh variable, and `planar_subdivide`
  shows that subdividing edges keeps a graph planar. Two composed clause emitters make the
  reduction polynomial-time.
* **Nondeterminism.** `NTM/Core` simulates any `NMachine` on stacks, reading its choices from a
  register. For one direction the verifier runs this simulation with the certificate as the
  choices; no step counter is needed, since every path halts in time. For the other, a
  nondeterministic machine runs a compiled clock program that writes a unary budget, a
  two-state machine that guesses certificate bits in its place, and the compiled checker, which
  decodes the guess and simulates the verifier on the paired input (`NTM/Guess`, `Guesser`).

## Axioms and what is trusted

* `#print axioms` for every compared theorem gives `[propext, Classical.choice, Quot.sound]`. The default
  build also runs `Audit.lean`, which checks every declaration of the `Complexity` namespace
  and fails if any depends on another axiom.
* No Lean file other than `Challenge.lean` contains `sorry`, `admit`, `native_decide` or an
  `axiom` declaration (`scripts/check_submission.py` checks this). `Challenge.lean` contains
  exactly one deliberate `sorry` per compared theorem, as Palomar requires.
* What has to be trusted is Lean's kernel (Comparator replays the proof in several independent
  checkers) and the definitions of `Challenge.lean`. Comparator checks that the theorems of
  `Solution.lean` have exactly the types of those in `Challenge.lean`, including every definition
  they mention.

## Building and checking

You need [elan](https://github.com/leanprover/elan) (it installs the Lean version pinned in
`lean-toolchain`), Python 3, and, for `lake check` and `lake comparator`,
[bubblewrap](https://github.com/containers/bubblewrap). A full build takes under a minute.

```sh
lake build                     # library, axiom audit, Solution and examples
lake build Challenge           # the statement (one deliberate `sorry` per theorem)
scripts/palomar_dryrun.sh      # everything Palomar's mechanical verification runs
```

`scripts/palomar_dryrun.sh [--paranoid]` runs, in order, `scripts/check_submission.py` (the
repository rules Palomar checks before building: module headers, line limits, the Challenge's
size and imports, `comparator.json`, the licence, the metadata fields, and that `Challenge.lean`
matches its generator), `lake build`, `lake build Challenge`, `lake check`, and
`lake comparator --config comparator.json` in its sandbox with NanoDa; `--paranoid` adds every
other checker bundled with Lean. Logs go to `.lake/dryrun/`. The GitHub workflow
`.github/workflows/verify.yml` runs the same steps (with `--paranoid`) on every push.

`Challenge.lean` is generated from the library sources by `scripts/generate_challenge.py`,
which copies the selected definitions with their docstrings; `--check` fails if the file is out
of date. Comparator, not the generator, is what establishes that the statements agree.

## Repository layout

| Path | Contents |
| --- | --- |
| `Challenge.lean` | The statement: definitions and the eight theorems, with `sorry`. |
| `Solution.lean` | Imports the proofs of the eight theorems. |
| `comparator.json` | The Comparator configuration Palomar uses. |
| `formalization.yaml` | Palomar metadata: sources, authorship, AI use, review, limitations. |
| `Complexity/` | The library: 146 modules, about 41,000 lines (machine model, classes, SAT, compilers, tableau, reductions; `Restricted/`, `Binary/`, `NTM/` and `Planar/` for the further theorems; `Planarity.lean` and `PlanarSAT.lean` define planarity and planar 3-SAT). |
| `Complexity.lean` | Imports the whole library. |
| `Audit.lean` | Fails the build if a `Complexity` declaration uses a nonstandard axiom. |
| `Examples/` | `Sanity.lean` (tests of the definitions) and `Downstream.lean` (using the results). |
| `docs/FOUNDATION.md` | How to use the library to prove other problems NP-complete. |
| `docs/VERIFICATION.md` | Record of the verification runs. |
| `docs/SUBMISSION.md` | Checklist for a future Palomar submission. |
| `scripts/` | Challenge generator, submission preflight, Palomar rehearsal. |

## Using the results

Import `Complexity`. To prove a new language `L` NP-complete, give `InNP L` and a reduction
to `L` from any of the NP-complete languages here (SAT, 3-SAT, exactly-3-SAT, (≤1,≤2)-SAT,
binary SAT, both planar versions), and apply `NPComplete.of_reduction` (or `npComplete_of_sat_reduction`,
`npComplete_of_threeSAT_reduction`); `PolyRed.trans` composes reductions, and
`InNP.polyRed_sat` gives the Cook–Levin reduction from any NP language.
[docs/FOUNDATION.md](docs/FOUNDATION.md) explains the machine-programming API (stack machines
and their compiler) used to prove running times, and `Examples/Downstream.lean` has checked
examples.

**Downstream Palomar entries.** A Palomar Challenge may import only Lean core and the
allowlisted Mathlib, Tau Ceti or CSLib, and a registered entry does not become an allowed
import. A later entry claiming that some problem is NP-hard or NP-complete therefore copies the
definitions it needs from `Challenge.lean` verbatim (for `NPHard`/`NPComplete` statements,
everything up to `NPComplete`; the SAT definitions only if its statement mentions SAT), and its
Solution imports this repository, pinned at a commit, to use `threeSAT_np_hard`, `PolyRed.trans`
and the machine-programming API. Comparator then checks that the copied definitions are exactly
the library's. This has been tested with a Challenge importing all of Mathlib (v4.35.0-rc2):
Comparator accepts. That is why `powerBound` writes `Nat.pow` rather than `^`: with Mathlib
imported, `^` on `Nat` elaborates through Mathlib's monoid structure, a different term.
[docs/FOUNDATION.md](docs/FOUNDATION.md) describes the procedure.

## Other formalizations

The Cook–Levin theorem has been mechanized several times before, and this development claims
no priority. It is independent of all of them and uses none of their code.

* **Coq:** Lennard Gäher and Fabian Kunze, "Mechanising Complexity Theory: The Cook-Levin
  Theorem in Coq", ITP 2021 ([doi:10.4230/LIPIcs.ITP.2021.20](https://doi.org/10.4230/LIPIcs.ITP.2021.20),
  [code](https://github.com/uds-psl/coq-library-complexity)): SAT and 3-SAT NP-complete, with
  polynomial time defined in the call-by-value λ-calculus L.
* **Isabelle/HOL:** Frank J. Balbach, [The Cook-Levin theorem](https://isa-afp.org/entries/Cook_Levin.html),
  Archive of Formal Proofs, 2023: CNF-SAT NP-complete for multi-tape Turing machines, following
  Arora and Barak.
* **Lean 4:** [Complexitylib](https://github.com/SamuelSchlesinger/complexitylib) (Samuel
  Schlesinger and contributors), a Mathlib-based library of complexity theory over multi-tape
  Turing machines, proves SAT and 3SAT NP-complete among many other results; it is the closest
  prior work. [cook-levin-lean](https://github.com/DominicBreuker/cook-levin-lean) (Dominic
  Breuker, Lean 4 and Mathlib) proves SAT NP-complete for single-tape machines.
  [descriptive-complexity](https://github.com/PierreSenellart/descriptive-complexity) (Pierre
  Senellart and Anton Gnatenko, [arXiv:2609.18261](https://arxiv.org/abs/2609.18261)) proves
  SAT, 3SAT and Karp's 21 problems complete for NP defined logically, without machines.
* **ACL2:** Ruben Gamboa and John Cowles, "A Mechanical Proof of the Cook-Levin Theorem",
  TPHOLs 2004 ([doi:10.1007/978-3-540-30142-4_8](https://doi.org/10.1007/978-3-540-30142-4_8)):
  the translation of machine computations to SAT, without complexity classes.

For the further theorems: the Coq and Lean developments above also prove 3-SAT (with at most or
exactly three literals per clause) NP-complete, and the descriptive-complexity library relates
its logically defined NP to acceptance by nondeterministic machines. A search found no earlier
formalization of (≤1,≤2)-SAT, of the binary-index variant, or of planar 3-SAT.

What distinguishes this one: the statement needs nothing beyond Lean core, so it can be audited
in one 464-line file; it uses a single-tape model and proves every running time, including that
of the Cook–Levin reduction itself, by counting the steps of an actual machine; and it is
prepared for checking by Palomar's Comparator pipeline.

## Licence

Apache License 2.0 (`LICENSE`). Lean, which is not redistributed here, is also under the
Apache License 2.0.

## History of this repository

* The first commit holds the Lean project exactly as GPT-6 Astra delivered it: the Lean
  sources, the Lake configuration, `comparator.json` and the Challenge generator. The delivered
  archive also contained a handover note, metadata templates, and validation records made in a
  restricted environment: there the `lean` executable could not start, so the sources were
  elaborated through the Lean frontend embedded in a small C host, and exported proofs were
  replayed with Comparator's functions and the leanchecker, NanoDa and con-ron checkers. Those
  files are not part of this repository; the native `lake comparator` pipeline had not run.
* The second commit, by Claude Opus 5.5, ran the ordinary Lake and Comparator pipeline (it
  passed on the delivered sources), made the changes listed in the [AI disclosure](#ai-disclosure),
  and replaced the restricted-environment tooling with the ordinary build and the scripts
  above. Two changes reach the statement itself, both checked by
  Comparator: `SAT.SAT` and `SAT.ThreeSAT` are now defined as images of `SAT.encode` (before,
  through the parser `SAT.decode`; `SAT.SAT_iff_decode` proves the definitions equivalent), and
  the Challenge no longer contains the unused definitions `InP`, `Tape.size` and
  `Instruction.mapState`, nor the parser.
* Later commits, by Claude Opus 5.5 and its subagents: `powerBound` written with `Nat.pow` so
  that the definitions elaborate identically when Mathlib is imported (checked with a mock
  downstream project); the definitions of the variants of SAT, of planar 3-SAT and of
  nondeterministic machines; the proofs of the six further compared theorems, each merged as
  one commit after review; and a compression of the Challenge's layout and docstrings.
