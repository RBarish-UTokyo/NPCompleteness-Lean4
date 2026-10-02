# Using the complexity foundation

Import `Complexity` for the complete result and reduction API. For a published
downstream project, pin the exact source commit and preserve the pinned Lean
toolchain. The present project has no external package dependencies.

## Public statements

All names in this section live in `Complexity` unless qualified otherwise.

| Declaration | Type or purpose |
| --- | --- |
| `Word` | `List Bool` |
| `Language` | `Word → Prop` |
| `PolyTime f` | A fixed total polynomial-time tape transducer computes `f`. |
| `InNP L` | Polynomial-length certificates characterize membership through a total polynomial-time tape verifier. |
| `PolyRed A B` | There is a total `PolyTime` function `f` with `A x ↔ B (f x)` for every word `x`. |
| `NPHard L` | Every language satisfying `InNP` reduces to `L`. |
| `NPComplete L` | `InNP L ∧ NPHard L`. |
| `sat_np_complete` | `NPComplete SAT.SAT` |
| `threeSAT_np_complete` | `NPComplete SAT.ThreeSAT` |
| `InNP.polyRed_sat` | Construct the Cook–Levin reduction from an NP-membership proof. |
| `InNP.polyRed_threeSAT` | Construct the corresponding reduction to 3-SAT. |

SAT means serialized CNF satisfiability. 3-SAT means serialized CNF
satisfiability with at most three literals in each clause. See the README and
`SAT.lean` for the complete encoding conventions. A downstream reduction must
handle every binary input, including words that fail to decode.

## Proving a new language NP-complete

After defining a language `L`, prove its membership in `InNP` and a reduction
from either established source problem:

```lean
module
import Complexity

open Complexity

example {L : Language} (hL : InNP L) (hred : PolyRed SAT.SAT L) :
    NPComplete L :=
  npComplete_of_sat_reduction hL hred

example {L : Language} (hL : InNP L) (hred : PolyRed SAT.ThreeSAT L) :
    NPComplete L :=
  npComplete_of_threeSAT_reduction hL hred

example {L : Language} (hred : PolyRed SAT.SAT L) : NPHard L :=
  sat_np_hard.of_reduction hred
```

The direction matters: the known hard problem is the source of the reduction.
A reduction *to* SAT proves no hardness claim about its source.

Constructing `PolyRed` separates the executable algorithm from its mathematical
correctness:

```lean
module
import Complexity

open Complexity

example {A B : Language} (f : Word → Word) (hf : PolyTime f)
    (hcorrect : ∀ x, A x ↔ B (f x)) : PolyRed A B :=
  ⟨f, hf, hcorrect⟩

example {A B C : Language} (hAB : PolyRed A B) (hBC : PolyRed B C) :
    PolyRed A C :=
  hAB.trans hBC

example {A B : Language} (hA : NPComplete A)
    (hAB : PolyRed A B) (hB : InNP B) : NPComplete B :=
  hA.transfer hAB hB
```

`PolyRed.trans` uses `polyTime_comp`, which simulates the actual transducers.
Output length bounds and machine composition are proved in the foundation.
Polynomial output size alone is insufficient to supply `hf : PolyTime f`.
The file [Examples/Downstream.lean](../Examples/Downstream.lean) contains checked
examples using the public aggregate import.

## Implementing algorithms

The lowest-level route supplies a `Machine`, proves its `runInput` behavior,
and bounds the number of local instructions uniformly over all inputs.
Use `PolynomialBound` to compose arithmetic upper bounds. Its bounds dominate
functions by a constant times a fixed power of `input.length + 1`.

For more convenient programming, use finite Boolean-stack registers. A
`StackMachine.Machine` has finitely many states and a fixed finite number of
registers. Instructions push one bit, pop or inspect one bit with finite
branching, jump, or halt. `StackProgram` provides finite-control composition,
loops, and a compiler with counted execution theorems. These are intermediate
models with proved implementations on the original tape machine.

The principal compiler entry points are:

- `StackCompile.simulate`: transfer a bounded stack computation, preserving
  its decision and output.
- `StackCompile.polyTime_of_stack`: turn a uniform polynomial stack-time
  bound for a transducer into `PolyTime`.
- `StackCompile.polynomialTimeMachine_of_stack`: transfer a total decision
  algorithm's polynomial bound.
- `StackCompile.accepts_iff`: relate acceptance of the compiled machine to
  the original stack machine when the stack computation is total.

These theorems account for tape layout initialization, register operations,
finite-control execution, and final output positioning. A stack operation
never evaluates an arbitrary `Word → Word` function at unit cost.

For CNF generation, `StackTableauEmitter.ClauseProgram` is a finite syntax of
literal emission, sequencing, descending bounded loops, numeric comparisons,
and input-bit tests. Numeric expressions use constants, variables, addition,
multiplication, saturating subtraction, and predecessor. The theorem
`StackTableauEmitter.polyTime_emitter` proves polynomial-time serialization
for every fixed program whose sole initial numeric parameter is input length.
The compiler proves the emitted bytes agree with `ClauseProgram.emit` and
preserves a polynomial workspace capacity through nested loops.

## Semantic boundaries to retain

`SAT.SAT` and `SAT.ThreeSAT` are predicates on encoded words, not on the
internal `CNF` datatype: a word belongs to them only if it is `SAT.encode f`
for a suitable formula `f`. The parser `SAT.decode` rejects malformed words and
trailing data, and `SAT.SAT_iff_decode`, `SAT.ThreeSAT_iff_decode` and
`SAT.decode_eq_some_iff` connect it with the definitions. Use `SAT.encode`, these
theorems, and explicit malformed branches when defining a total reduction.

`SAT.Satisfiable` permits a mathematical assignment `Nat → Bool`. The verifier
bridge proves that a finite certificate suffices; it does not treat an
infinite assignment as a machine input. Variable names and list lengths are
encoded in unary. An algorithm analyzed for a different representation needs
a proved encoding conversion before these runtime theorems apply.

The NP definition is a verifier characterization for the specified finite
single-tape model. This project does not additionally prove equivalence to a
separately defined nondeterministic-machine class, nor an invariance theorem
covering every conventional machine model. The final hardness theorem directly
quantifies over the explicit `InNP` definition.

## Reusing the result in a Palomar submission

Ordinary Lean reuse and Challenge admissibility are separate matters. A pinned
Solution may import this foundation. A downstream Challenge must obey the
current transitive statement-import policy; prior registration alone grants
no dependency permission. Inline the necessary concrete definitions, and run
Comparator against the proved Solution. Copying the theorem names or making
the Challenge's definitions opaque does not establish matching statements.

The supplied Challenge generator targets this project's declarations. It is
not a general generator for downstream languages. Reuse its extraction approach
only after reviewing the resulting mathematical statement and checking every
dependency that occurs in the theorem types. See the
[current submission rules](https://palomar-registry.org/how-to-submit).

Keep proof checking, independent replay, statement comparison, and human review
distinct in downstream provenance. Record the exact checked commit and actual
validation results. Do not inherit a review or registration claim from this
repository.
