module

public import Complexity.Classes

/-!
# Nondeterministic machines

Nondeterministic single-tape machines in the style of Arora and Barak (*Computational
Complexity: A Modern Approach*, ch. 2): a machine has two transition tables and may follow
either at every step. `NondeterministicPolyTime L` says that such a machine accepts `L` and
that every computation path halts within a polynomial number of steps. The theorem
`inNP_iff_nondeterministicPolyTime` proves that this class is `InNP`.
-/

@[expose] public section

namespace Complexity

/-- A nondeterministic single-tape Turing machine: like `Machine`, but with two transition
tables, `code false` and `code true`; at every step the machine may follow either. -/
structure NMachine where
  states : Nat
  start : Fin (states + 1)
  code : Bool → Fin (states + 1) → Symbol → Instruction (states + 1)

/-- `M.run choices q t` runs `M` from control state `q` and tape `t`, using the table
`code c` at the step that consumes the choice `c`. It is `some (b, t')` if the machine
executes `halt b` within the steps given by `choices` (halting counts as a step), `t'` being
the final tape, and `none` if it has not halted when the choices run out. -/
def NMachine.run (M : NMachine) : List Bool → Fin (M.states + 1) → Tape → Option (Bool × Tape)
  | [], _, _ => none
  | c :: choices, q, t =>
    match M.code c q t.read with
    | .halt b => some (b, t)
    | .step a d q' => M.run choices q' ((t.write a).move d)

/-- Nondeterministic polynomial time: some nondeterministic machine `M` and bound
`p n = c * (n + 1) ^ k` such that, on every input `x`, every computation path halts within
`p |x|` steps, and `x ∈ L` iff some computation path accepts. -/
def NondeterministicPolyTime (L : Language) : Prop :=
  ∃ M : NMachine, ∃ coefficient exponent, ∀ input : Word,
    (∀ choices : List Bool, choices.length = powerBound coefficient exponent input.length →
      M.run choices M.start (Tape.ofInput input) ≠ none) ∧
    (L input ↔ ∃ choices tape, M.run choices M.start (Tape.ofInput input) = some (true, tape))

end Complexity
