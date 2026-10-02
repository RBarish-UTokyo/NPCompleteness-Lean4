module

public import Complexity.StackTableauEmitterCorrect
public import Complexity.StackTableauLiteralBounds
public import Complexity.StackTableauFits

@[expose] public section

namespace Complexity.StackTableauEmitterCompile

open StackTableauEmitter
open StackTableauProgram (Exec)
open StackMachine (Registers)

/-- A syntax-directed upper bound on actual elementary-stack steps. The same
capacity is used at every loop iteration; output and clause count are streamed. -/
def bodyCost {n : Nat} : ClauseProgram n → Nat → Nat
  | .clause literals, C => clauseCost literals C
  | .seq first second, C => bodyCost first C + bodyCost second C
  | .forDown bound body, C => numCost bound C + (C + 3) + C * (bodyCost body C + 3) + 2
  | .ifLe left right yes no, C =>
      numCost left C + numCost right C + (3 * C + 2) +
        (bodyCost yes C + bodyCost no C) + 1
  | .ifInput index empty zero one, C =>
      numCost index C + (6 * C + 6) + (3 * C + 2) +
        (bodyCost empty C + bodyCost zero C + bodyCost one C) + 1

/-- Quantitative execution with one immutable global workspace capacity.
Exact serialized output follows independently from `compileBody_correct`
and deterministic actual machine execution. -/
def BodyBounded {n : Nat} (program : ClauseProgram n) : Prop :=
  ∀ {k : Nat} (envRegisters : Fin n → Fin (k + 1)) (env : Env n)
    (base : Nat) (input : SAT.Word) (r : Registers k),
    5 ≤ base →
    (∀ i, 5 ≤ (envRegisters i).val ∧ (envRegisters i).val < base) →
    base + programSpace program ≤ k + 1 →
    (∀ i, r (envRegisters i) = List.replicate (env i) true) →
    r (register k 1) = input → r (register k 3) = [] →
    ∀ C, program.Fits input env C → WorkBound r C →
    ∃ time out, Exec (compileBody envRegisters base program) r time (true, out) ∧
      BodyFrame base r out ∧ time ≤ bodyCost program C ∧ WorkBound out C

theorem polynomialBound_bodyCost {n : Nat} (program : ClauseProgram n) : PolynomialBound (bodyCost program) := by
  induction program with
  | clause literals => exact polynomialBound_clauseCost literals PolynomialBound.identity
  | seq first second ihf ihs => exact ihf.add ihs
  | forDown bound body ih =>
      exact (((polynomialBound_numCost bound PolynomialBound.identity).add
        (PolynomialBound.identity.add (PolynomialBound.constant 3))).add
        (PolynomialBound.identity.mul (ih.add (PolynomialBound.constant 3)))).add
        (PolynomialBound.constant 2)
  | ifLe left right yes no ihy ihn =>
      exact (((((polynomialBound_numCost left PolynomialBound.identity).add (polynomialBound_numCost right PolynomialBound.identity)).add
        (((PolynomialBound.constant 3).mul PolynomialBound.identity).add (PolynomialBound.constant 2))).add
        (ihy.add ihn))).add (PolynomialBound.constant 1)
  | ifInput index empty zero one ihe ihz iho =>
      exact (((((polynomialBound_numCost index PolynomialBound.identity).add
        (((PolynomialBound.constant 6).mul PolynomialBound.identity).add (PolynomialBound.constant 6))).add
        (((PolynomialBound.constant 3).mul PolynomialBound.identity).add (PolynomialBound.constant 2))).add
        ((ihe.add ihz).add iho))).add (PolynomialBound.constant 1)

end Complexity.StackTableauEmitterCompile
