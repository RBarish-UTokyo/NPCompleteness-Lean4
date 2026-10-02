module

public import Complexity.SAT

/-!
# Restricted and binary-coded satisfiability

Three further satisfiability languages, all over CNF formulas:

* `ExactThreeSAT`: every clause has exactly three literals, on three distinct variables;
* `LeOneLeTwoSAT`, (≤1,≤2)-SAT: every clause has two or three literals, and every variable
  occurs at most once positively and at most twice negatively;
* `BinarySAT`: arbitrary CNF formulas, coded with binary variable indices.

The definitions avoid notation whose meaning depends on the instances in scope (they use
`Nat.beq` rather than `==` or `decide`), so that they elaborate to the same terms when Mathlib
is imported.
-/

@[expose] public section

namespace Complexity.SAT

/-- Every clause of `f` has exactly three literals, on three distinct variables. -/
def IsExactThreeCNF (f : CNF) : Prop :=
  ∀ c ∈ f, c.length = 3 ∧ (c.map Literal.var).Nodup

/-- Exactly-3-SAT: the words `encode f` with `f` satisfiable and `IsExactThreeCNF f`. -/
def ExactThreeSAT (input : Word) : Prop :=
  ∃ f, encode f = input ∧ IsExactThreeCNF f ∧ Satisfiable f

/-- The (≤1,≤2) restriction: every clause of `f` has two or three literals, and every variable
occurs in `f` at most once positively and at most twice negatively. -/
def IsLeOneLeTwoCNF (f : CNF) : Prop :=
  (∀ c ∈ f, 2 ≤ c.length ∧ c.length ≤ 3) ∧
  ∀ v : Nat, (f.flatten.filter fun l => l.positive && Nat.beq l.var v).length ≤ 1 ∧
    (f.flatten.filter fun l => !l.positive && Nat.beq l.var v).length ≤ 2

/-- (≤1,≤2)-SAT: the words `encode f` with `f` satisfiable and satisfying `IsLeOneLeTwoCNF`. -/
def LeOneLeTwoSAT (input : Word) : Prop :=
  ∃ f, encode f = input ∧ IsLeOneLeTwoCNF f ∧ Satisfiable f

/-- The number with binary digits `bits`, least significant digit first. -/
def binaryValue : List Bool → Nat
  | [] => 0
  | b :: bits => b.toNat + 2 * binaryValue bits

/-- A literal naming its variable by binary digits, least significant first (zeros may trail). -/
structure BinaryLiteral where
  bits : List Bool
  positive : Bool

/-- The literal named by a `BinaryLiteral`. -/
def BinaryLiteral.toLiteral (l : BinaryLiteral) : Literal :=
  ⟨binaryValue l.bits, l.positive⟩

/-- The code of a binary literal: its sign bit, then its digits (their count in unary first). -/
def encodeBinaryLiteral (l : BinaryLiteral) : Word :=
  l.positive :: writeList (fun b => [b]) l.bits

/-- The code of a formula with binary indices; clause and literal counts stay in unary. -/
def encodeBinary (f : List (List BinaryLiteral)) : Word :=
  writeList (writeList encodeBinaryLiteral) f

/-- Binary SAT: the words `encodeBinary f` such that the formula `f` names is satisfiable. -/
def BinarySAT (input : Word) : Prop :=
  ∃ f, encodeBinary f = input ∧ Satisfiable (f.map (List.map BinaryLiteral.toLiteral))

end Complexity.SAT
