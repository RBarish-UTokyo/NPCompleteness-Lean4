module

public import Complexity.SAT
import Lean.Elab.Tactic.Omega

/-!
Finite Boolean constraints expressed directly as CNF.  The cardinality
constraints count list positions, so their semantics remains precise even if
variable identifiers occur more than once.  These constructions and size bounds
are semantic infrastructure, not machine running-time claims.
-/

@[expose] public section

namespace Complexity.Constraints

open Complexity.SAT

def negateLiteral (l : Literal) : Literal := ⟨l.var, !l.positive⟩

@[simp] theorem evalLiteral_negate (a : Assignment) (l : Literal) :
    evalLiteral a (negateLiteral l) = !(evalLiteral a l) := by
  cases l with
  | mk v sign => cases sign <;> simp [negateLiteral, evalLiteral]

@[simp] theorem negateLiteral_negate (l : Literal) :
    negateLiteral (negateLiteral l) = l := by
  cases l with
  | mk v sign => cases sign <;> rfl

def evalConjunction (a : Assignment) (premises : List Literal) : Bool :=
  premises.all (evalLiteral a)

/-- The implication from all premises to at least one conclusion. Empty
premises mean truth; empty conclusions mean falsehood. -/
def implicationClause (premises conclusions : List Literal) : Clause :=
  premises.map negateLiteral ++ conclusions

theorem eval_implicationClause (a : Assignment) (premises conclusions : List Literal) :
    evalClause a (implicationClause premises conclusions) =
      (!(evalConjunction a premises) || evalClause a conclusions) := by
  induction premises with
  | nil => simp [implicationClause, evalConjunction]
  | cons l rest ih =>
      simp only [implicationClause, List.map_cons, List.cons_append, evalClause_cons,
        evalLiteral_negate] at ih ⊢
      rw [ih]
      simp only [evalConjunction, List.all_cons]
      cases evalLiteral a l <;> cases rest.all (evalLiteral a) <;>
        cases evalClause a conclusions <;> rfl

theorem implicationClause_correct (a : Assignment) (premises conclusions : List Literal) :
    evalClause a (implicationClause premises conclusions) = true ↔
      (evalConjunction a premises = true → evalClause a conclusions = true) := by
  rw [eval_implicationClause]
  cases evalConjunction a premises <;> cases evalClause a conclusions <;> simp

theorem implicationClause_length (premises conclusions : List Literal) :
    (implicationClause premises conclusions).length = premises.length + conclusions.length := by
  simp [implicationClause]

/-- The number of true variable occurrences, counting repeated positions. -/
def countTrue (a : Assignment) : List Nat → Nat
  | [] => 0
  | v :: rest => (if a v then 1 else 0) + countTrue a rest

def positiveClause : List Nat → Clause
  | [] => []
  | v :: rest => ⟨v, true⟩ :: positiveClause rest

@[simp] theorem positiveClause_length (variables : List Nat) :
    (positiveClause variables).length = variables.length := by
  induction variables with
  | nil => rfl
  | cons v rest ih => simp [positiveClause, ih]

theorem positiveClause_correct (a : Assignment) (variables : List Nat) :
    evalClause a (positiveClause variables) = true ↔ 0 < countTrue a variables := by
  induction variables with
  | nil => simp [positiveClause, countTrue]
  | cons v rest ih =>
      cases h : a v <;> simp [positiveClause, countTrue, h, ih] <;> omega

/-- Exclude selecting `v` together with any position in `variables`. -/
def excludeWith (v : Nat) : List Nat → CNF
  | [] => []
  | w :: rest => [⟨v, false⟩, ⟨w, false⟩] :: excludeWith v rest

theorem excludeWith_correct (a : Assignment) (v : Nat) (variables : List Nat) :
    evalCNF a (excludeWith v variables) = true ↔
      (a v = true → countTrue a variables = 0) := by
  induction variables with
  | nil => simp [excludeWith, countTrue]
  | cons w rest ih =>
      cases hv : a v <;> cases hw : a w <;>
        simp [excludeWith, countTrue, hv, hw, ih]

@[simp] theorem excludeWith_length (v : Nat) (variables : List Nat) :
    (excludeWith v variables).length = variables.length := by
  induction variables with
  | nil => rfl
  | cons w rest ih => simp [excludeWith, ih]

theorem excludeWith_binary (v : Nat) (variables : List Nat) :
    ∀ c ∈ excludeWith v variables, c.length = 2 := by
  induction variables with
  | nil => simp [excludeWith]
  | cons w rest ih =>
      intro c hc
      simp only [excludeWith, List.mem_cons] at hc
      rcases hc with rfl | hc
      · rfl
      · exact ih c hc

/-- Pairwise exclusions for distinct list positions, including repeated IDs. -/
def atMostOne : List Nat → CNF
  | [] => []
  | v :: rest => excludeWith v rest ++ atMostOne rest

theorem atMostOne_correct (a : Assignment) (variables : List Nat) :
    evalCNF a (atMostOne variables) = true ↔ countTrue a variables ≤ 1 := by
  induction variables with
  | nil => simp [atMostOne, countTrue]
  | cons v rest ih =>
      simp only [atMostOne, evalCNF_append, Bool.and_eq_true, excludeWith_correct, ih]
      cases hv : a v <;> simp [countTrue, hv] <;> omega

theorem atMostOne_binary (variables : List Nat) :
    ∀ c ∈ atMostOne variables, c.length = 2 := by
  induction variables with
  | nil => simp [atMostOne]
  | cons v rest ih =>
      intro c hc
      simp only [atMostOne, List.mem_append] at hc
      rcases hc with hc | hc
      · exact excludeWith_binary v rest c hc
      · exact ih c hc

theorem atMostOne_length_le (variables : List Nat) :
    (atMostOne variables).length ≤ variables.length * variables.length := by
  induction variables with
  | nil => simp [atMostOne]
  | cons v rest ih =>
      simp only [atMostOne, List.length_append, excludeWith_length, List.length_cons]
      simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one]
      omega

/-- At least one selected position together with all pairwise exclusions. -/
def exactlyOne (variables : List Nat) : CNF :=
  positiveClause variables :: atMostOne variables

theorem exactlyOne_correct (a : Assignment) (variables : List Nat) :
    evalCNF a (exactlyOne variables) = true ↔ countTrue a variables = 1 := by
  simp only [exactlyOne, evalCNF_cons, Bool.and_eq_true,
    positiveClause_correct, atMostOne_correct]
  omega

theorem exactlyOne_length_le (variables : List Nat) :
    (exactlyOne variables).length ≤ variables.length * variables.length + 1 := by
  have h := atMostOne_length_le variables
  simp only [exactlyOne, List.length_cons]
  omega

theorem exactlyOne_clause_length (variables : List Nat) :
    ∀ c ∈ exactlyOne variables, c.length = variables.length ∨ c.length = 2 := by
  intro c hc
  simp only [exactlyOne, List.mem_cons] at hc
  rcases hc with rfl | hc
  · exact Or.inl (positiveClause_length variables)
  · exact Or.inr (atMostOne_binary variables c hc)

/-- Count literal occurrences, independently of the chosen variable encoding. -/
def literalCount : CNF → Nat
  | [] => 0
  | c :: rest => c.length + literalCount rest

theorem literalCount_append (f g : CNF) :
    literalCount (f ++ g) = literalCount f + literalCount g := by
  induction f with
  | nil => simp [literalCount]
  | cons c rest ih => simp [literalCount, ih, Nat.add_assoc]

theorem literalCount_of_binary (f : CNF) (hf : ∀ c ∈ f, c.length = 2) :
    literalCount f = 2 * f.length := by
  induction f with
  | nil => simp [literalCount]
  | cons c rest ih =>
      have hc := hf c (by simp)
      have hr : ∀ d ∈ rest, d.length = 2 := by
        intro d hd
        exact hf d (by simp [hd])
      simp [literalCount, hc, ih hr, Nat.mul_add, Nat.add_comm]

theorem exactlyOne_literalCount_le (variables : List Nat) :
    literalCount (exactlyOne variables) ≤
      variables.length + 2 * (variables.length * variables.length) := by
  have hsize := atMostOne_length_le variables
  have hcount := literalCount_of_binary (atMostOne variables) (atMostOne_binary variables)
  simp only [exactlyOne, literalCount, positiveClause_length]
  omega

end Complexity.Constraints
