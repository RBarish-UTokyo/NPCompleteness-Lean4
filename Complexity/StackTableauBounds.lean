module

public import Complexity.StackTableauEmitter
public import Complexity.PolynomialBound
public import Complexity.SATBounds

/-!
Syntactic polynomial envelopes for immutable arithmetic and lexically bounded
clause generation. These bounds are independent of any compiler runtime claim.
-/

@[expose] public section

namespace Complexity.StackTableauEmitter

def NumExpr.upper {n : Nat} : NumExpr n → Nat → Nat
  | .var _, bound => bound
  | .const value, _ => value
  | .add left right, bound => left.upper bound + right.upper bound
  | .mul left right, bound => left.upper bound * right.upper bound
  | .sub left _, bound => left.upper bound
  | .pred value, bound => value.upper bound

theorem NumExpr.eval_le_upper {n : Nat} (expr : NumExpr n) (env : Env n) (bound : Nat)
    (henv : ∀ i, env i ≤ bound) : expr.eval env ≤ expr.upper bound := by
  induction expr with
  | var i => exact henv i
  | const value => exact Nat.le_refl _
  | add left right ihl ihr => exact Nat.add_le_add ihl ihr
  | mul left right ihl ihr => exact Nat.mul_le_mul ihl ihr
  | sub left right ihl _ => exact Nat.le_trans (Nat.sub_le _ _) ihl
  | pred value ih => exact Nat.le_trans (Nat.sub_le _ _) ih

theorem NumExpr.upper_mono {n : Nat} (expr : NumExpr n) {a b : Nat} (h : a ≤ b) :
    expr.upper a ≤ expr.upper b := by
  induction expr with
  | var _ => exact h
  | const _ => exact Nat.le_refl _
  | add _ _ ihl ihr => exact Nat.add_le_add ihl ihr
  | mul _ _ ihl ihr => exact Nat.mul_le_mul ihl ihr
  | sub _ _ ihl _ => exact ihl
  | pred _ ih => exact ih

theorem NumExpr.upper_polynomial {n : Nat} (expr : NumExpr n) :
    PolynomialBound expr.upper := by
  induction expr with
  | var _ => exact PolynomialBound.identity
  | const value => exact PolynomialBound.constant value
  | add _ _ ihl ihr => exact ihl.add ihr
  | mul _ _ ihl ihr => exact ihl.mul ihr
  | sub _ _ ihl _ => exact ihl
  | pred _ ih => exact ih

/-- A bound on every arithmetic subexpression, including discarded operands
of subtraction, sufficient for evaluating an expression with unary counters. -/
def NumExpr.magnitude {n : Nat} : NumExpr n → Nat → Nat
  | .var _, bound => bound
  | .const value, _ => value
  | .add left right, bound => left.magnitude bound + right.magnitude bound
  | .mul left right, bound =>
      left.magnitude bound + right.magnitude bound + left.magnitude bound * right.magnitude bound
  | .sub left right, bound => left.magnitude bound + right.magnitude bound
  | .pred value, bound => value.magnitude bound

theorem NumExpr.upper_le_magnitude {n : Nat} (expr : NumExpr n) (bound : Nat) :
    expr.upper bound ≤ expr.magnitude bound := by
  induction expr with
  | var _ => exact Nat.le_refl _
  | const _ => exact Nat.le_refl _
  | add _ _ ihl ihr => exact Nat.add_le_add ihl ihr
  | mul left right ihl ihr =>
    exact Nat.le_trans (Nat.mul_le_mul ihl ihr) (Nat.le_add_left _ _)
  | sub left right ihl _ => exact Nat.le_trans ihl (Nat.le_add_right _ _)
  | pred _ ih => exact ih

theorem NumExpr.magnitude_polynomial {n : Nat} (expr : NumExpr n) :
    PolynomialBound expr.magnitude := by
  induction expr with
  | var _ => exact PolynomialBound.identity
  | const value => exact PolynomialBound.constant value
  | add _ _ ihl ihr => exact ihl.add ihr
  | mul _ _ ihl ihr => exact (ihl.add ihr).add (ihl.mul ihr)
  | sub _ _ ihl ihr => exact ihl.add ihr
  | pred _ ih => exact ih

def literalBitsBound {n : Nat} : List (LiteralExpr n) → Nat → Nat
  | [], _ => 1
  | literal :: rest, bound => literal.index.upper bound + 3 + literalBitsBound rest bound

theorem literalBitsBound_polynomial {n : Nat} (literals : List (LiteralExpr n)) :
    PolynomialBound (literalBitsBound literals) := by
  induction literals with
  | nil => exact PolynomialBound.constant 1
  | cons literal rest ih =>
    exact (literal.index.upper_polynomial.add (PolynomialBound.constant 3)).add ih

theorem encodeClause_length_le_literalBitsBound {n : Nat} (literals : List (LiteralExpr n))
    (env : Env n) (bound : Nat) (henv : ∀ i, env i ≤ bound) :
    (SAT.encodeClause (literals.map (fun l => l.eval env))).length ≤
      literalBitsBound literals bound := by
  induction literals with
  | nil => exact Nat.le_refl _
  | cons literal rest ih =>
    rw [List.map_cons, SATBounds.encodeClause_cons_length]
    exact Nat.add_le_add
      (Nat.add_le_add_right (literal.index.eval_le_upper env bound henv) 3) ih

/-- Combined clause-header and clause-body serialization cost, omitting the
one final formula terminator. It is additive over clause concatenation. -/
def formulaWeight : SAT.CNF → Nat
  | [] => 0
  | clause :: rest => (SAT.encodeClause clause).length + 1 + formulaWeight rest

@[simp] theorem formulaWeight_append (first second : SAT.CNF) :
    formulaWeight (first ++ second) = formulaWeight first + formulaWeight second := by
  induction first with
  | nil => simp [formulaWeight]
  | cons clause rest ih => simp [formulaWeight, ih, Nat.add_assoc]

@[simp] theorem encode_length_eq_formulaWeight (formula : SAT.CNF) :
    (SAT.encode formula).length = formulaWeight formula + 1 := by
  induction formula with
  | nil => rfl
  | cons clause rest ih => simp [SATBounds.encode_cons_length, formulaWeight, ih, Nat.add_assoc]


theorem length_le_formulaWeight (formula : SAT.CNF) : formula.length ≤ formulaWeight formula := by
  induction formula with
  | nil => exact Nat.le_refl _
  | cons clause rest ih =>
    simp only [List.length_cons, formulaWeight]
    omega

def ClauseProgram.outputBound {n : Nat} : ClauseProgram n → Nat → Nat
  | .clause literals, bound => literalBitsBound literals bound + 1
  | .seq first second, bound => first.outputBound bound + second.outputBound bound
  | .forDown expr body, bound => expr.upper bound * body.outputBound (expr.upper bound + bound)
  | .ifLe _ _ yes no, bound => yes.outputBound bound + no.outputBound bound
  | .ifInput _ empty zero one, bound =>
      empty.outputBound bound + zero.outputBound bound + one.outputBound bound

theorem weight_flatMap_le {α : Type} (xs : List α) (body : α → SAT.CNF) (bound : Nat)
    (h : ∀ x ∈ xs, formulaWeight (body x) ≤ bound) :
    formulaWeight (xs.flatMap body) ≤ xs.length * bound := by
  induction xs with
  | nil => simp [formulaWeight]
  | cons x xs ih =>
    have hx := h x List.mem_cons_self
    have ht := ih (fun y hy => h y (List.mem_cons_of_mem x hy))
    simpa [Nat.add_mul, Nat.add_assoc, Nat.add_comm] using Nat.add_le_add hx ht

theorem ClauseProgram.outputBound_polynomial {n : Nat} (program : ClauseProgram n) :
    PolynomialBound program.outputBound := by
  induction program with
  | clause literals => exact (literalBitsBound_polynomial literals).add (PolynomialBound.constant 1)
  | seq _ _ ihfirst ihsecond => exact ihfirst.add ihsecond
  | forDown expr body ih =>
    exact expr.upper_polynomial.mul (ih.comp (expr.upper_polynomial.add PolynomialBound.identity))
  | ifLe _ _ _ _ ihyes ihno => exact ihyes.add ihno
  | ifInput _ _ _ _ ihempty ihzero ihone => exact (ihempty.add ihzero).add ihone

theorem ClauseProgram.weight_emit_le {n : Nat} (program : ClauseProgram n) (input : SAT.Word)
    (env : Env n) (bound : Nat) (henv : ∀ i, env i ≤ bound) :
    formulaWeight (program.emit input env) ≤ program.outputBound bound := by
  induction program generalizing bound with
  | clause literals =>
    exact Nat.add_le_add_right (encodeClause_length_le_literalBitsBound literals env bound henv) 1
  | seq first second ihfirst ihsecond =>
    simpa [ClauseProgram.emit, ClauseProgram.outputBound] using Nat.add_le_add (ihfirst env bound henv) (ihsecond env bound henv)
  | forDown expr body ih =>
    have hx := expr.eval_le_upper env bound henv
    have hall : ∀ i ∈ (List.range (expr.eval env)).reverse,
        formulaWeight (body.emit input (extend i env)) ≤
          body.outputBound (expr.upper bound + bound) := by
      intro i hi
      have hi' : i < expr.eval env := by simpa using hi
      apply ih (extend i env) (expr.upper bound + bound)
      intro j
      induction j using Fin.cases with
      | zero => exact Nat.le_trans (Nat.le_of_lt hi') (Nat.le_trans hx (Nat.le_add_right _ _))
      | succ j => exact Nat.le_trans (henv j) (Nat.le_add_left _ _)
    have hflat := weight_flatMap_le _ _ _ hall
    simp only [List.length_reverse, List.length_range] at hflat
    exact Nat.le_trans hflat (Nat.mul_le_mul_right _ hx)
  | ifLe left right yes no ihyes ihno =>
    simp only [ClauseProgram.emit, ClauseProgram.outputBound]
    split
    · exact Nat.le_trans (ihyes env bound henv) (Nat.le_add_right _ _)
    · exact Nat.le_trans (ihno env bound henv) (Nat.le_add_left _ _)
  | ifInput index empty zero one ihempty ihzero ihone =>
    have he := ihempty env bound henv
    have hz := ihzero env bound henv
    have ho := ihone env bound henv
    simp only [ClauseProgram.emit, ClauseProgram.outputBound]
    split
    · omega
    · omega
    · omega


theorem ClauseProgram.length_emit_le {n : Nat} (program : ClauseProgram n) (input : SAT.Word)
    (env : Env n) (bound : Nat) (henv : ∀ i, env i ≤ bound) :
    (program.emit input env).length ≤ program.outputBound bound :=
  Nat.le_trans (length_le_formulaWeight _) (program.weight_emit_le input env bound henv)

end Complexity.StackTableauEmitter
