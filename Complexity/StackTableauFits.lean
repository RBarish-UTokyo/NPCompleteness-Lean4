module

public import Complexity.StackTableauNumBounds

/-!
One polynomial capacity bounds all lexical environments and all intermediate
arithmetic values throughout a fixed first-order clause program. Loop bodies
have the same capacity at every iteration; no iterated polynomial composition
is hidden in the runtime argument.
-/

@[expose] public section

namespace Complexity.StackTableauEmitter

open StackTableauEmitterCompile

def ClauseProgram.Fits {n : Nat} : ClauseProgram n → SAT.Word → Env n → Nat → Prop
  | .clause literals, _, env, C =>
      literals.length ≤ C ∧ ∀ l ∈ literals, NumFits l.index env C
  | .seq first second, input, env, C => first.Fits input env C ∧ second.Fits input env C
  | .forDown expr body, input, env, C =>
      NumFits expr env C ∧ ∀ i, i < expr.eval env → body.Fits input (extend i env) C
  | .ifLe left right yes no, input, env, C =>
      NumFits left env C ∧ NumFits right env C ∧ yes.Fits input env C ∧ no.Fits input env C
  | .ifInput index empty zero one, input, env, C =>
      NumFits index env C ∧ empty.Fits input env C ∧ zero.Fits input env C ∧ one.Fits input env C

def literalsMagnitude {n : Nat} : List (LiteralExpr n) → Nat → Nat
  | [], _ => 0
  | literal :: rest, V => numBound literal.index V + literalsMagnitude rest V

theorem literalsMagnitude_polynomial {n : Nat} (ls : List (LiteralExpr n)) :
    PolynomialBound (literalsMagnitude ls) := by
  induction ls with
  | nil => exact PolynomialBound.constant 0
  | cons literal rest ih => exact (polynomialBound_numBound literal.index).add ih

theorem literal_numBound_le {n : Nat} (ls : List (LiteralExpr n)) (V : Nat)
    (l : LiteralExpr n) (hl : l ∈ ls) : numBound l.index V ≤ literalsMagnitude ls V := by
  induction ls with
  | nil => simp at hl
  | cons literal rest ih =>
    rcases List.mem_cons.mp hl with rfl | ht
    · exact Nat.le_add_right _ _
    · exact Nat.le_trans (ih ht) (Nat.le_add_left _ _)

def ClauseProgram.envelope {n : Nat} : ClauseProgram n → Nat → Nat
  | .clause literals, V => V + literals.length + literalsMagnitude literals V + 1
  | .seq first second, V => V + first.envelope V + second.envelope V + 1
  | .forDown expr body, V =>
      V + numBound expr V + body.envelope (numBound expr V + V) + 1
  | .ifLe left right yes no, V =>
      V + numBound left V + numBound right V + yes.envelope V + no.envelope V + 1
  | .ifInput index empty zero one, V =>
      V + numBound index V + empty.envelope V + zero.envelope V + one.envelope V + 1

theorem ClauseProgram.envelope_ge {n : Nat} (program : ClauseProgram n) (V : Nat) :
    V ≤ program.envelope V := by cases program <;> simp only [envelope] <;> omega

theorem ClauseProgram.envelope_pos {n : Nat} (program : ClauseProgram n) (V : Nat) :
    1 ≤ program.envelope V := by cases program <;> simp only [envelope] <;> omega

theorem ClauseProgram.envelope_polynomial {n : Nat} (program : ClauseProgram n) :
    PolynomialBound program.envelope := by
  induction program with
  | clause literals =>
    exact ((PolynomialBound.identity.add (PolynomialBound.constant literals.length)).add
      (literalsMagnitude_polynomial literals)).add (PolynomialBound.constant 1)
  | seq first second ihfirst ihsecond =>
    exact ((PolynomialBound.identity.add ihfirst).add ihsecond).add (PolynomialBound.constant 1)
  | forDown expr body ih =>
    exact ((PolynomialBound.identity.add (polynomialBound_numBound expr)).add
      (ih.comp ((polynomialBound_numBound expr).add PolynomialBound.identity))).add
        (PolynomialBound.constant 1)
  | ifLe left right yes no ihyes ihno =>
    exact ((((PolynomialBound.identity.add (polynomialBound_numBound left)).add
      (polynomialBound_numBound right)).add ihyes).add ihno).add (PolynomialBound.constant 1)
  | ifInput index empty zero one ihempty ihzero ihone =>
    exact ((((PolynomialBound.identity.add (polynomialBound_numBound index)).add
      ihempty).add ihzero).add ihone).add (PolynomialBound.constant 1)

theorem ClauseProgram.fits_of_envelope {n : Nat} (program : ClauseProgram n)
    (input : SAT.Word) (env : Env n) (V C : Nat) (henv : ∀ i, env i ≤ V)
    (hC : program.envelope V ≤ C) : program.Fits input env C := by
  induction program generalizing V C with
  | clause literals =>
    have hlen : literals.length ≤ C := by simp only [envelope] at hC; omega
    refine ⟨hlen, ?_⟩
    intro l hl
    apply numFits_of_bound l.index env V C henv
    have hb := literal_numBound_le literals V l hl
    simp only [envelope] at hC
    omega
  | seq first second ihfirst ihsecond =>
    simp only [envelope] at hC
    exact ⟨ihfirst env V C henv (by omega), ihsecond env V C henv (by omega)⟩
  | forDown expr body ih =>
    simp only [envelope] at hC
    have hnum : NumFits expr env (numBound expr V) := numFits_of_bound expr env V _ henv (Nat.le_refl _)
    refine ⟨numFits_of_bound expr env V C henv (by omega), ?_⟩
    intro i hi
    apply ih (extend i env) (numBound expr V + V) C _ (by omega)
    intro j
    induction j using Fin.cases with
    | zero => have h := hnum.value; change i ≤ _; omega
    | succ j => exact Nat.le_trans (henv j) (Nat.le_add_left _ _)
  | ifLe left right yes no ihyes ihno =>
    simp only [envelope] at hC
    exact ⟨numFits_of_bound left env V C henv (by omega),
      numFits_of_bound right env V C henv (by omega),
      ihyes env V C henv (by omega), ihno env V C henv (by omega)⟩
  | ifInput index empty zero one ihempty ihzero ihone =>
    simp only [envelope] at hC
    exact ⟨numFits_of_bound index env V C henv (by omega),
      ihempty env V C henv (by omega), ihzero env V C henv (by omega),
      ihone env V C henv (by omega)⟩

theorem ClauseProgram.fits_envelope {n : Nat} (program : ClauseProgram n)
    (input : SAT.Word) (env : Env n) (V : Nat) (henv : ∀ i, env i ≤ V) :
    program.Fits input env (program.envelope V) :=
  program.fits_of_envelope input env V _ henv (Nat.le_refl _)

end Complexity.StackTableauEmitter
