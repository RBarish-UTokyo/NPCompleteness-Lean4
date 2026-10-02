module

public import Complexity.StackTableauLiteralCorrect
public import Complexity.StackTableauNumBounds
import Lean.Elab.Tactic.Omega

@[expose] public section

namespace Complexity.StackTableauEmitterCompile

open StackTableauEmitter
open StackTableauProgram (Command Exec)
open StackMachine (Registers)

def literalCost {n : Nat} : List (LiteralExpr n) → Nat → Nat
  | [], _ => 1
  | literal :: rest, capacity =>
      literalCost rest capacity + numCost literal.index capacity + 5 * capacity + 8

def LiteralFits {n : Nat} (literals : List (LiteralExpr n)) (env : Env n)
    (capacity : Nat) : Prop := ∀ literal ∈ literals, NumFits literal.index env capacity

theorem polynomialBound_literalCost {n : Nat} (literals : List (LiteralExpr n))
    {capacity : Nat → Nat} (h : PolynomialBound capacity) :
    PolynomialBound (fun N => literalCost literals (capacity N)) := by
  induction literals with
  | nil => exact PolynomialBound.constant 1
  | cons literal rest ih =>
    exact ((ih.add (polynomialBound_numCost literal.index h)).add
      ((PolynomialBound.constant 5).mul h)).add (PolynomialBound.constant 8)

theorem compileLiterals_bounded {n : Nat} (literals : List (LiteralExpr n))
    {k : Nat} (envRegisters : Fin n → Fin (k + 1)) (env : Env n)
    (base : Nat) (r : Registers k) (hb : 5 ≤ base)
    (he : ∀ i, 5 ≤ (envRegisters i).val ∧ (envRegisters i).val < base)
    (hk : base + literalSpace literals ≤ k + 1)
    (hv : ∀ i, r (envRegisters i) = List.replicate (env i) true)
    (hs : r (register k 3) = []) (capacity : Nat)
    (hfits : LiteralFits literals env capacity) (hwork : WorkBound r capacity) :
    ∃ time out, Exec (compileLiterals envRegisters base literals) r time (true, out) ∧
      out (register k 0) =
        SAT.writeValues SAT.encodeLiteral (literals.map (fun literal => literal.eval env)) ++
          r (register k 0) ∧
      Frame base (register k 0) r out ∧ time ≤ literalCost literals capacity ∧
      WorkBound out capacity := by
  induction literals generalizing r with
  | nil => exact ⟨1, r, Exec.stop true r, rfl, Frame.refl _ _ _, Nat.le_refl _, hwork⟩
  | cons literal rest ih =>
    have hbase : base < k + 1 := by have := literalSpace_pos (literal :: rest); omega
    have hrest : base + literalSpace rest ≤ k + 1 := by
      have := Nat.le_max_right (1 + numSpace literal.index) (literalSpace rest)
      change base + max _ _ ≤ _ at hk
      omega
    obtain ⟨tt, middle, ht, ho, hf, htt, hmw⟩ := ih r hrest hv hs
      (fun l hl => hfits l (List.mem_cons_of_mem literal hl)) hwork
    have hmEnv : ∀ i, middle (envRegisters i) = List.replicate (env i) true := by
      intro i
      rw [hf _ (he i).2
        (Ne.symm (register_ne_fin (by omega) (by have := (he i).1; omega)))
        (Ne.symm (register_ne_fin (by omega) (by have := (he i).1; omega)))]
      exact hv i
    have hmScratch : middle (register k 3) = [] := by
      rw [hf _ (by rw [register_val (by omega)]; omega)
        (register_ne (by omega) (by omega) (by omega))
        (register_ne (by omega) (by omega) (by omega))]
      exact hs
    have hnEnv : ∀ i, 5 ≤ (envRegisters i).val ∧
        (envRegisters i).val < base + 1 ∧ envRegisters i ≠ register k base := by
      intro i
      refine ⟨(he i).1, by have := (he i).2; omega, ?_⟩
      exact Ne.symm (register_ne_fin hbase (by have := (he i).2; omega))
    obtain ⟨nt, numeric, hn, hnval, hnframe, hnt, hnw⟩ := compileNum_bounded literal.index
      envRegisters env (register k base) (base + 1) middle
        (by rw [register_val hbase]; omega) (by rw [register_val hbase]; omega)
        hnEnv (by
          have := Nat.le_max_left (1 + numSpace literal.index) (literalSpace rest)
          change base + max _ _ ≤ _ at hk
          omega) hmEnv hmScratch capacity
          (hfits literal (List.mem_cons_self)) hmw
    have hnScratch : numeric (register k 3) = [] :=
      (frame_scratch hnframe (by omega) (by rw [register_val hbase]; omega)
        (by omega)).trans hmScratch
    have hnOutput : numeric (register k 0) = middle (register k 0) :=
      hnframe _ (by rw [register_val (by omega)]; omega)
        (register_ne (by omega) hbase (by omega))
        (register_ne (by omega) (by omega) (by omega))
    have hp := Exec.prependLiteral (number := register k base) (output := register k 0)
      (scratch := register k 3) (sign := literal.positive)
      (register_ne hbase (by omega) (by omega))
      (register_ne hbase (by omega) (by omega))
      (register_ne (by omega) (by omega) (by omega)) hnScratch
    refine ⟨_, _, Exec.seq ht (Exec.seq hn hp), ?_, ?_, ?_, ?_⟩
    · simp [hnval, hnOutput, ho, LiteralExpr.eval, SAT.writeValues, List.append_assoc]
    · exact hf.trans ((hnframe.weaken (by omega)
        (Or.inr (by rw [register_val hbase]; exact Nat.le_refl _))).trans
          (Frame.set numeric _ (Or.inl rfl)))
    · have hlen : (numeric (register k base)).length ≤ capacity :=
        hnw _ (by rw [register_val hbase]; omega) (by rw [register_val hbase]; omega)
      change tt + (nt + (5 * (numeric (register k base)).length + 8)) ≤ _
      simp only [literalCost]
      omega
    · intro j hj0 hj2
      rw [StackMachine.set_other numeric (by
        intro heq
        exact hj0 ((congrArg Fin.val heq).trans (register_val (by omega)))) _]
      exact hnw j hj0 hj2


def clauseCost {n : Nat} (literals : List (LiteralExpr n)) (capacity : Nat) : Nat :=
  literalCost literals capacity + capacity + 7 * literals.length + 11

theorem polynomialBound_clauseCost {n : Nat} (literals : List (LiteralExpr n))
    {capacity : Nat → Nat} (h : PolynomialBound capacity) :
    PolynomialBound (fun N => clauseCost literals (capacity N)) :=
  (((polynomialBound_literalCost literals h).add h).add
    (PolynomialBound.constant (7 * literals.length))).add (PolynomialBound.constant 11)

theorem compile_clause_bounded {n : Nat} (literals : List (LiteralExpr n))
    {k : Nat} (envRegisters : Fin n → Fin (k + 1)) (env : Env n)
    (base : Nat) (input : SAT.Word) (r : Registers k) (hb : 5 ≤ base)
    (he : ∀ i, 5 ≤ (envRegisters i).val ∧ (envRegisters i).val < base)
    (hk : base + programSpace (.clause literals) ≤ k + 1)
    (hv : ∀ i, r (envRegisters i) = List.replicate (env i) true)
    (_hinput : r (register k 1) = input) (hs : r (register k 3) = [])
    (capacity : Nat) (hfits : LiteralFits literals env capacity)
    (hlength : literals.length ≤ capacity) (hwork : WorkBound r capacity) :
    ∃ time out, Exec (compileBody envRegisters base (.clause literals)) r time (true, out) ∧
      out (register k 0) =
        SAT.writeValues SAT.encodeClause ((ClauseProgram.clause literals).emit input env) ++
          r (register k 0) ∧
      out (register k 2) =
        List.replicate ((ClauseProgram.clause literals).emit input env).length true ++
          r (register k 2) ∧
      BodyFrame base r out ∧ time ≤ clauseCost literals capacity ∧ WorkBound out capacity := by
  have hbase : base < k + 1 := by
    have := literalSpace_pos literals
    change base + literalSpace literals ≤ k + 1 at hk
    omega
  obtain ⟨lt, middle, hl, hlval, hlframe, hlt, hlwork⟩ :=
    compileLiterals_bounded literals envRegisters env base r hb he hk hv hs capacity hfits hwork
  have hmScratch : middle (register k 3) = [] := by
    rw [hlframe _ (by rw [register_val (by omega)]; omega)
      (register_ne (by omega) (by omega) (by omega))
      (register_ne (by omega) (by omega) (by omega))]
    exact hs
  have hmCount : middle (register k 2) = r (register k 2) :=
    hlframe _ (by rw [register_val (by omega)]; omega)
      (register_ne (by omega) (by omega) (by omega))
      (register_ne (by omega) (by omega) (by omega))
  let counted := StackMachine.set middle (register k base) (List.replicate literals.length true)
  have hc : Exec (constant (register k base) literals.length) middle _ (true, counted) :=
    exec_constant _ _ _
  have hcScratch : counted (register k 3) = [] := by
    simp [counted, register_ne (by omega : 3 < k + 1) hbase (by omega), hmScratch]
  have hp := Exec.prependNat (number := register k base) (output := register k 0)
    (scratch := register k 3)
    (register_ne hbase (by omega) (by omega))
    (register_ne hbase (by omega) (by omega))
    (register_ne (by omega) (by omega) (by omega)) hcScratch
  refine ⟨_, _, Exec.seq hl (Exec.seq hc (Exec.seq hp (Exec.push (register k 2) true _))),
    ?_, ?_, ?_, ?_, ?_⟩
  · simp [counted, register_ne (by omega : 0 < k + 1) hbase (by omega),
      register_ne (by omega : 0 < k + 1) (by omega : 2 < k + 1) (by omega),
      hlval, SAT.writeValues, SAT.encodeClause, SAT.writeList, List.append_assoc]
  · simp [counted, register_ne (by omega : 2 < k + 1) hbase (by omega),
      register_ne (by omega : 2 < k + 1) (by omega : 0 < k + 1) (by omega), hmCount]
  · exact (hlframe.toBody (Nat.le_refl _) (Or.inl rfl)).trans
      ((BodyFrame.set middle _ (Or.inr (Or.inr (Or.inr (by rw [register_val hbase]; exact Nat.le_refl _))))).trans
        ((BodyFrame.set counted _ (Or.inl rfl)).trans
          (BodyFrame.set _ _ (Or.inr (Or.inl rfl)))))

  · have hm : (middle (register k base)).length ≤ capacity :=
      hlwork _ (by rw [register_val hbase]; omega) (by rw [register_val hbase]; omega)
    change lt + ((middle (register k base)).length + 2 * literals.length + 3 +
      (5 * (counted (register k base)).length + 6 + 2)) ≤ _
    simp only [counted, StackMachine.set_same, List.length_replicate, clauseCost]
    omega
  · intro j hj0 hj2
    have hjcount : j ≠ register k 2 := by
      intro heq
      exact hj2 ((congrArg Fin.val heq).trans (register_val (by omega)))
    have hjoutput : j ≠ register k 0 := by
      intro heq
      exact hj0 ((congrArg Fin.val heq).trans (register_val (by omega)))
    simp only [StackMachine.set_other _ hjcount _, StackMachine.set_other _ hjoutput _]
    by_cases hjbase : j = register k base
    · subst j
      simpa [counted] using hlength
    · simpa only [counted, StackMachine.set_other _ hjbase _] using hlwork j hj0 hj2

end Complexity.StackTableauEmitterCompile
