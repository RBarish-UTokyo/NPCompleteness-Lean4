module

public import Complexity.StackTableauBodySpec
import Lean.Elab.Tactic.Omega

@[expose] public section

namespace Complexity.StackTableauEmitterCompile

open StackTableauEmitter
open StackTableauProgram (Command Exec)
open StackMachine (Registers)

theorem literalSpace_pos {n : Nat} (literals : List (LiteralExpr n)) :
    0 < literalSpace literals := by
  cases literals with
  | nil => exact Nat.zero_lt_succ 0
  | cons literal rest =>
    have := Nat.le_max_left (1 + numSpace literal.index) (literalSpace rest)
    change 0 < max _ _
    omega

theorem compileLiterals_correct {n : Nat} (literals : List (LiteralExpr n))
    {k : Nat} (envRegisters : Fin n → Fin (k + 1)) (env : Env n)
    (base : Nat) (r : Registers k) (hb : 5 ≤ base)
    (he : ∀ i, 5 ≤ (envRegisters i).val ∧ (envRegisters i).val < base)
    (hk : base + literalSpace literals ≤ k + 1)
    (hv : ∀ i, r (envRegisters i) = List.replicate (env i) true)
    (hs : r (register k 3) = []) :
    ∃ time out, Exec (compileLiterals envRegisters base literals) r time (true, out) ∧
      out (register k 0) =
        SAT.writeValues SAT.encodeLiteral (literals.map (fun literal => literal.eval env)) ++
          r (register k 0) ∧
      Frame base (register k 0) r out := by
  induction literals generalizing r with
  | nil => exact ⟨1, r, Exec.stop true r, rfl, Frame.refl _ _ _⟩
  | cons literal rest ih =>
    have hbase : base < k + 1 := by have := literalSpace_pos (literal :: rest); omega
    have hrest : base + literalSpace rest ≤ k + 1 := by
      have := Nat.le_max_right (1 + numSpace literal.index) (literalSpace rest)
      change base + max _ _ ≤ _ at hk
      omega
    obtain ⟨tt, middle, ht, ho, hf⟩ := ih r hrest hv hs
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
    obtain ⟨nt, numeric, hn, hnval, hnframe⟩ := compileNum_correct literal.index
      envRegisters env (register k base) (base + 1) middle
        (by rw [register_val hbase]; omega) (by rw [register_val hbase]; omega)
        hnEnv (by
          have := Nat.le_max_left (1 + numSpace literal.index) (literalSpace rest)
          change base + max _ _ ≤ _ at hk
          omega) hmEnv hmScratch
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
    refine ⟨_, _, Exec.seq ht (Exec.seq hn hp), ?_, ?_⟩
    · simp [hnval, hnOutput, ho, LiteralExpr.eval, SAT.writeValues, List.append_assoc]
    · exact hf.trans ((hnframe.weaken (by omega)
        (Or.inr (by rw [register_val hbase]; exact Nat.le_refl _))).trans
          (Frame.set numeric _ (Or.inl rfl)))

theorem compile_clause_correct {n : Nat} (literals : List (LiteralExpr n)) :
    BodyCorrect (.clause literals) := by
  intro k envRegisters env base input r hb he hk hv hinput hs
  have hbase : base < k + 1 := by
    have := literalSpace_pos literals
    change base + literalSpace literals ≤ k + 1 at hk
    omega
  obtain ⟨lt, middle, hl, hlval, hlframe⟩ :=
    compileLiterals_correct literals envRegisters env base r hb he hk hv hs
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
    ?_, ?_, ?_⟩
  · simp [counted, register_ne (by omega : 0 < k + 1) hbase (by omega),
      register_ne (by omega : 0 < k + 1) (by omega : 2 < k + 1) (by omega),
      hlval, SAT.writeValues, SAT.encodeClause, SAT.writeList, List.append_assoc]
  · simp [counted, register_ne (by omega : 2 < k + 1) hbase (by omega),
      register_ne (by omega : 2 < k + 1) (by omega : 0 < k + 1) (by omega), hmCount]
  · exact (hlframe.toBody (Nat.le_refl _) (Or.inl rfl)).trans
      ((BodyFrame.set middle _ (Or.inr (Or.inr (Or.inr (by rw [register_val hbase]; exact Nat.le_refl _))))).trans
        ((BodyFrame.set counted _ (Or.inl rfl)).trans
          (BodyFrame.set _ _ (Or.inr (Or.inl rfl)))))

end Complexity.StackTableauEmitterCompile
