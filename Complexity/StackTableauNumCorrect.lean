module

public import Complexity.StackTableauEmitterCompile
import Lean.Elab.Tactic.Omega

@[expose] public section

namespace Complexity.StackTableauEmitterCompile

open StackTableauEmitter
open StackTableauProgram (Command Exec)
open StackMachine (Registers)

/-- Numeric expression execution, with an explicit frame around its work area. -/
def NumCorrect {n : Nat} (expression : NumExpr n) : Prop :=
  ∀ {k : Nat} (envRegisters : Fin n → Fin (k + 1)) (env : Env n)
    (dst : Fin (k + 1)) (base : Nat) (r : Registers k),
    5 ≤ dst.val → dst.val < base →
    (∀ i, 5 ≤ (envRegisters i).val ∧ (envRegisters i).val < base ∧ envRegisters i ≠ dst) →
    base + numSpace expression ≤ k + 1 →
    (∀ i, r (envRegisters i) = List.replicate (env i) true) →
    r (register k 3) = [] →
    ∃ time out, Exec (compileNum envRegisters dst base expression) r time (true, out) ∧
      out dst = List.replicate (expression.eval env) true ∧ Frame base dst r out

/-- Both operands are evaluated into disjoint fresh registers. -/
theorem eval_operands {n : Nat} (left right : NumExpr n)
    (hl : NumCorrect left) (hr : NumCorrect right)
    {k : Nat} (envRegisters : Fin n → Fin (k + 1)) (env : Env n)
    (dst : Fin (k + 1)) (base : Nat) (r : Registers k)
    (hd : 5 ≤ dst.val) (hdb : dst.val < base)
    (he : ∀ i, 5 ≤ (envRegisters i).val ∧ (envRegisters i).val < base ∧ envRegisters i ≠ dst)
    (hk : base + (2 + max (numSpace left) (numSpace right)) ≤ k + 1)
    (hv : ∀ i, r (envRegisters i) = List.replicate (env i) true)
    (hs : r (register k 3) = []) :
    ∃ time out,
      Exec (.seq (compileNum envRegisters (register k base) (base + 2) left)
        (compileNum envRegisters (register k (base + 1)) (base + 2) right)) r time (true, out) ∧
      out (register k base) = List.replicate (left.eval env) true ∧
      out (register k (base + 1)) = List.replicate (right.eval env) true ∧
      out (register k 3) = [] ∧ Frame base dst r out := by
  have hb : 5 ≤ base := by omega
  have hbase : base < k + 1 := by omega
  have hbase' : base + 1 < k + 1 := by omega
  have ht : 5 ≤ k + 1 := by omega
  have henvLeft : ∀ i, 5 ≤ (envRegisters i).val ∧
      (envRegisters i).val < base + 2 ∧ envRegisters i ≠ register k base := by
    intro i
    rcases he i with ⟨hi, hib, _⟩
    refine ⟨hi, by omega, ?_⟩
    intro heq
    have heq' := congrArg Fin.val heq
    rw [register_val hbase] at heq'
    omega
  obtain ⟨ltime, middle, lexec, lval, lframe⟩ :=
    hl envRegisters env (register k base) (base + 2) r
      (by rw [register_val hbase]; omega) (by rw [register_val hbase]; omega)
      henvLeft (by have := Nat.le_max_left (numSpace left) (numSpace right); omega) hv hs
  have hs' : middle (register k 3) = [] :=
    (frame_scratch lframe (by omega) (by rw [register_val hbase]; omega) ht).trans hs
  have hv' : ∀ i, middle (envRegisters i) = List.replicate (env i) true := by
    intro i
    rw [lframe (envRegisters i) (henvLeft i).2.1 (henvLeft i).2.2]
    · exact hv i
    · intro heq
      have heq' := congrArg Fin.val heq
      rw [register_val (by omega)] at heq'
      have := (he i).1
      omega
  have henvRight : ∀ i, 5 ≤ (envRegisters i).val ∧
      (envRegisters i).val < base + 2 ∧ envRegisters i ≠ register k (base + 1) := by
    intro i
    rcases he i with ⟨hi, hib, _⟩
    refine ⟨hi, by omega, ?_⟩
    intro heq
    have heq' := congrArg Fin.val heq
    rw [register_val hbase'] at heq'
    omega
  obtain ⟨rtime, out, rexec, rval, rframe⟩ :=
    hr envRegisters env (register k (base + 1)) (base + 2) middle
      (by rw [register_val hbase']; omega) (by rw [register_val hbase']; omega)
      henvRight (by have := Nat.le_max_right (numSpace left) (numSpace right); omega) hv' hs'
  refine ⟨ltime + rtime, out, Exec.seq lexec rexec, ?_, rval, ?_, ?_⟩
  · rw [rframe (register k base) (by rw [register_val hbase]; omega)
      (register_ne hbase hbase' (by omega)) (register_ne hbase (by omega) (by omega))]
    exact lval
  · exact (frame_scratch rframe (by omega) (by rw [register_val hbase']; omega) ht).trans hs'
  · exact (lframe.weaken (by omega) (Or.inr (by rw [register_val hbase]; omega))).trans
      (rframe.weaken (by omega) (Or.inr (by rw [register_val hbase']; omega)))

theorem register_ne_fin {k a : Nat} {j : Fin (k + 1)} (ha : a < k + 1)
    (h : a ≠ j.val) : register k a ≠ j := by
  intro heq
  exact h ((register_val ha).symm.trans (congrArg Fin.val heq))

theorem exec_seq_assoc {k : Nat} {a b c : Command k} {r middle : Registers k}
    {t s : Nat} {result} (hab : Exec (.seq a b) r t (true, middle))
    (hc : Exec c middle s result) : Exec (.seq a (.seq b c)) r (t + s) result := by
  cases hab with
  | seq ha hb => simpa [Nat.add_assoc] using Exec.seq ha (Exec.seq hb hc)

theorem compileNum_correct {n : Nat} (expression : NumExpr n) : NumCorrect expression := by
  induction expression with
  | var index =>
      intro k envRegisters env dst base r hd hdb he hk hv hs
      have hdt : dst ≠ register k 3 := Ne.symm (register_ne_fin (by omega) (by omega))
      have hit : envRegisters index ≠ register k 3 := by
        apply Ne.symm (register_ne_fin (by omega) _)
        have := (he index).1
        omega
      refine ⟨_, _, Exec.copy (he index).2.2 hit hdt hs, ?_, ?_⟩
      · simpa [NumExpr.eval] using hv index
      · exact Frame.set r _ (Or.inl rfl)
  | const value =>
      intro k envRegisters env dst base r hd hdb he hk hv hs
      refine ⟨_, _, exec_constant dst value r, ?_, ?_⟩
      · simp [NumExpr.eval]
      · exact Frame.set r _ (Or.inl rfl)
  | pred value ih =>
      intro k envRegisters env dst base r hd hdb he hk hv hs
      obtain ⟨t, middle, hex, hval, hframe⟩ := ih envRegisters env dst base r hd hdb he hk hv hs
      refine ⟨_, _, Exec.seq hex (Exec.pop dst middle), ?_, ?_⟩
      · simp [NumExpr.eval, hval]
      · exact hframe.trans (Frame.set middle _ (Or.inl rfl))
  | add left right ihl ihr =>
      intro k envRegisters env dst base r hd hdb he hk hv hs
      obtain ⟨t, middle, hex, hl, hr, hscratch, hf⟩ :=
        eval_operands left right ihl ihr envRegisters env dst base r hd hdb he hk hv hs
      have hleft : base < k + 1 := by change base + (2 + _) ≤ k + 1 at hk; omega
      have hright : base + 1 < k + 1 := by change base + (2 + _) ≤ k + 1 at hk; omega
      have hld : register k base ≠ dst := register_ne_fin hleft (by omega)
      have hrd : register k (base + 1) ≠ dst := register_ne_fin hright (by omega)
      have hls : register k base ≠ register k 3 := register_ne hleft (by omega) (by omega)
      have hrs : register k (base + 1) ≠ register k 3 := register_ne hright (by omega) (by omega)
      have hds : dst ≠ register k 3 := Ne.symm (register_ne_fin (by omega) (by omega))
      let copied := StackMachine.set middle dst (middle (register k base))
      have hcopy : Exec (.copy (register k base) dst (register k 3)) middle _ (true, copied) :=
        Exec.copy hld hls hds hscratch
      have hsc : copied (register k 3) = [] := by simp [copied, Ne.symm hds, hscratch]
      have hadd := Exec.add hrd hrs hds hsc
      refine ⟨_, _, exec_seq_assoc hex (Exec.seq hcopy hadd), ?_, ?_⟩
      · simp [copied, hrd, hr, hl, NumExpr.eval, Nat.add_comm]
      · exact hf.trans ((Frame.set middle _ (Or.inl rfl)).trans
          (Frame.set copied _ (Or.inl rfl)))
  | mul left right ihl ihr =>
      intro k envRegisters env dst base r hd hdb he hk hv hs
      obtain ⟨t, middle, hex, hl, hr, hscratch, hf⟩ :=
        eval_operands left right ihl ihr envRegisters env dst base r hd hdb he hk hv hs
      have hleft : base < k + 1 := by change base + (2 + _) ≤ k + 1 at hk; omega
      have hright : base + 1 < k + 1 := by change base + (2 + _) ≤ k + 1 at hk; omega
      have hld : register k base ≠ dst := register_ne_fin hleft (by omega)
      have hrd : register k (base + 1) ≠ dst := register_ne_fin hright (by omega)
      have hls : register k base ≠ register k 3 := register_ne hleft (by omega) (by omega)
      have hrs : register k (base + 1) ≠ register k 3 := register_ne hright (by omega) (by omega)
      have hds : dst ≠ register k 3 := Ne.symm (register_ne_fin (by omega) (by omega))
      have hcl : register k 4 ≠ register k base := register_ne (by omega) hleft (by omega)
      have hcd : register k 4 ≠ dst := register_ne_fin (by omega) (by omega)
      have hcs : register k 4 ≠ register k 3 := register_ne (by omega) (by omega) (by omega)
      have hrc : register k (base + 1) ≠ register k 4 := register_ne hright (by omega) (by omega)
      have hm := Exec.multiply hld hls hds hcl hcd hcs hrc hrs hrd hscratch hr
      refine ⟨_, _, exec_seq_assoc hex hm, ?_, ?_⟩
      · simp [NumExpr.eval, hl, Nat.mul_comm]
      · exact hf.trans ((Frame.set middle _ (Or.inr (Or.inl rfl))).trans
          (Frame.set _ _ (Or.inl rfl)))
  | sub left right ihl ihr =>
      intro k envRegisters env dst base r hd hdb he hk hv hs
      obtain ⟨t, middle, hex, hl, hr, hscratch, hf⟩ :=
        eval_operands left right ihl ihr envRegisters env dst base r hd hdb he hk hv hs
      have hleft : base < k + 1 := by change base + (2 + _) ≤ k + 1 at hk; omega
      have hright : base + 1 < k + 1 := by change base + (2 + _) ≤ k + 1 at hk; omega
      have hld : register k base ≠ dst := register_ne_fin hleft (by omega)
      have hrd : register k (base + 1) ≠ dst := register_ne_fin hright (by omega)
      have hls : register k base ≠ register k 3 := register_ne hleft (by omega) (by omega)
      have hrs : register k (base + 1) ≠ register k 3 := register_ne hright (by omega) (by omega)
      have hds : dst ≠ register k 3 := Ne.symm (register_ne_fin (by omega) (by omega))
      have hcd : register k 4 ≠ dst := register_ne_fin (by omega) (by omega)
      have hcs : register k 4 ≠ register k 3 := register_ne (by omega) (by omega) (by omega)
      have hrc : register k (base + 1) ≠ register k 4 := register_ne hright (by omega) (by omega)
      let copied := StackMachine.set middle dst (middle (register k base))
      have hcopy : Exec (.copy (register k base) dst (register k 3)) middle _ (true, copied) :=
        Exec.copy hld hls hds hscratch
      have hsc : copied (register k 3) = [] := by simp [copied, Ne.symm hds, hscratch]
      let counted := StackMachine.set copied (register k 4) (copied (register k (base + 1)))
      have hcounter : Exec (.copy (register k (base + 1)) (register k 4) (register k 3))
          copied _ (true, counted) := Exec.copy hrc hrs hcs hsc
      have hcval : counted (register k 4) = List.replicate (right.eval env) true := by
        simp [counted, copied, hrd, hr]
      have hsub := exec_subtractCounter (register k 4) dst hcd (right.eval env) counted hcval
      refine ⟨_, _, exec_seq_assoc hex (Exec.seq hcopy (Exec.seq hcounter hsub)), ?_, ?_⟩
      · simp [counted, copied, Ne.symm hcd, hl, NumExpr.eval]
      · exact hf.trans ((Frame.set middle _ (Or.inl rfl)).trans
          ((Frame.set copied _ (Or.inr (Or.inl rfl))).trans
            ((Frame.set counted _ (Or.inr (Or.inl rfl))).trans
              (Frame.set _ _ (Or.inl rfl)))))

end Complexity.StackTableauEmitterCompile
