module

public import Complexity.StackTableauNumCorrect
public import Complexity.PolynomialBound
import Lean.Elab.Tactic.Omega

/-!
Quantitative execution of numeric expressions. Output bytes and the emitted
clause counter are excluded from the work capacity: arithmetic never reads
those registers. Every bound counts the actual stack macro instructions.
-/

@[expose] public section

namespace Complexity.StackTableauEmitterCompile

open StackTableauEmitter
open StackTableauProgram (Command Exec)
open StackMachine (Registers)

set_option backward.isDefEq.respectTransparency false

def WorkBound {k : Nat} (r : Registers k) (capacity : Nat) : Prop :=
  ∀ j, j.val ≠ 0 → j.val ≠ 2 → (r j).length ≤ capacity

theorem WorkBound.set {k C : Nat} {r : Registers k} (h : WorkBound r C)
    (j : Fin (k + 1)) (xs : List Bool) (hx : xs.length ≤ C) :
    WorkBound (StackMachine.set r j xs) C := by
  intro a h0 h2
  by_cases ha : a = j
  · subst a; simpa using hx
  · simpa [StackMachine.set, ha] using h a h0 h2

theorem WorkBound.set_output {k C : Nat} {r : Registers k} (h : WorkBound r C)
    (j : Fin (k + 1)) (xs : List Bool) (hj : j.val = 0 ∨ j.val = 2) :
    WorkBound (StackMachine.set r j xs) C := by
  intro a h0 h2
  have ha : a ≠ j := by intro heq; subst a; rcases hj with hj | hj <;> contradiction
  simpa [StackMachine.set, ha] using h a h0 h2

theorem WorkBound.register {k C index : Nat} {r : Registers k} (h : WorkBound r C)
    (hi : index < k + 1) (h0 : index ≠ 0) (h2 : index ≠ 2) :
    (r (register k index)).length ≤ C :=
  h _ (by simpa only [register_val hi]) (by simpa only [register_val hi])

/-- Every intermediate arithmetic result, not just the final value, fits. -/
def NumFits {n : Nat} : NumExpr n → Env n → Nat → Prop
  | .var i, env, C => env i ≤ C
  | .const value, _, C => value ≤ C
  | .pred value, env, C => NumFits value env C
  | .add left right, env, C =>
      NumFits left env C ∧ NumFits right env C ∧ left.eval env + right.eval env ≤ C
  | .mul left right, env, C =>
      NumFits left env C ∧ NumFits right env C ∧ left.eval env * right.eval env ≤ C
  | .sub left right, env, C => NumFits left env C ∧ NumFits right env C

theorem NumFits.value {n C : Nat} {e : NumExpr n} {env : Env n} (h : NumFits e env C) :
    e.eval env ≤ C := by
  induction e with
  | var i => exact h
  | const v => exact h
  | pred e ih => have he := ih h; simp only [NumExpr.eval]; omega
  | add a b _ _ => exact h.2.2
  | mul a b _ _ => exact h.2.2
  | sub a b ih _ => have ha := ih h.1; simp only [NumExpr.eval]; omega

def numNodes {n : Nat} : NumExpr n → Nat
  | .var _ | .const _ => 1
  | .pred e => numNodes e + 1
  | .add a b | .mul a b | .sub a b => numNodes a + numNodes b + 1

def numUnit (C : Nat) : Nat := 20 * (C + 1) ^ 2

def numCost {n : Nat} (e : NumExpr n) (C : Nat) : Nat := numNodes e * numUnit C

theorem numUnit_linear (C : Nat) : 20 * C + 20 ≤ numUnit C := by
  have hp : C + 1 ≤ (C + 1) ^ 2 := Nat.le_pow (by decide)
  have h := Nat.mul_le_mul_left 20 hp
  simpa [numUnit, Nat.mul_add] using h

theorem numUnit_multiply (C : Nat) : 2 * C + 5 * C + C * (5 * C + 5) + 10 ≤ numUnit C := by
  simp only [numUnit, Nat.pow_succ, Nat.pow_zero, Nat.one_mul, Nat.mul_add, Nat.add_mul,
    Nat.mul_one, Nat.one_mul]
  have hm : C * (5 * C) = 5 * (C * C) := Nat.mul_left_comm C 5 C
  rw [hm]
  omega

/-- A syntax-dependent bound on all intermediate values, as a polynomial in
one common bound on the lexical environment. -/
def numBound {n : Nat} : NumExpr n → Nat → Nat
  | .var _, V => V
  | .const v, _ => v
  | .pred e, V => numBound e V
  | .add a b, V => numBound a V + numBound b V
  | .sub a b, V => numBound a V + numBound b V
  | .mul a b, V => (numBound a V + 1) * (numBound b V + 1)

theorem polynomialBound_numBound {n : Nat} (e : NumExpr n) : PolynomialBound (numBound e) := by
  induction e with
  | var i => exact PolynomialBound.identity
  | const v => exact PolynomialBound.constant v
  | pred e ih => exact ih
  | add a b ih jh => exact ih.add jh
  | sub a b ih jh => exact ih.add jh
  | mul a b ih jh => exact (ih.add (PolynomialBound.constant 1)).mul (jh.add (PolynomialBound.constant 1))

theorem polynomialBound_numCost {n : Nat} (e : NumExpr n) {capacity : Nat → Nat}
    (h : PolynomialBound capacity) : PolynomialBound (fun N => numCost e (capacity N)) :=
  (PolynomialBound.constant (numNodes e)).mul
    ((PolynomialBound.constant 20).mul ((h.add (PolynomialBound.constant 1)).pow 2))

theorem numFits_of_bound {n : Nat} (e : NumExpr n) (env : Env n) (V C : Nat)
    (he : ∀ i, env i ≤ V) (hC : numBound e V ≤ C) : NumFits e env C := by
  induction e generalizing C with
  | var i => exact Nat.le_trans (he i) hC
  | const v => exact hC
  | pred e ih => exact ih C hC
  | add a b ih jh =>
    have ha : numBound a V ≤ C := by change numBound a V + numBound b V ≤ C at hC; omega
    have hb : numBound b V ≤ C := by change numBound a V + numBound b V ≤ C at hC; omega
    have hva := (ih (numBound a V) (Nat.le_refl _)).value
    have hvb := (jh (numBound b V) (Nat.le_refl _)).value
    exact ⟨ih C ha, jh C hb, Nat.le_trans (Nat.add_le_add hva hvb) hC⟩
  | sub a b ih jh =>
    exact ⟨ih C (by change numBound a V + numBound b V ≤ C at hC; omega),
      jh C (by change numBound a V + numBound b V ≤ C at hC; omega)⟩
  | mul a b ih jh =>
    have hab : numBound a V * numBound b V + numBound a V + numBound b V + 1 ≤ C := by
      simpa [numBound, Nat.add_mul, Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hC
    have ha : numBound a V ≤ C := by omega
    have hb : numBound b V ≤ C := by omega
    have hva := (ih (numBound a V) (Nat.le_refl _)).value
    have hvb := (jh (numBound b V) (Nat.le_refl _)).value
    exact ⟨ih C ha, jh C hb, Nat.le_trans (Nat.mul_le_mul hva hvb) (by omega)⟩

def NumBounded {n : Nat} (expression : NumExpr n) : Prop :=
  ∀ {k : Nat} (envRegisters : Fin n → Fin (k + 1)) (env : Env n)
    (dst : Fin (k + 1)) (base : Nat) (r : Registers k),
    5 ≤ dst.val → dst.val < base →
    (∀ i, 5 ≤ (envRegisters i).val ∧ (envRegisters i).val < base ∧ envRegisters i ≠ dst) →
    base + numSpace expression ≤ k + 1 →
    (∀ i, r (envRegisters i) = List.replicate (env i) true) →
    r (register k 3) = [] →
    ∀ C : Nat, NumFits expression env C → WorkBound r C →
    ∃ time out, Exec (compileNum envRegisters dst base expression) r time (true, out) ∧
      out dst = List.replicate (expression.eval env) true ∧ Frame base dst r out ∧
      time ≤ numCost expression C ∧ WorkBound out C

/-- Both operands are evaluated into disjoint fresh registers. -/
theorem eval_operands_bounded {n : Nat} (left right : NumExpr n)
    (hl : NumBounded left) (hr : NumBounded right)
    {k : Nat} (envRegisters : Fin n → Fin (k + 1)) (env : Env n)
    (dst : Fin (k + 1)) (base : Nat) (r : Registers k)
    (hd : 5 ≤ dst.val) (hdb : dst.val < base)
    (he : ∀ i, 5 ≤ (envRegisters i).val ∧ (envRegisters i).val < base ∧ envRegisters i ≠ dst)
    (hk : base + (2 + max (numSpace left) (numSpace right)) ≤ k + 1)
    (hv : ∀ i, r (envRegisters i) = List.replicate (env i) true)
    (hs : r (register k 3) = []) (C : Nat)
    (hfits : NumFits left env C ∧ NumFits right env C) (hw : WorkBound r C) :
    ∃ time out,
      Exec (.seq (compileNum envRegisters (register k base) (base + 2) left)
        (compileNum envRegisters (register k (base + 1)) (base + 2) right)) r time (true, out) ∧
      out (register k base) = List.replicate (left.eval env) true ∧
      out (register k (base + 1)) = List.replicate (right.eval env) true ∧
      out (register k 3) = [] ∧ Frame base dst r out ∧
      time ≤ numCost left C + numCost right C ∧ WorkBound out C := by
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
  obtain ⟨ltime, middle, lexec, lval, lframe, lbound, lwork⟩ :=
    hl envRegisters env (register k base) (base + 2) r
      (by rw [register_val hbase]; omega) (by rw [register_val hbase]; omega)
      henvLeft (by have := Nat.le_max_left (numSpace left) (numSpace right); omega) hv hs C hfits.1 hw
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
  obtain ⟨rtime, out, rexec, rval, rframe, rbound, rwork⟩ :=
    hr envRegisters env (register k (base + 1)) (base + 2) middle
      (by rw [register_val hbase']; omega) (by rw [register_val hbase']; omega)
      henvRight (by have := Nat.le_max_right (numSpace left) (numSpace right); omega) hv' hs' C hfits.2 lwork
  refine ⟨ltime + rtime, out, Exec.seq lexec rexec, ?_, rval, ?_, ?_, Nat.add_le_add lbound rbound, rwork⟩
  · rw [rframe (register k base) (by rw [register_val hbase]; omega)
      (register_ne hbase hbase' (by omega)) (register_ne hbase (by omega) (by omega))]
    exact lval
  · exact (frame_scratch rframe (by omega) (by rw [register_val hbase']; omega) ht).trans hs'
  · exact (lframe.weaken (by omega) (Or.inr (by rw [register_val hbase]; omega))).trans
      (rframe.weaken (by omega) (Or.inr (by rw [register_val hbase']; omega)))


theorem compileNum_bounded {n : Nat} (expression : NumExpr n) : NumBounded expression := by
  induction expression with
  | var index =>
      intro k envRegisters env dst base r hd hdb he hk hv hs C hfits hw
      have hdt : dst ≠ register k 3 := Ne.symm (register_ne_fin (by omega) (by omega))
      have hit : envRegisters index ≠ register k 3 := by
        apply Ne.symm (register_ne_fin (by omega) _)
        have := (he index).1
        omega
      refine ⟨_, _, Exec.copy (he index).2.2 hit hdt hs, ?_, ?_, ?_, ?_⟩
      · simpa [NumExpr.eval] using hv index
      · exact Frame.set r _ (Or.inl rfl)
      · have hdlen := hw dst (by omega) (by omega)
        have hslen : (r (envRegisters index)).length ≤ C := by
          rw [hv index]; simpa [NumFits] using hfits
        have hu := numUnit_linear C
        simp only [numCost, numNodes, Nat.one_mul]
        omega
      · apply hw.set
        rw [hv index]; simpa [NumFits] using hfits
  | const value =>
      intro k envRegisters env dst base r hd hdb he hk hv hs C hfits hw
      refine ⟨_, _, exec_constant dst value r, ?_, ?_, ?_, ?_⟩
      · simp [NumExpr.eval]
      · exact Frame.set r _ (Or.inl rfl)
      · have hdlen := hw dst (by omega) (by omega)
        have hu := numUnit_linear C
        change value ≤ C at hfits
        simp only [numCost, numNodes, Nat.one_mul]
        omega
      · apply hw.set
        simpa [NumFits] using hfits
  | pred value ih =>
      intro k envRegisters env dst base r hd hdb he hk hv hs C hfits hw
      obtain ⟨t, middle, hex, hval, hframe, ht, hm⟩ := ih envRegisters env dst base r hd hdb he hk hv hs C hfits hw
      refine ⟨_, _, Exec.seq hex (Exec.pop dst middle), ?_, ?_, ?_, ?_⟩
      · simp [NumExpr.eval, hval]
      · exact hframe.trans (Frame.set middle _ (Or.inl rfl))
      · have hu := numUnit_linear C
        simp only [numCost, numNodes, Nat.add_mul, Nat.one_mul] at ht ⊢
        omega
      · apply hm.set
        have hh := hm dst (by omega) (by omega)
        simpa only [List.length_tail] using Nat.le_trans (Nat.sub_le _ 1) hh
  | add left right ihl ihr =>
      intro k envRegisters env dst base r hd hdb he hk hv hs C hfits hw
      obtain ⟨t, middle, hex, hl, hr, hscratch, hf, ht, hwk⟩ :=
        eval_operands_bounded left right ihl ihr envRegisters env dst base r hd hdb he hk hv hs C ⟨hfits.1, hfits.2.1⟩ hw
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
      refine ⟨_, _, exec_seq_assoc hex (Exec.seq hcopy hadd), ?_, ?_, ?_, ?_⟩
      · simp [copied, hrd, hr, hl, NumExpr.eval, Nat.add_comm]
      · exact hf.trans ((Frame.set middle _ (Or.inl rfl)).trans
          (Frame.set copied _ (Or.inl rfl)))
      · have hdlen := hwk dst (by omega) (by omega)
        have hlfit := hfits.1.value
        have hrfit := hfits.2.1.value
        have hu := numUnit_linear C
        simp only [numCost, numNodes, Nat.add_mul, Nat.one_mul] at ht ⊢
        simp only [copied, StackMachine.set_other _ hrd, hl, hr, List.length_replicate]
        omega
      · have hcopied : WorkBound copied C := hwk.set _ _ (by
          rw [hl]; simpa using hfits.1.value)
        apply hcopied.set
        simp only [copied, StackMachine.set_same, StackMachine.set_other _ hrd,
          hl, hr, List.length_append, List.length_replicate]
        have hh := hfits.2.2
        omega
  | mul left right ihl ihr =>
      intro k envRegisters env dst base r hd hdb he hk hv hs C hfits hw
      obtain ⟨t, middle, hex, hl, hr, hscratch, hf, ht, hwk⟩ :=
        eval_operands_bounded left right ihl ihr envRegisters env dst base r hd hdb he hk hv hs C ⟨hfits.1, hfits.2.1⟩ hw
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
      refine ⟨_, _, exec_seq_assoc hex hm, ?_, ?_, ?_, ?_⟩
      · simp [NumExpr.eval, hl, Nat.mul_comm]
      · exact hf.trans ((Frame.set middle _ (Or.inr (Or.inl rfl))).trans
          (Frame.set _ _ (Or.inl rfl)))
      · have hdlen := hwk dst (by omega) (by omega)
        have hclen := hwk.register (index := 4) (by omega) (by omega) (by omega)
        have hlfit := hfits.1.value
        have hrfit := hfits.2.1.value
        have hmul := Nat.mul_le_mul hrfit (Nat.add_le_add_right (Nat.mul_le_mul_left 5 hlfit) 5)
        have hu := numUnit_multiply C
        simp only [numCost, numNodes, Nat.add_mul, Nat.one_mul] at ht ⊢
        simp only [hl, List.length_replicate]
        omega
      · apply (hwk.set (register k 4) [] (by simp)).set
        simp only [List.length_replicate, hl]
        have hh := hfits.2.2
        simpa only [Nat.mul_comm] using hh
  | sub left right ihl ihr =>
      intro k envRegisters env dst base r hd hdb he hk hv hs C hfits hw
      obtain ⟨t, middle, hex, hl, hr, hscratch, hf, ht, hwk⟩ :=
        eval_operands_bounded left right ihl ihr envRegisters env dst base r hd hdb he hk hv hs C hfits hw
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
      refine ⟨_, _, exec_seq_assoc hex (Exec.seq hcopy (Exec.seq hcounter hsub)), ?_, ?_, ?_, ?_⟩
      · simp [counted, copied, Ne.symm hcd, hl, NumExpr.eval]
      · exact hf.trans ((Frame.set middle _ (Or.inl rfl)).trans
          ((Frame.set copied _ (Or.inr (Or.inl rfl))).trans
            ((Frame.set counted _ (Or.inr (Or.inl rfl))).trans
              (Frame.set _ _ (Or.inl rfl)))))

      · have hdlen := hwk dst (by omega) (by omega)
        have hclen := hwk.register (index := 4) (by omega) (by omega) (by omega)
        have hlfit := hfits.1.value
        have hrfit := hfits.2.value
        have hu := numUnit_linear C
        simp only [numCost, numNodes, Nat.add_mul, Nat.one_mul] at ht ⊢
        simp only [copied, StackMachine.set_other _ hcd, StackMachine.set_other _ hrd,
          hl, hr, List.length_replicate]
        omega
      · have hcopied : WorkBound copied C := hwk.set _ _ (by
          rw [hl]; simpa using hfits.1.value)
        have hcounted : WorkBound counted C := hcopied.set _ _ (by
          simp only [copied, StackMachine.set_other _ hrd, hr, List.length_replicate]
          exact hfits.2.value)
        apply (hcounted.set (register k 4) [] (by simp)).set
        simp only [List.length_drop]
        exact Nat.le_trans (Nat.sub_le _ _) (hcounted dst (by omega) (by omega))

end Complexity.StackTableauEmitterCompile
