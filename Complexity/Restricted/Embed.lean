module

public import Complexity.StackProgram
import Lean.Elab.Tactic.Omega

/-!
# Running a program on the low registers of a larger register file

`embed h p` runs the stack program `p` (with registers `0, …, k`) on the registers
`0, …, k` of a register file `0, …, K`; the other registers are untouched. Execution counts
are unchanged.
-/

@[expose] public section

namespace Complexity.Restricted

open StackProgram
open StackMachine (Registers set branch)

variable {k K : Nat}

def liftReg (h : k ≤ K) (j : Fin (k + 1)) : Fin (K + 1) := Fin.castLE (by omega) j

def embedOp (h : k ≤ K) {L : Type} : Op k L → Op K L
  | .halt b => .halt b
  | .goto q => .goto q
  | .push j b q => .push (liftReg h j) b q
  | .pop j e z o => .pop (liftReg h j) e z o
  | .peek j e z o => .peek (liftReg h j) e z o

def embed (h : k ≤ K) {L : Type} (p : Program k L) : Program K L where
  start := p.start
  code := fun q => embedOp h (p.code q)

/-- The low registers of a larger register file. -/
def low (h : k ≤ K) (R : Registers K) : Registers k := fun j => R (liftReg h j)

/-- Replace the low registers of `R` by `r`. -/
def merge (_h : k ≤ K) (R : Registers K) (r : Registers k) : Registers K :=
  fun i => if hi : i.val < k + 1 then r ⟨i.val, hi⟩ else R i

theorem liftReg_inj (h : k ≤ K) {i j : Fin (k + 1)} (hij : liftReg h i = liftReg h j) : i = j := by
  apply Fin.ext
  have := congrArg Fin.val hij
  simpa [liftReg] using this

@[simp] theorem low_merge (h : k ≤ K) (R : Registers K) (r : Registers k) :
    low h (merge h R r) = r := by
  funext j
  simp [low, merge, liftReg]

@[simp] theorem merge_low (h : k ≤ K) (R : Registers K) : merge h R (low h R) = R := by
  funext i
  simp only [merge, low, liftReg]
  split
  · rfl
  · rfl

@[simp] theorem merge_merge (h : k ≤ K) (R : Registers K) (r r' : Registers k) :
    merge h (merge h R r) r' = merge h R r' := by
  funext i
  simp only [merge]
  split <;> rfl

theorem merge_high (h : k ≤ K) (R : Registers K) (r : Registers k) (i : Fin (K + 1))
    (hi : k + 1 ≤ i.val) : merge h R r i = R i := by
  simp only [merge]
  split
  · omega
  · rfl

theorem merge_set (h : k ≤ K) (R : Registers K) (r : Registers k) (j : Fin (k + 1)) (v : List Bool) :
    merge h R (set r j v) = set (merge h R r) (liftReg h j) v := by
  funext i
  simp only [merge, StackMachine.set, liftReg]
  by_cases hi : i.val < k + 1
  · simp only [hi, dite_true]
    by_cases hij : i = Fin.castLE (by omega) j
    · simp [hij]
    · have : (⟨i.val, hi⟩ : Fin (k + 1)) ≠ j := by
        intro e
        apply hij
        apply Fin.ext
        simp [← e]
      simp [this, hij]
  · simp only [hi, dite_false]
    have : i ≠ Fin.castLE (by omega) j := by
      intro e
      apply hi
      rw [e]
      simp
    simp [this]

theorem step_embed (h : k ≤ K) {L : Type} (p : Program k L) (q : L) (R : Registers K) :
    StackProgram.step (embed h p) q R = match StackProgram.step p q (low h R) with
      | .inl (b, r') => .inl (b, merge h R r')
      | .inr (q', r') => .inr (q', merge h R r') := by
  have hl : ∀ j, low h R j = R (liftReg h j) := fun j => rfl
  cases hc : p.code q with
  | halt b => simp [StackProgram.step, embed, embedOp, hc]
  | goto q' => simp [StackProgram.step, embed, embedOp, hc]
  | push j b q' =>
    simp only [StackProgram.step, embed, embedOp, hc]
    rw [merge_set, merge_low, hl]
  | pop j e z o =>
    simp only [StackProgram.step, embed, embedOp, hc]
    rw [merge_set, merge_low, hl]
  | peek j e z o => simp [StackProgram.step, embed, embedOp, hc, hl]

theorem exec_embed (h : k ≤ K) {L : Type} {p : Program k L} {q : L} {r : Registers k} {t : Nat}
    {res : Bool × Registers k} (hx : Exec p q r t res) :
    ∀ R : Registers K, low h R = r → Exec (embed h p) q R t (res.1, merge h R res.2) := by
  induction hx with
  | halt hs =>
    intro R hR
    apply Exec.halt
    rw [step_embed, hR, hs]
  | @next q r q' r' t result hs _ ih =>
    intro R hR
    apply Exec.next (q' := q') (r' := merge h R r')
    · rw [step_embed, hR, hs]
    · have := ih (merge h R r') (low_merge h R r')
      simpa using this

end Complexity.Restricted
