module

public import Complexity.Planar.Chk
import Lean.Elab.Tactic.Omega

/-!
# Reading numbers stored in a word

A certificate stores numbers as *thermometer fields* of a fixed width `B`: the value `v` is
written `1^v 0^(B - v)`.  A field is well formed when no `1` follows a non-`1` and its last bit
is not `1`; absent bits (past the end of the word) count as non-`1`, so fields past the end are
well formed and read as `0`.  For a well-formed field the value is the only `v < B` with
`bit (o + v - 1) = 1` (or `v = 0`) and `bit (o + v) ≠ 1`, a test on two bits, which is how
`Chk.readField` binds the value to a slot.
-/

@[expose] public section

namespace Complexity.Planar

open Chk

/-- The bit at `p` is not a `1` (it is `0` or absent). -/
def NotOne (u : List Bool) (p : Nat) : Prop := u[p]? ≠ some true

/-- The two-bit test selecting the value `v` of the field at `o`. -/
def Selected (u : List Bool) (o v : Nat) : Prop :=
  (v = 0 ∧ NotOne u o) ∨ (0 < v ∧ u[o + v - 1]? = some true ∧ NotOne u (o + v))

/-- A well-formed field of width `B` at offset `o`. -/
def FieldWF (u : List Bool) (o B : Nat) : Prop :=
  (∀ b, b + 1 < B → NotOne u (o + b) → NotOne u (o + b + 1)) ∧ NotOne u (o + B - 1)

/-- The number of leading ones among the `k` bits from `o`. -/
def leadOnes (u : List Bool) (o : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => if u[o]? = some true then leadOnes u (o + 1) k + 1 else 0

theorem leadOnes_le (u : List Bool) (o k : Nat) : leadOnes u o k ≤ k := by
  induction k generalizing o with
  | zero => simp [leadOnes]
  | succ k ih => simp only [leadOnes]; split <;> have := ih (o + 1) <;> omega

theorem leadOnes_ones (u : List Bool) (o k : Nat) :
    ∀ i, i < leadOnes u o k → u[o + i]? = some true := by
  induction k generalizing o with
  | zero => simp [leadOnes]
  | succ k ih =>
    intro i hi
    simp only [leadOnes] at hi
    split at hi
    · next h =>
      cases i with
      | zero => simpa using h
      | succ i =>
        have := ih (o + 1) i (by omega)
        rwa [show o + 1 + i = o + (i + 1) by omega] at this
    · omega

theorem leadOnes_stop (u : List Bool) (o k : Nat) (h : leadOnes u o k < k) :
    NotOne u (o + leadOnes u o k) := by
  induction k generalizing o with
  | zero => simp [leadOnes] at h
  | succ k ih =>
    simp only [leadOnes] at h ⊢
    split
    · next hb =>
      simp only [hb, ite_true] at h
      have := ih (o + 1) (by omega)
      rwa [show o + 1 + leadOnes u (o + 1) k = o + (leadOnes u (o + 1) k + 1) by omega] at this
    · next hb => simpa [NotOne] using hb

theorem leadOnes_eq (u : List Bool) (o k v : Nat) (hv : v ≤ k)
    (hones : ∀ i, i < v → u[o + i]? = some true) (hstop : v < k → NotOne u (o + v)) :
    leadOnes u o k = v := by
  induction k generalizing o v with
  | zero => simp [leadOnes]; omega
  | succ k ih =>
    simp only [leadOnes]
    cases v with
    | zero =>
      have := hstop (by omega)
      simp only [NotOne, Nat.add_zero] at this
      simp [this]
    | succ v =>
      have h0 := hones 0 (by omega)
      simp only [Nat.add_zero] at h0
      simp only [h0, ite_true]
      have := ih (o + 1) v (by omega)
        (fun i hi => by rw [show o + 1 + i = o + (i + 1) by omega]; exact hones (i + 1) (by omega))
        (fun hlt => by rw [show o + 1 + v = o + (v + 1) by omega]; exact hstop (by omega))
      omega

/-- The value of a field. -/
def tval (u : List Bool) (o B : Nat) : Nat := leadOnes u o B

theorem tval_lt {u : List Bool} {o B : Nat} (hwf : FieldWF u o B) (hB : 0 < B) :
    tval u o B < B := by
  rcases Nat.lt_or_ge (tval u o B) B with h | h
  · exact h
  · have heq : tval u o B = B := Nat.le_antisymm (leadOnes_le u o B) h
    have := leadOnes_ones u o B (B - 1) (by unfold tval at heq; omega)
    have h2 := hwf.2
    rw [show o + B - 1 = o + (B - 1) by omega] at h2
    exact absurd this h2

/-- Below a one, a well-formed field has only ones. -/
theorem FieldWF.ones_below {u : List Bool} {o B : Nat} (hwf : FieldWF u o B) (v : Nat)
    (hv : v < B) (h : u[o + v]? = some true) : ∀ i, i ≤ v → u[o + i]? = some true := by
  intro i hi
  induction h' : v - i generalizing i with
  | zero => have : i = v := by omega
            subst this; exact h
  | succ k ih =>
    have hnext := ih (i + 1) (by omega) (by omega)
    apply Classical.byContradiction
    intro hne
    have := hwf.1 i (by omega) hne
    rw [show o + i + 1 = o + (i + 1) by omega] at this
    exact this hnext

/-- **Reading a well-formed field**: the selected values are exactly the stored value. -/
theorem selected_iff {u : List Bool} {o B : Nat} (hwf : FieldWF u o B) (hB : 0 < B) (v : Nat)
    (hv : v < B) : Selected u o v ↔ v = tval u o B := by
  have hlt := tval_lt hwf hB
  constructor
  · rintro (⟨rfl, hno⟩ | ⟨hpos, hone, hno⟩)
    · symm
      apply leadOnes_eq u o B 0 (by omega) (by intro i hi; omega)
      intro _; simpa using hno
    · symm
      apply leadOnes_eq u o B v (by omega)
      · intro i hi
        have hone' : u[o + (v - 1)]? = some true := by
          rw [show o + (v - 1) = o + v - 1 by omega]; exact hone
        exact hwf.ones_below (v - 1) (by omega) hone' i (by omega)
      · intro _; exact hno
  · rintro rfl
    by_cases h0 : tval u o B = 0
    · left
      refine ⟨h0, ?_⟩
      have := leadOnes_stop u o B hlt
      unfold tval at h0; rw [h0] at this; simpa using this
    · right
      refine ⟨by omega, ?_, leadOnes_stop u o B hlt⟩
      have := leadOnes_ones u o B (tval u o B - 1) (by unfold tval at h0 ⊢; omega)
      rwa [show o + (tval u o B - 1) = o + tval u o B - 1 by omega] at this

/-- Fields past the end of the word are well formed. -/
theorem fieldWF_of_ge {u : List Bool} {o B : Nat} (h : u.length ≤ o) (hB : 0 < B) :
    FieldWF u o B := by
  constructor
  · intro b _ _ hb
    simp [List.getElem?_eq_none (show u.length ≤ o + b + 1 by omega)] at hb
  · simp [NotOne, List.getElem?_eq_none (show u.length ≤ o + B - 1 by omega)]

/-! ## Reading fields in checks -/

variable {S : Nat}

/-- Run `body` when the slot `s` holds the value selected at offset `o`. -/
def selectAt (o : Ex S) (s : Fin S) (body : Chk S) : Chk S :=
  .le (.slot s) (.const 0)
    (.bit o body body .ok)
    (.bit (.sub (.add o (.slot s)) (.const 1)) .ok .ok (.bit (.add o (.slot s)) body body .ok))

theorem holds_selectAt (u : List Bool) (o : Ex S) (s : Fin S) (body : Chk S)
    (ρ : Fin S → Nat) :
    Holds u (selectAt o s body) ρ ↔ (Selected u (o.eval ρ) (ρ s) → Holds u body ρ) := by
  simp only [selectAt, Holds, Ex.eval, Selected, NotOne]
  by_cases h0 : ρ s ≤ 0
  · have : ρ s = 0 := by omega
    simp only [this]
    rcases hb : u[o.eval ρ]? with _ | _ | _ <;> simp
  · simp only [h0, ite_false]
    have hpos : 0 < ρ s := by omega
    have hne : ρ s ≠ 0 := by omega
    rcases hb : u[o.eval ρ + ρ s - 1]? with _ | _ | _
    · simp [hpos, hne]
    · simp [hpos, hne]
    · simp only
      rcases hb2 : u[o.eval ρ + ρ s]? with _ | _ | _ <;> simp [hpos, hne]

/-- Bind the value of the field of width `B` at offset `o` to the slot `s`. -/
def readField (o B : Ex S) (s : Fin S) (body : Chk S) : Chk S :=
  .all s B (selectAt o s body)

/-- Slot `s` does not occur in `e`. -/
def Ex.fresh : Ex S → Fin S → Bool
  | .slot t, s => t != s
  | .const _, _ => true
  | .add a b, s => a.fresh s && b.fresh s
  | .mul a b, s => a.fresh s && b.fresh s
  | .sub a b, s => a.fresh s && b.fresh s

@[simp] theorem Ex.fresh_slot (t s : Fin S) : (Ex.slot t).fresh s = (t != s) := rfl
@[simp] theorem Ex.fresh_const (c : Nat) (s : Fin S) : (Ex.const c : Ex S).fresh s = true := rfl
@[simp] theorem Ex.fresh_add (a b : Ex S) (s : Fin S) :
    (Ex.add a b).fresh s = (a.fresh s && b.fresh s) := rfl
@[simp] theorem Ex.fresh_mul (a b : Ex S) (s : Fin S) :
    (Ex.mul a b).fresh s = (a.fresh s && b.fresh s) := rfl
@[simp] theorem Ex.fresh_sub (a b : Ex S) (s : Fin S) :
    (Ex.sub a b).fresh s = (a.fresh s && b.fresh s) := rfl

theorem Ex.eval_setSlot_fresh (e : Ex S) (s : Fin S) (v : Nat) (ρ : Fin S → Nat)
    (h : e.fresh s = true) : e.eval (setSlot ρ s v) = e.eval ρ := by
  induction e with
  | slot t =>
    simp only [Ex.fresh, bne_iff_ne, ne_eq] at h
    simp [Ex.eval, setSlot_other ρ h]
  | const c => rfl
  | add a b iha ihb =>
    simp only [Ex.fresh, Bool.and_eq_true] at h
    simp [Ex.eval, iha h.1, ihb h.2]
  | mul a b iha ihb =>
    simp only [Ex.fresh, Bool.and_eq_true] at h
    simp [Ex.eval, iha h.1, ihb h.2]
  | sub a b iha ihb =>
    simp only [Ex.fresh, Bool.and_eq_true] at h
    simp [Ex.eval, iha h.1, ihb h.2]

/-- **Reading a field**: when the field at the offset is well formed, the body runs with the
stored value. -/
theorem holds_readField (u : List Bool) (o B : Ex S) (s : Fin S) (body : Chk S)
    (ρ : Fin S → Nat) (hfo : o.fresh s = true)
    (hwf : FieldWF u (o.eval ρ) (B.eval ρ)) (hB : 0 < B.eval ρ) :
    Holds u (readField o B s body) ρ ↔
      Holds u body (setSlot ρ s (tval u (o.eval ρ) (B.eval ρ))) := by
  simp only [readField, holds_all, holds_selectAt, setSlot_same,
    Ex.eval_setSlot_fresh o s _ ρ hfo]
  constructor
  · intro h
    exact h _ (tval_lt hwf hB) ((selected_iff hwf hB _ (tval_lt hwf hB)).mpr rfl)
  · intro h i hi hsel
    rw [(selected_iff hwf hB i hi).mp hsel]
    exact h

end Complexity.Planar
