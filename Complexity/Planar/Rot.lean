module

public import Complexity.Planarity
import Lean.Elab.Tactic.Omega

/-!
# Cyclic successors in a list

For a list without duplicates, `rnext l d` is the element after `d` and `rprev l d` the element
before it, cyclically.  Iterating `rnext` from any element reaches every element.
-/

@[expose] public section

namespace Complexity.Planar

/-- The cyclic successor of `d` in `l`. -/
def rnext (l : List Nat) (d : Nat) : Nat := l.getD ((l.idxOf d + 1) % l.length) 0

/-- The cyclic predecessor of `d` in `l`. -/
def rprev (l : List Nat) (d : Nat) : Nat := l.getD ((l.idxOf d + l.length - 1) % l.length) 0

section

variable {l : List Nat}

theorem idxOf_getElem (hl : l.Nodup) {p : Nat} (hp : p < l.length) : l.idxOf l[p] = p :=
  hl.idxOf_getElem p hp

theorem getD_eq (p : Nat) (hp : p < l.length) : l.getD p 0 = l[p] := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hp]

theorem rnext_getElem (hl : l.Nodup) {p : Nat} (hp : p < l.length) :
    rnext l l[p] = l[(p + 1) % l.length]'(Nat.mod_lt _ (by omega)) := by
  unfold rnext
  rw [idxOf_getElem hl hp, getD_eq _ (Nat.mod_lt _ (by omega))]

theorem rprev_getElem (hl : l.Nodup) {p : Nat} (hp : p < l.length) :
    rprev l l[p] = l[(p + l.length - 1) % l.length]'(Nat.mod_lt _ (by omega)) := by
  unfold rprev
  rw [idxOf_getElem hl hp, getD_eq _ (Nat.mod_lt _ (by omega))]

theorem mem_getElem {d : Nat} (hd : d ∈ l) : ∃ p, ∃ hp : p < l.length, l[p] = d := by
  obtain ⟨p, hp, he⟩ := List.getElem_of_mem hd
  exact ⟨p, hp, he⟩

theorem rnext_mem {d : Nat} (hl : l.Nodup) (hd : d ∈ l) : rnext l d ∈ l := by
  obtain ⟨p, hp, rfl⟩ := mem_getElem hd
  rw [rnext_getElem hl hp]
  exact List.getElem_mem _

theorem rprev_mem {d : Nat} (hl : l.Nodup) (hd : d ∈ l) : rprev l d ∈ l := by
  obtain ⟨p, hp, rfl⟩ := mem_getElem hd
  rw [rprev_getElem hl hp]
  exact List.getElem_mem _

theorem rnext_rprev {d : Nat} (hl : l.Nodup) (hd : d ∈ l) : rnext l (rprev l d) = d := by
  obtain ⟨p, hp, rfl⟩ := mem_getElem hd
  rw [rprev_getElem hl hp, rnext_getElem hl (Nat.mod_lt _ (by omega))]
  congr 1
  rcases Nat.eq_zero_or_pos p with h0 | h0
  · subst h0
    rw [Nat.zero_add, Nat.mod_eq_of_lt (show l.length - 1 < l.length by omega),
      Nat.sub_add_cancel (show 1 ≤ l.length by omega), Nat.mod_self]
  · rw [show p + l.length - 1 = (p - 1) + l.length by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt (show p - 1 < l.length by omega), Nat.sub_add_cancel h0,
      Nat.mod_eq_of_lt hp]

theorem rprev_rnext {d : Nat} (hl : l.Nodup) (hd : d ∈ l) : rprev l (rnext l d) = d := by
  obtain ⟨p, hp, rfl⟩ := mem_getElem hd
  rw [rnext_getElem hl hp, rprev_getElem hl (Nat.mod_lt _ (by omega))]
  congr 1
  rcases Nat.lt_or_ge (p + 1) l.length with h1 | h1
  · rw [Nat.mod_eq_of_lt h1, show p + 1 + l.length - 1 = p + l.length by omega,
      Nat.add_mod_right, Nat.mod_eq_of_lt hp]
  · have : p + 1 = l.length := by omega
    rw [this, Nat.mod_self, Nat.zero_add,
      Nat.mod_eq_of_lt (show l.length - 1 < l.length by omega)]
    omega

theorem iterate_rnext (hl : l.Nodup) {p : Nat} (hp : p < l.length) (k : Nat) :
    iterate (rnext l) k l[p] = l[(p + k) % l.length]'(Nat.mod_lt _ (by omega)) := by
  induction k generalizing p with
  | zero => simp [iterate, Nat.mod_eq_of_lt hp]
  | succ k ih =>
    simp only [iterate]
    rw [rnext_getElem hl hp, ih (Nat.mod_lt _ (by omega))]
    congr 1
    rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod, Nat.add_assoc, Nat.add_comm 1 k]

/-- Iterating the successor reaches every element. -/
theorem rnext_reach {d d' : Nat} (hl : l.Nodup) (hd : d ∈ l) (hd' : d' ∈ l) :
    ∃ k, iterate (rnext l) k d = d' := by
  obtain ⟨p, hp, rfl⟩ := mem_getElem hd
  obtain ⟨q, hq, rfl⟩ := mem_getElem hd'
  refine ⟨q + l.length - p, ?_⟩
  rw [iterate_rnext hl hp]
  congr 1
  rw [show p + (q + l.length - p) = q + l.length by omega, Nat.add_mod_right,
    Nat.mod_eq_of_lt hq]

end

end Complexity.Planar
