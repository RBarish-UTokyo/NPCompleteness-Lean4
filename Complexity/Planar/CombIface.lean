module

public import Complexity.Planar.CombBasic
import Lean.Elab.Tactic.Omega

/-!
# Comb conditions clause by clause

`combOK_of` derives `CombOK` from conditions on single clauses and on pairs of clauses: every
clause has at least two literals whose variables increase (a top clause) or decrease (a bottom
clause), and any two clauses on the same side are laminar in terms of their sorted variable
lists (`LamRaw`).
-/

@[expose] public section

namespace Complexity.Planar.Comb

open SAT

/-- The side of a clause: top when its first two variables increase. -/
def sideOf (c : Clause) : Bool :=
  decide ((c[0]?.getD ({ var := 0, positive := true } : Literal)).var <
    (c[1]?.getD ({ var := 0, positive := true } : Literal)).var)

/-- The variables of a clause in increasing order (for a well-shaped clause). -/
def svars (c : Clause) : List Nat := if sideOf c then c.map Literal.var else (c.map Literal.var).reverse

/-- A sorted list lies in a pocket (between consecutive entries) of another. -/
def NestRaw (a b : List Nat) : Prop :=
  ∃ t, ∃ ht : t + 1 < b.length, b[t] ≤ a.headD 0 ∧ a.getLastD 0 ≤ b[t + 1]

/-- Two sorted lists with non-overlapping spans. -/
def DisjRaw (a b : List Nat) : Prop := a.getLastD 0 ≤ b.headD 0 ∨ b.getLastD 0 ≤ a.headD 0

/-- Laminarity of two sorted lists. -/
def LamRaw (a b : List Nat) : Prop := NestRaw a b ∨ NestRaw b a ∨ DisjRaw a b

/-- The shape of a clause: at least two literals, variables below `K`, strictly monotone in the
direction given by its side. -/
def Shape (K : Nat) (c : Clause) : Prop :=
  2 ≤ c.length ∧ (∀ l ∈ c, l.var < K) ∧
    (if sideOf c then (c.map Literal.var).Pairwise (· < ·)
      else (c.map Literal.var).Pairwise (· > ·))

section iface

variable {f : CNF}

theorem cl_eq {j : Nat} (hj : j < f.length) : cl f j = f[j] := by
  simp [cl, List.getElem?_eq_getElem hj]

theorem isTop_eq {j : Nat} (hj : j < f.length) : isTop f j = sideOf f[j] := by
  unfold isTop sideOf vr
  rw [cl_eq hj]

theorem vr_eq {j t : Nat} (hj : j < f.length) (ht : t < f[j].length) : vr f j t = (f[j][t]).var := by
  unfold vr; rw [cl_eq hj]; simp [List.getElem?_eq_getElem ht]

theorem pairwise_lt_getElem {l : List Nat} (hp : l.Pairwise (· < ·)) {a b : Nat} (hab : a < b)
    (hb : b < l.length) : l[a] < l[b] :=
  List.pairwise_iff_getElem.mp hp a b (by omega) hb hab

theorem pairwise_gt_getElem {l : List Nat} (hp : l.Pairwise (· > ·)) {a b : Nat} (hab : a < b)
    (hb : b < l.length) : l[a] > l[b] :=
  List.pairwise_iff_getElem.mp hp a b (by omega) hb hab

/-- Oriented legs in terms of sorted variables. -/
theorem ov_top {j t : Nat} (hj : j < f.length) (hs : sideOf f[j] = true) (ht : t < f[j].length) :
    ov f j t = (svars f[j])[t]'(by simp [svars, hs]; exact ht) := by
  unfold ov opos
  rw [isTop_eq hj, hs, vr_eq hj ht]
  simp [svars, hs]

theorem ov_bot {j t : Nat} (hj : j < f.length) (hs : sideOf f[j] = false) (ht : t < f[j].length) :
    ov f j t = nK f - 1 - (svars f[j])[f[j].length - 1 - t]'(by simp [svars, hs]; omega) := by
  unfold ov opos
  rw [isTop_eq hj, hs, vr_eq hj ht]
  simp only [Bool.false_eq_true, ite_false, svars, hs]
  rw [List.getElem_reverse]
  simp only [List.length_map, List.getElem_map]
  congr 3
  omega

theorem svars_length (c : Clause) : (svars c).length = c.length := by
  unfold svars; split <;> simp

theorem svars_lt {K : Nat} {c : Clause} (hc : Shape K c) {i : Nat} (hi : i < (svars c).length) :
    (svars c)[i] < K := by
  unfold svars at hi ⊢
  split
  · next hs =>
    simp only [List.getElem_map]
    exact hc.2.1 _ (List.getElem_mem _)
  · next hs =>
    simp only [List.getElem_reverse, List.getElem_map]
    exact hc.2.1 _ (List.getElem_mem _)

theorem svars_sorted {K : Nat} {c : Clause} (hc : Shape K c) : (svars c).Pairwise (· < ·) := by
  have h3 := hc.2.2
  unfold svars
  split
  · next hs => rw [ite_eq_left hs] at h3; exact h3
  · next hs =>
    rw [ite_eq_right hs] at h3
    rw [List.pairwise_reverse]
    exact h3

theorem svars_head {c : Clause} (hl : 0 < c.length) :
    (svars c).headD 0 = (svars c)[0]'(by rw [svars_length]; exact hl) := by
  rw [List.headD_eq_head?_getD, List.head?_eq_getElem?, List.getElem?_eq_getElem]
  rfl

theorem svars_last {c : Clause} (hl : 0 < c.length) :
    (svars c).getLastD 0 = (svars c)[c.length - 1]'(by rw [svars_length]; omega) := by
  rw [List.getLastD_eq_getLast?, List.getLast?_eq_getElem?, List.getElem?_eq_getElem]
  · simp [svars_length]
  · rw [svars_length]; omega

/-- **Comb conditions from clause shapes and pairwise laminarity.** -/
theorem combOK_of (hK : 3 ≤ nK f) (hshape : ∀ c ∈ f, Shape (nK f) c)
    (hlam : f.Pairwise fun c d => sideOf c = sideOf d → LamRaw (svars c) (svars d)) :
    CombOK f := by
  have sh : ∀ j (hj : j < f.length), Shape (nK f) f[j] := fun j hj => hshape _ (List.getElem_mem hj)
  have hkl : ∀ j (hj : j < f.length), kl f j = f[j].length := fun j hj => kl_of_lt f j hj
  have lamj : ∀ j j' (hj : j < f.length) (hj' : j' < f.length), j ≠ j' →
      sideOf f[j] = sideOf f[j'] → LamRaw (svars f[j]) (svars f[j']) := by
    intro j j' hj hj' hne hs
    rcases Nat.lt_or_gt_of_ne hne with c | c
    · exact List.pairwise_iff_getElem.mp hlam j j' hj hj' c hs
    · have := List.pairwise_iff_getElem.mp hlam j' j hj' hj c hs.symm
      unfold LamRaw at this ⊢
      rcases this with h1 | h1 | h1
      · exact Or.inr (Or.inl h1)
      · exact Or.inl h1
      · right; right; unfold DisjRaw at h1 ⊢; omega
  refine ⟨hK, fun j hj => by rw [hkl j hj]; exact (sh j hj).1, ?_, ?_⟩
  · intro j t hj ht
    rw [hkl j hj] at ht
    have hsort := svars_sorted (sh j hj)
    have hlen := svars_length f[j]
    cases hs : sideOf f[j]
    · rw [ov_bot hj hs (by omega), ov_bot hj hs ht]
      have h1 := pairwise_lt_getElem hsort (show f[j].length - 1 - (t + 1) < f[j].length - 1 - t
        by omega) (by omega)
      have h2 := svars_lt (sh j hj) (show f[j].length - 1 - t < (svars f[j]).length by omega)
      omega
    · rw [ov_top hj hs (by omega), ov_top hj hs ht]
      exact pairwise_lt_getElem hsort (by omega) (by omega)
  · intro j j' hj hj' hne hside
    rw [isTop_eq hj, isTop_eq hj'] at hside
    have hl := lamj j j' hj hj' hne hside
    have k1 := (sh j hj).1
    have k2 := (sh j' hj').1
    have l1 := svars_length f[j]
    have l2 := svars_length f[j']
    have s1 := svars_sorted (sh j hj)
    have s2 := svars_sorted (sh j' hj')
    unfold NestIn Disj lo hi
    simp only [hkl j hj, hkl j' hj']
    unfold LamRaw NestRaw DisjRaw at hl
    rw [svars_head (show 0 < f[j].length by omega), svars_head (show 0 < f[j'].length by omega),
      svars_last (show 0 < f[j].length by omega), svars_last (show 0 < f[j'].length by omega)] at hl
    cases hs : sideOf f[j]
    · have hs' : sideOf f[j'] = false := by rw [← hside, hs]
      have b1 : ∀ t (ht : t < f[j].length), ov f j t = nK f - 1 -
          (svars f[j])[f[j].length - 1 - t]'(by omega) := fun t ht => ov_bot hj hs ht
      have b2 : ∀ t (ht : t < f[j'].length), ov f j' t = nK f - 1 -
          (svars f[j'])[f[j'].length - 1 - t]'(by omega) := fun t ht => ov_bot hj' hs' ht
      have v1 : ∀ i (hi : i < (svars f[j]).length), (svars f[j])[i] < nK f :=
        fun i hi => svars_lt (sh j hj) hi
      have v2 : ∀ i (hi : i < (svars f[j']).length), (svars f[j'])[i] < nK f :=
        fun i hi => svars_lt (sh j' hj') hi
      rw [b1 0 (by omega), b1 _ (by omega), b2 0 (by omega), b2 _ (by omega)]
      have e1 := v1 0 (by omega)
      have e2 := v1 (f[j].length - 1) (by omega)
      have e3 := v2 0 (by omega)
      have e4 := v2 (f[j'].length - 1) (by omega)
      simp only [Nat.sub_zero, show f[j].length - 1 - (f[j].length - 1) = 0 by omega,
        show f[j'].length - 1 - (f[j'].length - 1) = 0 by omega] at *
      rcases hl with ⟨s, hs1, c1, c2⟩ | ⟨s, hs1, c1, c2⟩ | c
      · left
        refine ⟨f[j'].length - 2 - s, by omega, ?_, ?_⟩
        · rw [b2 _ (by omega)]
          have := v2 (f[j'].length - 1 - (f[j'].length - 2 - s)) (by omega)
          simp only [show f[j'].length - 1 - (f[j'].length - 2 - s) = s + 1 by omega] at this ⊢
          omega
        · rw [b2 _ (by omega)]
          have := v2 (f[j'].length - 1 - (f[j'].length - 2 - s + 1)) (by omega)
          simp only [show f[j'].length - 1 - (f[j'].length - 2 - s + 1) = s by omega] at this ⊢
          omega
      · right; left
        refine ⟨f[j].length - 2 - s, by omega, ?_, ?_⟩
        · rw [b1 _ (by omega)]
          have := v1 (f[j].length - 1 - (f[j].length - 2 - s)) (by omega)
          simp only [show f[j].length - 1 - (f[j].length - 2 - s) = s + 1 by omega] at this ⊢
          omega
        · rw [b1 _ (by omega)]
          have := v1 (f[j].length - 1 - (f[j].length - 2 - s + 1)) (by omega)
          simp only [show f[j].length - 1 - (f[j].length - 2 - s + 1) = s by omega] at this ⊢
          omega
      · right; right; omega
    · have hs' : sideOf f[j'] = true := by rw [← hside, hs]
      have b1 : ∀ t (ht : t < f[j].length), ov f j t = (svars f[j])[t]'(by omega) :=
        fun t ht => ov_top hj hs ht
      have b2 : ∀ t (ht : t < f[j'].length), ov f j' t = (svars f[j'])[t]'(by omega) :=
        fun t ht => ov_top hj' hs' ht
      rw [b1 0 (by omega), b1 _ (by omega), b2 0 (by omega), b2 _ (by omega)]
      rcases hl with ⟨s, hs1, c1, c2⟩ | ⟨s, hs1, c1, c2⟩ | c
      · left
        refine ⟨s, by omega, ?_, ?_⟩
        · rw [b2 s (by omega)]; exact c1
        · rw [b2 (s + 1) (by omega)]; exact c2
      · right; left
        refine ⟨s, by omega, ?_, ?_⟩
        · rw [b1 s (by omega)]; exact c1
        · rw [b1 (s + 1) (by omega)]; exact c2
      · right; right; exact c

end iface

end Complexity.Planar.Comb
