module

public import Complexity.Planar.ParseCert
public import Complexity.Planar.Incidence
public import Complexity.Planar.Perm
import Lean.Elab.Tactic.Omega

/-!
# Comb formulas

A *comb drawing* of a formula `f` places the variables `0, 1, …, K - 1` on a horizontal line
(the *spine*) in this order and every clause as a vertex above (*top*) or below (*bottom*) the
spine, joined to the variables of its literals.  The literal order of a clause records its side:
top clauses list their variables in increasing order, bottom clauses in decreasing order.  In
*oriented coordinates* (`v` on top, `K - 1 - v` on the bottom) the variables of every clause
increase.  Consecutive legs of a clause bound its *pockets*.  The drawing has no crossings when
any two clauses on the same side are *laminar*: one lies in a pocket of the other, or their
spans do not overlap.  `CombOK` collects these conditions.

This file sets up the occurrence numbering, the oriented legs, the nesting order `ins` between
clauses (with ties between equal two-legged clauses broken by index), the measure `mu` that it
decreases, and the selection of innermost containing clauses.
-/

@[expose] public section

namespace Complexity.Planar.Comb

open SAT

section defs

variable (f : CNF)

/-- Clause lengths. -/
def lens : List Nat := f.map List.length

/-- The number of literal occurrences. -/
def nM : Nat := (lens f).sum

/-- The number of spine positions. -/
def nK : Nat := variableCount f

/-- The first occurrence of clause `j`. -/
def off (j : Nat) : Nat := ((lens f).take j).sum

/-- Clause `j` (empty out of range). -/
def cl (j : Nat) : Clause := f[j]?.getD []

/-- The length of clause `j`. -/
def kl (j : Nat) : Nat := (cl f j).length

/-- The variable of literal `t` of clause `j`. -/
def vr (j t : Nat) : Nat := ((cl f j)[t]?.getD ⟨0, true⟩).var

/-- Clause `j` is a top clause: its first two variables increase. -/
def isTop (j : Nat) : Bool := decide (vr f j 0 < vr f j 1)

/-- Oriented position of a variable for a side. -/
def opos (s : Bool) (v : Nat) : Nat := if s then v else nK f - 1 - v

/-- The oriented position of leg `t` of clause `j`. -/
def ov (j t : Nat) : Nat := opos f (isTop f j) (vr f j t)

/-- The ends of the span of clause `j` in oriented coordinates. -/
def lo (j : Nat) : Nat := ov f j 0
def hi (j : Nat) : Nat := ov f j (kl f j - 1)

/-- The clause and slot of occurrence `e`. -/
def oj (e : Nat) : Nat := (locate (lens f) e).1
def ot (e : Nat) : Nat := (locate (lens f) e).2

/-- Clause `j` lies in a pocket of clause `j'`. -/
def NestIn (j j' : Nat) : Prop :=
  ∃ t, t + 1 < kl f j' ∧ ov f j' t ≤ lo f j ∧ hi f j ≤ ov f j' (t + 1)

/-- The spans of `j` and `j'` do not overlap. -/
def Disj (j j' : Nat) : Prop := hi f j ≤ lo f j' ∨ hi f j' ≤ lo f j

/-- `j` lies strictly inside `j'`; equal two-legged clauses nest by index. -/
def ins (j j' : Nat) : Prop := j ≠ j' ∧ NestIn f j j' ∧ ¬ (NestIn f j' j ∧ j' < j)

/-- A measure decreased by `ins`. -/
def mu (j : Nat) : Nat :=
  j + (f.length + 1) * ((hi f j - lo f j) * 2 + (if kl f j = 2 then 1 else 0))

/-- The comb conditions. -/
structure CombOK : Prop where
  K3 : 3 ≤ nK f
  len2 : ∀ j, j < f.length → 2 ≤ kl f j
  mono : ∀ j t, j < f.length → t + 1 < kl f j → ov f j t < ov f j (t + 1)
  lam : ∀ j j', j < f.length → j' < f.length → j ≠ j' → isTop f j = isTop f j' →
    NestIn f j j' ∨ NestIn f j' j ∨ Disj f j j'

end defs

/-! ## Occurrences -/

section occ

variable (f : CNF)

theorem lens_length : (lens f).length = f.length := by simp [lens]

theorem lens_get (j : Nat) (hj : j < f.length) : (lens f)[j]! = kl f j := by
  simp [lens, kl, cl, hj]

theorem kl_of_lt (j : Nat) (hj : j < f.length) : kl f j = f[j].length := by
  simp [kl, cl, List.getElem?_eq_getElem hj]

theorem vr_of_lt (j t : Nat) (hj : j < f.length) (ht : t < kl f j) :
    vr f j t = (f[j][t]'(by rw [kl_of_lt f j hj] at ht; exact ht)).var := by
  have ht' : t < f[j].length := by rw [kl_of_lt f j hj] at ht; exact ht
  simp [vr, cl, List.getElem?_eq_getElem hj, List.getElem?_eq_getElem ht']

theorem off_succ (j : Nat) (hj : j < f.length) : off f (j + 1) = off f j + kl f j := by
  unfold off
  rw [sum_take_succ (lens f) j (by rw [lens_length]; exact hj)]
  congr 1
  simp [lens, kl, cl, List.getElem?_eq_getElem hj]

theorem off_mono {j j' : Nat} (h : j ≤ j') : off f j ≤ off f j' := by
  unfold off
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  induction d with
  | zero => exact Nat.le_refl _
  | succ d ih =>
    refine Nat.le_trans (ih (by omega)) ?_
    rw [show j + (d + 1) = (j + d) + 1 by omega]
    rcases Nat.lt_or_ge (j + d) (lens f).length with h1 | h1
    · rw [sum_take_succ (lens f) (j + d) h1]; omega
    · rw [List.take_of_length_le (by omega), List.take_of_length_le (by omega)]
      exact Nat.le_refl _

theorem off_le_nM (j : Nat) : off f j ≤ nM f := by
  unfold off nM
  rcases Nat.lt_or_ge j (lens f).length with h | h
  · conv => rhs; rw [← List.take_append_drop j (lens f)]
    rw [List.sum_append]; omega
  · rw [List.take_of_length_le h]
    exact Nat.le_refl _

theorem off_add_lt (j t : Nat) (hj : j < f.length) (ht : t < kl f j) : off f j + t < nM f := by
  have h1 := off_succ f j hj
  have h2 := off_le_nM f (j + 1)
  omega

/-- Decoding an occurrence. -/
theorem occ_spec (e : Nat) (he : e < nM f) :
    oj f e < f.length ∧ ot f e < kl f (oj f e) ∧ off f (oj f e) + ot f e = e := by
  obtain ⟨h1, h2, h3⟩ := locate_spec (lens f) e he
  rw [lens_length] at h1
  rw [lens_get f _ h1] at h2
  exact ⟨h1, h2, h3⟩

/-- Encoding an occurrence. -/
theorem occ_eq (j t : Nat) (hj : j < f.length) (ht : t < kl f j) :
    oj f (off f j + t) = j ∧ ot f (off f j + t) = t := by
  have h := locate_eq (lens f) j t (by rw [lens_length]; exact hj)
    (by simp only [lens, List.getElem_map]; rw [← kl_of_lt f j hj]; exact ht)
  simp only [oj, ot, off, h, and_self]

/-- An occurrence is determined by its clause and slot. -/
theorem occ_ext {e e' : Nat} (he : e < nM f) (he' : e' < nM f) (h1 : oj f e = oj f e')
    (h2 : ot f e = ot f e') : e = e' := by
  have := (occ_spec f e he).2.2
  have := (occ_spec f e' he').2.2
  rw [h1, h2] at *
  omega

end occ

/-! ## Legs -/

section legs

variable {f : CNF}

theorem vr_lt (j t : Nat) (hj : j < f.length) (ht : t < kl f j) : vr f j t < nK f := by
  rw [vr_of_lt f j t hj ht]
  exact (variableCount_spec f).1 _ (List.getElem_mem hj) _ (List.getElem_mem _)

theorem ov_lt (h : CombOK f) (j t : Nat) (hj : j < f.length) (ht : t < kl f j) :
    ov f j t < nK f := by
  have := vr_lt j t hj ht
  have := h.K3
  unfold ov opos
  split <;> omega

theorem ov_strict (h : CombOK f) (j : Nat) (hj : j < f.length) :
    ∀ t t', t < t' → t' < kl f j → ov f j t < ov f j t' := by
  intro t t' htt' ht'
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt htt'
  induction d with
  | zero => exact h.mono j t hj (by omega)
  | succ d ih =>
    have := ih (by omega) (by omega)
    have := h.mono j (t + d + 1) hj (by omega)
    rw [show t + (d + 1) + 1 = t + d + 1 + 1 by omega]
    omega

theorem ov_le (h : CombOK f) (j : Nat) (hj : j < f.length) {t t' : Nat} (htt' : t ≤ t')
    (ht' : t' < kl f j) : ov f j t ≤ ov f j t' := by
  rcases Nat.lt_or_ge t t' with h1 | h1
  · exact Nat.le_of_lt (ov_strict h j hj t t' h1 ht')
  · have : t = t' := by omega
    subst this; exact Nat.le_refl _

theorem ov_inj (h : CombOK f) (j : Nat) (hj : j < f.length) {t t' : Nat} (ht : t < kl f j)
    (ht' : t' < kl f j) (he : ov f j t = ov f j t') : t = t' := by
  rcases Nat.lt_trichotomy t t' with h1 | h1 | h1
  · have := ov_strict h j hj t t' h1 ht'; omega
  · exact h1
  · have := ov_strict h j hj t' t h1 ht; omega

theorem lo_lt_hi (h : CombOK f) (j : Nat) (hj : j < f.length) : lo f j < hi f j := by
  have := h.len2 j hj
  exact ov_strict h j hj 0 (kl f j - 1) (by omega) (by omega)

theorem lo_le_ov (h : CombOK f) (j t : Nat) (hj : j < f.length) (ht : t < kl f j) :
    lo f j ≤ ov f j t := ov_le h j hj (Nat.zero_le t) ht

theorem ov_le_hi (h : CombOK f) (j t : Nat) (hj : j < f.length) (ht : t < kl f j) :
    ov f j t ≤ hi f j := ov_le h j hj (by omega) (by omega)

theorem hi_lt (h : CombOK f) (j : Nat) (hj : j < f.length) : hi f j < nK f := by
  have := h.len2 j hj
  exact ov_lt h j _ hj (by omega)

/-- A pocket containing an interval of positive length is unique. -/
theorem pocket_unique (h : CombOK f) (j : Nat) (hj : j < f.length) {a b t t' : Nat}
    (hab : a < b) (ht : t + 1 < kl f j) (ht' : t' + 1 < kl f j)
    (h1 : ov f j t ≤ a) (h2 : b ≤ ov f j (t + 1))
    (h1' : ov f j t' ≤ a) (h2' : b ≤ ov f j (t' + 1)) : t = t' := by
  rcases Nat.lt_trichotomy t t' with h3 | h3 | h3
  · have := ov_le h j hj (show t + 1 ≤ t' by omega) (by omega); omega
  · exact h3
  · have := ov_le h j hj (show t' + 1 ≤ t by omega) (by omega); omega

end legs

/-! ## Nesting -/

theorem mu_mod {f : CNF} {j : Nat} (hj : j < f.length) : mu f j % (f.length + 1) = j := by
  unfold mu
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]

theorem mu_inj {f : CNF} {j j' : Nat} (hj : j < f.length) (hj' : j' < f.length)
    (he : mu f j = mu f j') : j = j' := by
  have h1 := mu_mod hj
  have h2 := mu_mod hj'
  rw [he] at h1
  omega

theorem hi_two {f : CNF} {j : Nat} (hk : kl f j = 2) : hi f j = ov f j 1 := by
  unfold hi; rw [hk]

section nest

variable {f : CNF} (h : CombOK f)
include h

theorem nest_lo_hi {j j' : Nat} (hj' : j' < f.length) (hn : NestIn f j j') :
    lo f j' ≤ lo f j ∧ hi f j ≤ hi f j' := by
  obtain ⟨t, ht, h1, h2⟩ := hn
  have := lo_le_ov h j' t hj' (by omega)
  have := ov_le_hi h j' (t + 1) hj' ht
  omega

/-- Equal spans under nesting force two legs. -/
theorem nest_same_span {j j' : Nat} (hj' : j' < f.length) (hn : NestIn f j j')
    (hlo : lo f j = lo f j') (hhi : hi f j = hi f j') : kl f j' = 2 := by
  obtain ⟨t, ht, h1, h2⟩ := hn
  have h2' := h.len2 j' hj'
  have ht0 : t = 0 := by
    rcases Nat.eq_zero_or_pos t with h0 | h0
    · exact h0
    · have := ov_strict h j' hj' 0 t h0 (by omega)
      unfold lo at hlo h1; omega
  subst ht0
  rw [Nat.zero_add] at h2 ht
  have hle := ov_le_hi h j' 1 hj' ht
  have e1 : hi f j' = ov f j' (kl f j' - 1) := rfl
  have : ov f j' 1 = ov f j' (kl f j' - 1) := by omega
  have := ov_inj h j' hj' ht (by omega) this
  omega

theorem nest_mutual {j j' : Nat} (hj : j < f.length) (hj' : j' < f.length) (hn : NestIn f j j')
    (hn' : NestIn f j' j) : lo f j = lo f j' ∧ hi f j = hi f j' ∧ kl f j = 2 ∧ kl f j' = 2 := by
  have a := nest_lo_hi h hj' hn
  have b := nest_lo_hi h hj hn'
  have hlo : lo f j = lo f j' := by omega
  have hhi : hi f j = hi f j' := by omega
  exact ⟨hlo, hhi, nest_same_span h hj hn' hlo.symm hhi.symm, nest_same_span h hj' hn hlo hhi⟩

omit h in
/-- A two-legged clause contains every clause within its span. -/
theorem nest_of_two {j j' : Nat} (hk : kl f j' = 2) (hlo : lo f j' ≤ lo f j)
    (hhi : hi f j ≤ hi f j') : NestIn f j j' :=
  ⟨0, by omega, by unfold lo at hlo; exact hlo, by rw [Nat.zero_add, ← hi_two hk]; exact hhi⟩

theorem ins_mu {j j' : Nat} (hj : j < f.length) (hj' : j' < f.length) (hi' : ins f j j') :
    mu f j < mu f j' := by
  obtain ⟨hne, hn, htie⟩ := hi'
  have hl := nest_lo_hi h hj' hn
  have hlt := lo_lt_hi h j hj
  have hlt' := lo_lt_hi h j' hj'
  have key : ∀ X X' : Nat, X < X' → j + (f.length + 1) * X < j' + (f.length + 1) * X' := by
    intro X X' hX
    have := Nat.mul_le_mul_left (f.length + 1) (show X + 1 ≤ X' by omega)
    rw [Nat.mul_add, Nat.mul_one] at this
    omega
  unfold mu
  rcases Nat.lt_or_ge (hi f j - lo f j) (hi f j' - lo f j') with h1 | h1
  · apply key; split <;> split <;> omega
  · have hlo : lo f j = lo f j' := by omega
    have hhi : hi f j = hi f j' := by omega
    have hk' := nest_same_span h hj' hn hlo hhi
    have hsp : hi f j - lo f j = hi f j' - lo f j' := by omega
    rw [hsp]
    by_cases hk : kl f j = 2
    · have hn' : NestIn f j' j := nest_of_two hk (by omega) (by omega)
      have : j < j' := by
        rcases Nat.lt_trichotomy j j' with h2 | h2 | h2
        · exact h2
        · exact absurd h2 hne
        · exact absurd ⟨hn', h2⟩ htie
      simp only [hk, hk', ite_true]; omega
    · simp only [hk, hk', ite_false, ite_true]; apply key; omega

theorem ins_trans {j1 j2 j3 : Nat} (hj1 : j1 < f.length) (hj2 : j2 < f.length)
    (hj3 : j3 < f.length) (h12 : ins f j1 j2) (h23 : ins f j2 j3) : ins f j1 j3 := by
  have m12 := ins_mu h hj1 hj2 h12
  have m23 := ins_mu h hj2 hj3 h23
  obtain ⟨_, n12, t12⟩ := h12
  obtain ⟨_, n23, t23⟩ := h23
  have a := nest_lo_hi h hj2 n12
  have b := nest_lo_hi h hj3 n23
  obtain ⟨t, ht, h1, h2⟩ := n23
  have n13 : NestIn f j1 j3 := ⟨t, ht, by omega, by omega⟩
  refine ⟨fun he => by subst he; omega, n13, ?_⟩
  rintro ⟨n31, hlt⟩
  obtain ⟨hlo, hhi, hk1, hk3⟩ := nest_mutual h hj1 hj3 n13 n31
  have n21 : NestIn f j2 j1 := nest_of_two hk1 (by omega) (by omega)
  obtain ⟨_, _, _, hk2⟩ := nest_mutual h hj1 hj2 n12 n21
  have n32 : NestIn f j3 j2 := nest_of_two hk2 (by omega) (by omega)
  have : j1 < j2 := by
    rcases Nat.lt_trichotomy j1 j2 with h4 | h4 | h4
    · exact h4
    · subst h4; omega
    · exact absurd ⟨n21, h4⟩ t12
  have : j2 < j3 := by
    rcases Nat.lt_trichotomy j2 j3 with h4 | h4 | h4
    · exact h4
    · subst h4; omega
    · exact absurd ⟨n32, h4⟩ t23
  omega

/-- Two clauses with pockets containing a common interval are comparable. -/
theorem chain {j1 j2 a b : Nat} (hj1 : j1 < f.length) (hj2 : j2 < f.length) (hne : j1 ≠ j2)
    (hs : isTop f j1 = isTop f j2) (hab : a < b)
    (c1 : ∃ t, t + 1 < kl f j1 ∧ ov f j1 t ≤ a ∧ b ≤ ov f j1 (t + 1))
    (c2 : ∃ t, t + 1 < kl f j2 ∧ ov f j2 t ≤ a ∧ b ≤ ov f j2 (t + 1)) :
    ins f j1 j2 ∨ ins f j2 j1 := by
  obtain ⟨t1, ht1, a1, b1⟩ := c1
  obtain ⟨t2, ht2, a2, b2⟩ := c2
  have := lo_le_ov h j1 t1 hj1 (by omega)
  have := ov_le_hi h j1 (t1 + 1) hj1 ht1
  have := lo_le_ov h j2 t2 hj2 (by omega)
  have := ov_le_hi h j2 (t2 + 1) hj2 ht2
  rcases h.lam j1 j2 hj1 hj2 hne hs with n | n | n
  · by_cases n' : NestIn f j2 j1
    · rcases Nat.lt_or_ge j1 j2 with h4 | h4
      · left; exact ⟨hne, n, fun ⟨_, h5⟩ => by omega⟩
      · right; exact ⟨Ne.symm hne, n', fun ⟨_, h5⟩ => by omega⟩
    · left; exact ⟨hne, n, fun ⟨h5, _⟩ => n' h5⟩
  · by_cases n' : NestIn f j1 j2
    · rcases Nat.lt_or_ge j1 j2 with h4 | h4
      · left; exact ⟨hne, n', fun ⟨_, h5⟩ => by omega⟩
      · right; exact ⟨Ne.symm hne, n, fun ⟨_, h5⟩ => by omega⟩
    · right; exact ⟨Ne.symm hne, n, fun ⟨h5, _⟩ => n' h5⟩
  · unfold Disj at n; omega

end nest

/-! ## Innermost selection -/

section select

variable (f : CNF)

theorem exists_min_mu (P : Nat → Prop) (hP : ∃ j, j < f.length ∧ P j) :
    ∃ j, (j < f.length ∧ P j) ∧ ∀ j', j' < f.length → P j' → mu f j ≤ mu f j' := by
  obtain ⟨j, hj, hp⟩ := hP
  obtain ⟨r, ⟨j0, hj0, hp0, hr⟩, hmin⟩ :=
    exists_least (P := fun r => ∃ j, j < f.length ∧ P j ∧ mu f j = r) ⟨mu f j, j, hj, hp, rfl⟩
  refine ⟨j0, ⟨hj0, hp0⟩, fun j' hj' hp' => ?_⟩
  apply Nat.le_of_not_lt
  intro hlt
  exact hmin (mu f j') (by omega) ⟨j', hj', hp', rfl⟩

/-- The clause of least measure satisfying `P`. -/
noncomputable def innerSel (P : Nat → Prop) : Option Nat := by
  classical
  exact if hP : ∃ j, j < f.length ∧ P j then some (Classical.choose (exists_min_mu f P hP))
    else none

variable {f}

theorem innerSel_none {P : Nat → Prop} (hP : ∀ j, j < f.length → ¬ P j) :
    innerSel f P = none := by
  unfold innerSel
  rw [dite_eq_right]
  rintro ⟨j, hj, hp⟩
  exact hP j hj hp

theorem innerSel_some {P : Nat → Prop} {j0 : Nat} (hj0 : j0 < f.length) (hp0 : P j0)
    (hmin : ∀ j', j' < f.length → P j' → j' ≠ j0 → mu f j0 < mu f j') :
    innerSel f P = some j0 := by
  have hP : ∃ j, j < f.length ∧ P j := ⟨j0, hj0, hp0⟩
  unfold innerSel
  rw [dite_eq_left hP]
  obtain ⟨⟨hc, hpc⟩, hmc⟩ := Classical.choose_spec (exists_min_mu f P hP)
  congr 1
  apply Classical.byContradiction
  intro hne
  have := hmin _ hc hpc hne
  have := hmc j0 hj0 hp0
  omega

theorem innerSel_congr {P P' : Nat → Prop} (hP : ∀ j, j < f.length → (P j ↔ P' j)) :
    innerSel f P = innerSel f P' := by
  unfold innerSel
  have hex : (∃ j, j < f.length ∧ P j) ↔ (∃ j, j < f.length ∧ P' j) :=
    ⟨fun ⟨j, hj, hp⟩ => ⟨j, hj, (hP j hj).mp hp⟩, fun ⟨j, hj, hp⟩ => ⟨j, hj, (hP j hj).mpr hp⟩⟩
  by_cases h1 : ∃ j, j < f.length ∧ P j
  · have h2 := hex.mp h1
    rw [dite_eq_left h1, dite_eq_left h2]
    obtain ⟨⟨hc, hpc⟩, hmc⟩ := Classical.choose_spec (exists_min_mu f P h1)
    obtain ⟨⟨hc', hpc'⟩, hmc'⟩ := Classical.choose_spec (exists_min_mu f P' h2)
    have a := hmc _ hc' ((hP _ hc').mpr hpc')
    have b := hmc' _ hc ((hP _ hc).mp hpc)
    congr 1
    exact mu_inj hc hc' (by omega)
  · have h2 : ¬ ∃ j, j < f.length ∧ P' j := fun h3 => h1 (hex.mpr h3)
    rw [dite_eq_right h1, dite_eq_right h2]

end select

/-! ## Regions -/

section regions

variable (f : CNF)

/-- The pocket of `j` containing `[a, b]`. -/
noncomputable def pidx (j a b : Nat) : Nat := by
  classical
  exact if hp : ∃ t, t + 1 < kl f j ∧ ov f j t ≤ a ∧ b ≤ ov f j (t + 1) then Classical.choose hp
    else 0

/-- The label of pocket `t` of clause `j` (the outer region is `0`). -/
def plab (j t : Nat) : Nat := off f j + t + 1

/-- Pockets of `j` containing `[a, b]`. -/
def Pk (j a b : Nat) : Prop := ∃ t, t + 1 < kl f j ∧ ov f j t ≤ a ∧ b ≤ ov f j (t + 1)

/-- The region just outside clause `j`. -/
noncomputable def parent (j : Nat) : Nat :=
  match innerSel f (fun j' => isTop f j' = isTop f j ∧ ins f j j') with
  | none => 0
  | some j0 => plab f j0 (pidx f j0 (lo f j) (hi f j))

/-- The region on side `s` above the oriented gap `[u, u + 1]`. -/
noncomputable def gapR (s : Bool) (u : Nat) : Nat :=
  match innerSel f (fun j' => isTop f j' = s ∧ Pk f j' u (u + 1)) with
  | none => 0
  | some j0 => plab f j0 (pidx f j0 u (u + 1))

variable {f}

theorem pidx_eq (h : CombOK f) {j a b t : Nat} (hj : j < f.length) (hab : a < b)
    (ht : t + 1 < kl f j) (h1 : ov f j t ≤ a) (h2 : b ≤ ov f j (t + 1)) : pidx f j a b = t := by
  have hp : ∃ t, t + 1 < kl f j ∧ ov f j t ≤ a ∧ b ≤ ov f j (t + 1) := ⟨t, ht, h1, h2⟩
  unfold pidx
  rw [dite_eq_left hp]
  obtain ⟨ht', h1', h2'⟩ := Classical.choose_spec hp
  exact pocket_unique h j hj hab ht' ht h1' h2' h1 h2


theorem innerSel_spec {P : Nat → Prop} {j0 : Nat} (hs : innerSel f P = some j0) :
    j0 < f.length ∧ P j0 := by
  unfold innerSel at hs
  split at hs
  · next hP =>
    obtain ⟨⟨hc, hpc⟩, _⟩ := Classical.choose_spec (exists_min_mu f P hP)
    simp only [Option.some.injEq] at hs
    rw [← hs]; exact ⟨hc, hpc⟩
  · simp at hs

/-- Selected labels agree for equivalent selections whose pockets agree. -/
theorem sel_label_congr {P P' : Nat → Prop} {a b a' b' : Nat}
    (hP : ∀ j, j < f.length → (P j ↔ P' j))
    (hidx : ∀ j, j < f.length → P j → pidx f j a b = pidx f j a' b') :
    (match innerSel f P with | none => 0 | some j0 => plab f j0 (pidx f j0 a b)) =
      (match innerSel f P' with | none => 0 | some j0 => plab f j0 (pidx f j0 a' b')) := by
  rw [← innerSel_congr hP]
  rcases hs : innerSel f P with _ | j0
  · rfl
  · obtain ⟨hj0, hp0⟩ := innerSel_spec hs
    simp only [hidx j0 hj0 hp0]

theorem parent_eq (h : CombOK f) {j j0 t0 : Nat} (hj : j < f.length) (hj0 : j0 < f.length)
    (hs : isTop f j0 = isTop f j) (hin : ins f j j0) (ht0 : t0 + 1 < kl f j0)
    (h1 : ov f j0 t0 ≤ lo f j) (h2 : hi f j ≤ ov f j0 (t0 + 1))
    (hmin : ∀ j', j' < f.length → isTop f j' = isTop f j → ins f j j' → j' ≠ j0 →
      ins f j0 j') : parent f j = plab f j0 t0 := by
  unfold parent
  rw [innerSel_some hj0 ⟨hs, hin⟩ (fun j' hj' hp hne => ins_mu h hj0 hj' (hmin j' hj' hp.1 hp.2 hne))]
  simp only
  rw [pidx_eq h hj0 (lo_lt_hi h j hj) ht0 h1 h2]

theorem parent_out {j : Nat} (hno : ∀ j', j' < f.length → isTop f j' = isTop f j → ¬ ins f j j') :
    parent f j = 0 := by
  unfold parent
  rw [innerSel_none (fun j' hj' hp => hno j' hj' hp.1 hp.2)]

theorem gap_eq (h : CombOK f) {s : Bool} {u j0 t0 : Nat} (hj0 : j0 < f.length)
    (hs : isTop f j0 = s) (ht0 : t0 + 1 < kl f j0)
    (h1 : ov f j0 t0 ≤ u) (h2 : u + 1 ≤ ov f j0 (t0 + 1))
    (hmin : ∀ j', j' < f.length → isTop f j' = s → Pk f j' u (u + 1) → j' ≠ j0 →
      ins f j0 j') : gapR f s u = plab f j0 t0 := by
  unfold gapR
  rw [innerSel_some hj0 ⟨hs, t0, ht0, h1, h2⟩
    (fun j' hj' hp hne => ins_mu h hj0 hj' (hmin j' hj' hp.1 hp.2 hne))]
  simp only
  rw [pidx_eq h hj0 (by omega) ht0 h1 h2]

theorem gap_out {s : Bool} {u : Nat}
    (hno : ∀ j', j' < f.length → isTop f j' = s → ¬ Pk f j' u (u + 1)) : gapR f s u = 0 := by
  unfold gapR
  rw [innerSel_none (fun j' hj' hp => hno j' hj' hp.1 hp.2)]
end regions
end Complexity.Planar.Comb
