module

public import Complexity.Planar.CombBasic
import Lean.Elab.Tactic.Omega

/-!
# Faces of a comb drawing

At a spine position the legs on one side are ordered counterclockwise by `key`: first the legs
of clauses starting there (inner first), then the leg of the clause passing through it (if any),
then the legs of clauses ending there (outer first).  `key_lt_iff` identifies this order with
the geometric order `before`.

Every sector of the drawing is labeled by the region containing it: a pocket of a clause or the
outer region.  The labels of sectors meeting at a clause leg and of sectors meeting along the
spine agree (`q1_first`, `q1_pred`, `q2_*`); these are the facts that make the labels constant
along the faces of the drawing.
-/

@[expose] public section

-- Section hypotheses stay in the signatures of lemmas that do not use them, so that all
-- lemmas of a section take the same arguments.
set_option linter.unusedSectionVars false

namespace Complexity.Planar.Comb

open SAT

section defs

variable (f : CNF)

/-- Occurrence `e` is a leg at oriented position `v` of a clause on side `s`. -/
def At (s : Bool) (v e : Nat) : Prop :=
  e < nM f ∧ isTop f (oj f e) = s ∧ ov f (oj f e) (ot f e) = v

/-- The angular key of a leg. -/
def key (e : Nat) : Nat :=
  if ot f e = 0 then
    (2 * hi f (oj f e) + (if kl f (oj f e) = 2 then 1 else 0)) * (f.length + 1) + oj f e
  else if ot f e + 1 = kl f (oj f e) then
    (2 * (nK f + 1 + lo f (oj f e)) + (if kl f (oj f e) = 2 then 0 else 1)) * (f.length + 1) +
      (f.length - oj f e)
  else 2 * nK f * (f.length + 1) + f.length

/-- The counterclockwise order of two legs at a vertex. -/
def before (e1 e2 : Nat) : Prop :=
  (ot f e1 = 0 ∧ ot f e2 = 0 ∧ ins f (oj f e1) (oj f e2)) ∨
  (ot f e1 = 0 ∧ ot f e2 ≠ 0) ∨
  (ot f e1 ≠ 0 ∧ ot f e1 + 1 < kl f (oj f e1) ∧ ot f e2 + 1 = kl f (oj f e2) ∧ ot f e2 ≠ 0) ∨
  (ot f e1 ≠ 0 ∧ ot f e1 + 1 = kl f (oj f e1) ∧ ot f e2 ≠ 0 ∧ ot f e2 + 1 = kl f (oj f e2) ∧
    ins f (oj f e2) (oj f e1))

end defs

theorem lex_lt {A B a b n : Nat} (hAB : A < B) (ha : a < n + 1) :
    A * (n + 1) + a < B * (n + 1) + b := by
  have := Nat.mul_le_mul_right (n + 1) (show A + 1 ≤ B by omega)
  rw [Nat.add_mul, Nat.one_mul] at this
  omega

section legs

variable {f : CNF} (h : CombOK f)
include h

theorem at_occ {s : Bool} {v e : Nat} (ha : At f s v e) :
    oj f e < f.length ∧ ot f e < kl f (oj f e) := by
  have := occ_spec f e ha.1
  exact ⟨this.1, this.2.1⟩

theorem at_same {s : Bool} {v e1 e2 : Nat} (h1 : At f s v e1) (h2 : At f s v e2)
    (hj : oj f e1 = oj f e2) : e1 = e2 := by
  have a1 := at_occ h h1
  have a2 := at_occ h h2
  have hv : ov f (oj f e1) (ot f e1) = ov f (oj f e1) (ot f e2) := by
    rw [h1.2.2]; rw [hj, h2.2.2]
  have ht := ov_inj h _ a1.1 a1.2 (by rw [hj]; exact a2.2) hv
  exact occ_ext f h1.1 h2.1 hj ht

theorem at_R {s : Bool} {v e : Nat} (ha : At f s v e) (ht : ot f e = 0) :
    lo f (oj f e) = v ∧ v < hi f (oj f e) := by
  have a := at_occ h ha
  have := lo_lt_hi h _ a.1
  have e1 : lo f (oj f e) = v := by unfold lo; rw [← ha.2.2, ht]
  exact ⟨e1, by omega⟩

theorem at_L {s : Bool} {v e : Nat} (ha : At f s v e) (ht : ot f e + 1 = kl f (oj f e)) :
    hi f (oj f e) = v ∧ lo f (oj f e) < v := by
  have a := at_occ h ha
  have := lo_lt_hi h _ a.1
  have e1 : hi f (oj f e) = v := by
    unfold hi; rw [← ha.2.2, show kl f (oj f e) - 1 = ot f e by omega]
  exact ⟨e1, by omega⟩

theorem at_M {s : Bool} {v e : Nat} (ha : At f s v e) (h0 : ot f e ≠ 0)
    (h1 : ot f e + 1 < kl f (oj f e)) : lo f (oj f e) < v ∧ v < hi f (oj f e) := by
  have a := at_occ h ha
  have := ov_strict h _ a.1 0 (ot f e) (by omega) a.2
  have := ov_strict h _ a.1 (ot f e) (kl f (oj f e) - 1) (by omega) (by omega)
  unfold lo hi
  rw [← ha.2.2]
  omega

/-- No leg lies strictly inside a pocket of its own clause. -/
theorem no_leg_inside {j t t' : Nat} (hj : j < f.length) (ht : t + 1 < kl f j)
    (ht' : t' < kl f j) (h1 : ov f j t < ov f j t') (h2 : ov f j t' < ov f j (t + 1)) : False := by
  rcases Nat.lt_or_ge t t' with h3 | h3
  · have := ov_le h j hj (show t + 1 ≤ t' by omega) ht'
    omega
  · have := ov_le h j hj h3 (by omega)
    omega

/-- At most one clause passes through a vertex on each side. -/
theorem two_mid {s : Bool} {v e1 e2 : Nat} (h1 : At f s v e1) (h2 : At f s v e2)
    (m1 : ot f e1 ≠ 0 ∧ ot f e1 + 1 < kl f (oj f e1))
    (m2 : ot f e2 ≠ 0 ∧ ot f e2 + 1 < kl f (oj f e2)) : e1 = e2 := by
  apply at_same h h1 h2
  apply Classical.byContradiction
  intro hne
  have a1 := at_occ h h1
  have a2 := at_occ h h2
  have b1 := at_M h h1 m1.1 m1.2
  have b2 := at_M h h2 m2.1 m2.2
  rcases h.lam _ _ a1.1 a2.1 hne (by rw [h1.2.1, h2.2.1]) with n | n | n
  · obtain ⟨t, ht, c1, c2⟩ := n
    exact no_leg_inside h a2.1 ht a2.2 (by rw [h2.2.2]; omega) (by rw [h2.2.2]; omega)
  · obtain ⟨t, ht, c1, c2⟩ := n
    exact no_leg_inside h a1.1 ht a1.2 (by rw [h1.2.2]; omega) (by rw [h1.2.2]; omega)
  · unfold Disj at n; omega

/-- Two legs at a vertex starting clauses: the order of their keys is the nesting order. -/
theorem key_RR {s : Bool} {v e1 e2 : Nat} (h1 : At f s v e1) (h2 : At f s v e2) (hne : e1 ≠ e2)
    (t1 : ot f e1 = 0) (t2 : ot f e2 = 0) :
    (key f e1 < key f e2 ↔ ins f (oj f e1) (oj f e2)) ∧ key f e1 ≠ key f e2 := by
  have a1 := at_occ h h1
  have a2 := at_occ h h2
  have r1 := at_R h h1 t1
  have r2 := at_R h h2 t2
  have hj : oj f e1 ≠ oj f e2 := fun he => hne (at_same h h1 h2 he)
  have hs : isTop f (oj f e1) = isTop f (oj f e2) := by rw [h1.2.1, h2.2.1]
  have k1 := h.len2 _ a1.1
  have k2 := h.len2 _ a2.1
  unfold key
  simp only [t1, t2, ite_true]
  generalize oj f e1 = j1 at *
  generalize oj f e2 = j2 at *
  have lam := h.lam j1 j2 a1.1 a2.1 hj hs
  have asym : ins f j1 j2 → ¬ ins f j2 j1 := fun i1 i2 => by
    have := ins_mu h a1.1 a2.1 i1
    have := ins_mu h a2.1 a1.1 i2
    omega
  rcases Nat.lt_trichotomy (hi f j1) (hi f j2) with c | c | c
  · have n12 : NestIn f j1 j2 := by
      rcases lam with n | n | n
      · exact n
      · have := nest_lo_hi h a1.1 n; omega
      · unfold Disj at n; omega
    have i12 : ins f j1 j2 := ⟨hj, n12, fun ⟨n', _⟩ => by have := nest_lo_hi h a1.1 n'; omega⟩
    have := lex_lt (n := f.length) (a := j1) (b := j2)
      (show 2 * hi f j1 + (if kl f j1 = 2 then 1 else 0) <
        2 * hi f j2 + (if kl f j2 = 2 then 1 else 0) by split <;> split <;> omega) (by omega)
    exact ⟨⟨fun _ => i12, fun _ => this⟩, by omega⟩
  · rcases Nat.lt_trichotomy j1 j2 with d | d | d
    all_goals first
      | (exact absurd d hj)
      | skip
    · by_cases q1 : kl f j1 = 2
      · by_cases q2 : kl f j2 = 2
        · simp only [q1, q2, ite_true, c]
          have n12 := nest_of_two (j := j1) (j' := j2) q2 (by omega) (by omega)
          exact ⟨⟨fun _ => ⟨hj, n12, fun ⟨_, d'⟩ => by omega⟩, fun _ => by omega⟩, by omega⟩
        · simp only [q1, q2, ite_true, ite_false, c]
          have n21 := nest_of_two (j := j2) (j' := j1) q1 (by omega) (by omega)
          refine ⟨⟨fun hk => ?_, fun i12 => ?_⟩, ?_⟩
          · exfalso
            have := lex_lt (n := f.length) (a := j2) (b := j1)
              (show 2 * hi f j2 + 0 < 2 * hi f j2 + 1 by omega) (by omega)
            omega
          · exact absurd (nest_same_span h a2.1 i12.2.1 (by rw [r1.1, r2.1]) c) q2
          · have := lex_lt (n := f.length) (a := j2) (b := j1)
              (show 2 * hi f j2 + 0 < 2 * hi f j2 + 1 by omega) (by omega)
            omega
      · by_cases q2 : kl f j2 = 2
        · simp only [q1, q2, ite_true, ite_false, c]
          have n12 := nest_of_two (j := j1) (j' := j2) q2 (by omega) (by omega)
          have i12 : ins f j1 j2 := ⟨hj, n12, fun ⟨n', _⟩ =>
            q1 (nest_same_span h a1.1 n' (by rw [r1.1, r2.1]) (by omega))⟩
          have := lex_lt (n := f.length) (a := j1) (b := j2)
            (show 2 * hi f j2 + 0 < 2 * hi f j2 + 1 by omega) (by omega)
          exact ⟨⟨fun _ => i12, fun _ => by omega⟩, by omega⟩
        · exfalso
          rcases lam with n | n | n
          · exact q2 (nest_same_span h a2.1 n (by rw [r1.1, r2.1]) c)
          · exact q1 (nest_same_span h a1.1 n (by rw [r1.1, r2.1]) c.symm)
          · unfold Disj at n; omega
    · by_cases q1 : kl f j1 = 2
      · by_cases q2 : kl f j2 = 2
        · simp only [q1, q2, ite_true, c]
          have n21 := nest_of_two (j := j2) (j' := j1) q1 (by omega) (by omega)
          refine ⟨⟨fun hk => by omega, fun i12 => ?_⟩, by omega⟩
          exfalso
          exact i12.2.2 ⟨n21, d⟩
        · simp only [q1, q2, ite_true, ite_false, c]
          have n21 := nest_of_two (j := j2) (j' := j1) q1 (by omega) (by omega)
          refine ⟨⟨fun hk => ?_, fun i12 => ?_⟩, ?_⟩
          · exfalso
            have := lex_lt (n := f.length) (a := j2) (b := j1)
              (show 2 * hi f j2 + 0 < 2 * hi f j2 + 1 by omega) (by omega)
            omega
          · exact absurd (nest_same_span h a2.1 i12.2.1 (by rw [r1.1, r2.1]) c) q2
          · have := lex_lt (n := f.length) (a := j2) (b := j1)
              (show 2 * hi f j2 + 0 < 2 * hi f j2 + 1 by omega) (by omega)
            omega
      · by_cases q2 : kl f j2 = 2
        · simp only [q1, q2, ite_true, ite_false, c]
          have n12 := nest_of_two (j := j1) (j' := j2) q2 (by omega) (by omega)
          have i12 : ins f j1 j2 := ⟨hj, n12, fun ⟨n', _⟩ =>
            q1 (nest_same_span h a1.1 n' (by rw [r1.1, r2.1]) (by omega))⟩
          have := lex_lt (n := f.length) (a := j1) (b := j2)
            (show 2 * hi f j2 + 0 < 2 * hi f j2 + 1 by omega) (by omega)
          exact ⟨⟨fun _ => i12, fun _ => by omega⟩, by omega⟩
        · exfalso
          rcases lam with n | n | n
          · exact q2 (nest_same_span h a2.1 n (by rw [r1.1, r2.1]) c)
          · exact q1 (nest_same_span h a1.1 n (by rw [r1.1, r2.1]) c.symm)
          · unfold Disj at n; omega
  · have n21 : NestIn f j2 j1 := by
      rcases lam with n | n | n
      · have := nest_lo_hi h a2.1 n; omega
      · exact n
      · unfold Disj at n; omega
    have i21 : ins f j2 j1 := ⟨Ne.symm hj, n21,
      fun ⟨n', _⟩ => by have := nest_lo_hi h a2.1 n'; omega⟩
    have := lex_lt (n := f.length) (a := j2) (b := j1)
      (show 2 * hi f j2 + (if kl f j2 = 2 then 1 else 0) <
        2 * hi f j1 + (if kl f j1 = 2 then 1 else 0) by split <;> split <;> omega) (by omega)
    exact ⟨⟨fun hk => by omega, fun i12 => absurd i21 (asym i12)⟩, by omega⟩


/-- Two legs at a vertex ending clauses: the order of their keys is the reverse nesting order. -/
theorem key_LL {s : Bool} {v e1 e2 : Nat} (h1 : At f s v e1) (h2 : At f s v e2) (hne : e1 ≠ e2)
    (t1 : ot f e1 ≠ 0) (l1 : ot f e1 + 1 = kl f (oj f e1))
    (t2 : ot f e2 ≠ 0) (l2 : ot f e2 + 1 = kl f (oj f e2)) :
    (key f e1 < key f e2 ↔ ins f (oj f e2) (oj f e1)) ∧ key f e1 ≠ key f e2 := by
  have a1 := at_occ h h1
  have a2 := at_occ h h2
  have r1 := at_L h h1 l1
  have r2 := at_L h h2 l2
  have hj : oj f e1 ≠ oj f e2 := fun he => hne (at_same h h1 h2 he)
  have hs : isTop f (oj f e1) = isTop f (oj f e2) := by rw [h1.2.1, h2.2.1]
  unfold key
  simp only [t1, t2, l1, l2, ite_false, ite_true]
  generalize oj f e1 = j1 at *
  generalize oj f e2 = j2 at *
  have lam := h.lam j1 j2 a1.1 a2.1 hj hs
  have asym : ins f j1 j2 → ¬ ins f j2 j1 := fun i1 i2 => by
    have := ins_mu h a1.1 a2.1 i1
    have := ins_mu h a2.1 a1.1 i2
    omega
  rcases Nat.lt_trichotomy (lo f j1) (lo f j2) with c | c | c
  · have n21 : NestIn f j2 j1 := by
      rcases lam with n | n | n
      · have := nest_lo_hi h a2.1 n; omega
      · exact n
      · unfold Disj at n; omega
    have i21 : ins f j2 j1 := ⟨Ne.symm hj, n21,
      fun ⟨n', _⟩ => by have := nest_lo_hi h a2.1 n'; omega⟩
    have := lex_lt (n := f.length) (a := f.length - j1) (b := f.length - j2)
      (show 2 * (nK f + 1 + lo f j1) + (if kl f j1 = 2 then 0 else 1) <
        2 * (nK f + 1 + lo f j2) + (if kl f j2 = 2 then 0 else 1) by split <;> split <;> omega)
      (by omega)
    exact ⟨⟨fun _ => i21, fun _ => this⟩, by omega⟩
  · by_cases q1 : kl f j1 = 2
    · by_cases q2 : kl f j2 = 2
      · simp only [q1, q2, ite_true, c]
        have n21 := nest_of_two (j := j2) (j' := j1) q1 (by omega) (by omega)
        have n12 := nest_of_two (j := j1) (j' := j2) q2 (by omega) (by omega)
        refine ⟨⟨fun hk => ⟨Ne.symm hj, n21, fun ⟨_, d⟩ => by omega⟩, fun i21 => ?_⟩, ?_⟩
        · have : j2 < j1 := by
            rcases Nat.lt_trichotomy j2 j1 with d | d | d
            · exact d
            · exact absurd d.symm hj
            · exact absurd ⟨n12, d⟩ i21.2.2
          omega
        · omega
      · simp only [q1, q2, ite_true, ite_false, c]
        have n21 := nest_of_two (j := j2) (j' := j1) q1 (by omega) (by omega)
        have i21 : ins f j2 j1 := ⟨Ne.symm hj, n21, fun ⟨n', _⟩ =>
          q2 (nest_same_span h a2.1 n' (by omega) (by omega))⟩
        have := lex_lt (n := f.length) (a := f.length - j1) (b := f.length - j2)
          (show 2 * (nK f + 1 + lo f j2) + 0 < 2 * (nK f + 1 + lo f j2) + 1 by omega) (by omega)
        exact ⟨⟨fun _ => i21, fun _ => this⟩, by omega⟩
    · by_cases q2 : kl f j2 = 2
      · simp only [q1, q2, ite_true, ite_false, c]
        have := lex_lt (n := f.length) (a := f.length - j2) (b := f.length - j1)
          (show 2 * (nK f + 1 + lo f j2) + 0 < 2 * (nK f + 1 + lo f j2) + 1 by omega) (by omega)
        refine ⟨⟨fun hk => by omega, fun i21 => ?_⟩, by omega⟩
        exact absurd (nest_same_span h a1.1 i21.2.1 (by omega) (by omega)) q1
      · exfalso
        rcases lam with n | n | n
        · exact q2 (nest_same_span h a2.1 n c (by omega))
        · exact q1 (nest_same_span h a1.1 n c.symm (by omega))
        · unfold Disj at n; omega
  · have n12 : NestIn f j1 j2 := by
      rcases lam with n | n | n
      · exact n
      · have := nest_lo_hi h a1.1 n; omega
      · unfold Disj at n; omega
    have i12 : ins f j1 j2 := ⟨hj, n12, fun ⟨n', _⟩ => by have := nest_lo_hi h a1.1 n'; omega⟩
    have := lex_lt (n := f.length) (a := f.length - j2) (b := f.length - j1)
      (show 2 * (nK f + 1 + lo f j2) + (if kl f j2 = 2 then 0 else 1) <
        2 * (nK f + 1 + lo f j1) + (if kl f j1 = 2 then 0 else 1) by split <;> split <;> omega)
      (by omega)
    exact ⟨⟨fun hk => by omega, fun i21 => absurd i21 (asym i12)⟩, by omega⟩

theorem key_R_bound {s : Bool} {v e : Nat} (ha : At f s v e) (t0 : ot f e = 0) :
    key f e < 2 * nK f * (f.length + 1) := by
  have a := at_occ h ha
  have := hi_lt h _ a.1
  unfold key
  simp only [t0, ite_true]
  have := lex_lt (n := f.length) (a := oj f e) (b := 0)
    (show 2 * hi f (oj f e) + (if kl f (oj f e) = 2 then 1 else 0) < 2 * nK f by split <;> omega)
    (by omega)
  omega

omit h in
theorem key_M_eq {e : Nat} (t0 : ot f e ≠ 0) (tm : ot f e + 1 < kl f (oj f e)) :
    key f e = 2 * nK f * (f.length + 1) + f.length := by
  unfold key
  simp only [t0, ite_false, show ot f e + 1 ≠ kl f (oj f e) by omega]

theorem key_L_bound {s : Bool} {v e : Nat} (_ha : At f s v e) (t0 : ot f e ≠ 0)
    (tl : ot f e + 1 = kl f (oj f e)) : 2 * nK f * (f.length + 1) + f.length < key f e := by
  unfold key
  simp only [t0, tl, ite_false, ite_true]
  have := lex_lt (n := f.length) (a := f.length) (b := f.length - oj f e)
    (show 2 * nK f < 2 * (nK f + 1 + lo f (oj f e)) + (if kl f (oj f e) = 2 then 0 else 1) by
      split <;> omega) (by omega)
  omega

/-- Each leg starts, passes through or ends its clause. -/
theorem leg_cases {s : Bool} {v e : Nat} (ha : At f s v e) :
    ot f e = 0 ∨ (ot f e ≠ 0 ∧ ot f e + 1 < kl f (oj f e)) ∨
      (ot f e ≠ 0 ∧ ot f e + 1 = kl f (oj f e)) := by
  have := (at_occ h ha).2
  omega

/-- **The key order is the geometric order.** -/
theorem key_lt_iff {s : Bool} {v e1 e2 : Nat} (h1 : At f s v e1) (h2 : At f s v e2)
    (hne : e1 ≠ e2) : key f e1 < key f e2 ↔ before f e1 e2 := by
  have k1 := h.len2 _ (at_occ h h1).1
  have k2 := h.len2 _ (at_occ h h2).1
  unfold before
  rcases leg_cases h h1 with c1 | c1 | c1 <;> rcases leg_cases h h2 with c2 | c2 | c2
  · rw [(key_RR h h1 h2 hne c1 c2).1]
    constructor
    · intro hi'; left; exact ⟨c1, c2, hi'⟩
    · rintro (⟨_, _, hi'⟩ | ⟨_, h3⟩ | ⟨h3, _⟩ | ⟨h3, _⟩)
      · exact hi'
      · exact absurd c2 h3
      · exact absurd c1 h3
      · exact absurd c1 h3
  · have := key_R_bound h h1 c1
    rw [key_M_eq c2.1 c2.2]
    constructor
    · intro _; right; left; exact ⟨c1, c2.1⟩
    · intro _; omega
  · have := key_R_bound h h1 c1
    have := key_L_bound h h2 c2.1 c2.2
    constructor
    · intro _; right; left; exact ⟨c1, c2.1⟩
    · intro _; omega
  · have := key_R_bound h h2 c2
    rw [key_M_eq c1.1 c1.2]
    constructor
    · intro hk; omega
    · rintro (⟨h3, _⟩ | ⟨h3, _⟩ | ⟨_, _, _, h3⟩ | ⟨_, _, h3, _⟩)
      · exact absurd h3 c1.1
      · exact absurd h3 c1.1
      · exact absurd c2 h3
      · exact absurd c2 h3
  · exact absurd (two_mid h h1 h2 c1 c2) hne
  · have := key_L_bound h h2 c2.1 c2.2
    rw [key_M_eq c1.1 c1.2]
    constructor
    · intro _; right; right; left; exact ⟨c1.1, c1.2, c2.2, c2.1⟩
    · intro _; omega
  · have := key_R_bound h h2 c2
    have := key_L_bound h h1 c1.1 c1.2
    constructor
    · intro hk; omega
    · rintro (⟨h3, _⟩ | ⟨h3, _⟩ | ⟨_, _, _, h3⟩ | ⟨_, _, h3, _⟩)
      · exact absurd h3 c1.1
      · exact absurd h3 c1.1
      · exact absurd c2 h3
      · exact absurd c2 h3
  · have := key_L_bound h h1 c1.1 c1.2
    rw [key_M_eq c2.1 c2.2]
    constructor
    · intro hk; omega
    · rintro (⟨h3, _⟩ | ⟨h3, _⟩ | ⟨_, h3, _, _⟩ | ⟨_, _, _, h3, _⟩)
      · exact absurd h3 c1.1
      · exact absurd h3 c1.1
      · omega
      · omega
  · rw [(key_LL h h1 h2 hne c1.1 c1.2 c2.1 c2.2).1]
    constructor
    · intro hi'; right; right; right; exact ⟨c1.1, c1.2, c2.1, c2.2, hi'⟩
    · rintro (⟨h3, _⟩ | ⟨h3, _⟩ | ⟨_, h3, _, _⟩ | ⟨_, _, _, _, hi'⟩)
      · exact absurd h3 c1.1
      · exact absurd h3 c1.1
      · omega
      · exact hi'

theorem key_ne {s : Bool} {v e1 e2 : Nat} (h1 : At f s v e1) (h2 : At f s v e2)
    (hne : e1 ≠ e2) : key f e1 ≠ key f e2 := by
  have k1 := h.len2 _ (at_occ h h1).1
  have k2 := h.len2 _ (at_occ h h2).1
  rcases leg_cases h h1 with c1 | c1 | c1 <;> rcases leg_cases h h2 with c2 | c2 | c2
  · exact (key_RR h h1 h2 hne c1 c2).2
  · have := key_R_bound h h1 c1; rw [key_M_eq c2.1 c2.2]; omega
  · have := key_R_bound h h1 c1; have := key_L_bound h h2 c2.1 c2.2; omega
  · have := key_R_bound h h2 c2; rw [key_M_eq c1.1 c1.2]; omega
  · exact absurd (two_mid h h1 h2 c1 c2) hne
  · have := key_L_bound h h2 c2.1 c2.2; rw [key_M_eq c1.1 c1.2]; omega
  · have := key_R_bound h h2 c2; have := key_L_bound h h1 c1.1 c1.2; omega
  · have := key_L_bound h h1 c1.1 c1.2; rw [key_M_eq c2.1 c2.2]; omega
  · exact (key_LL h h1 h2 hne c1.1 c1.2 c2.1 c2.2).2
end legs


/-! ## Labels of sectors -/

section labels

variable (f : CNF)

/-- The label of the sector counterclockwise after a leg at its spine vertex. -/
noncomputable def legLbl (e : Nat) : Nat :=
  if ot f e = 0 then parent f (oj f e) else plab f (oj f e) (ot f e - 1)

/-- The label of the sector counterclockwise after a leg at its clause vertex. -/
noncomputable def clauseLbl (e : Nat) : Nat :=
  if ot f e + 1 < kl f (oj f e) then plab f (oj f e) (ot f e) else parent f (oj f e)

end labels

section q

variable {f : CNF} (h : CombOK f)
include h

omit h in
/-- The occurrence of leg `t` of clause `j`. -/
theorem mk_at {s : Bool} {v j t : Nat} (hj : j < f.length) (ht : t < kl f j)
    (hs : isTop f j = s) (hv : ov f j t = v) :
    At f s v (off f j + t) ∧ oj f (off f j + t) = j ∧ ot f (off f j + t) = t := by
  obtain ⟨e1, e2⟩ := occ_eq f j t hj ht
  refine ⟨⟨off_add_lt f j t hj ht, ?_, ?_⟩, e1, e2⟩
  · rw [e1]; exact hs
  · rw [e1, e2]; exact hv

theorem before_lt {s : Bool} {v e1 e2 : Nat} (h1 : At f s v e1) (h2 : At f s v e2)
    (hne : e1 ≠ e2) (hb : before f e1 e2) : key f e1 < key f e2 :=
  (key_lt_iff h h1 h2 hne).mpr hb

theorem lt_before {s : Bool} {v e1 e2 : Nat} (h1 : At f s v e1) (h2 : At f s v e2)
    (hne : e1 ≠ e2) (hk : key f e1 < key f e2) : before f e1 e2 :=
  (key_lt_iff h h1 h2 hne).mp hk

omit h in
/-- A pocket containing an interval contains its sub-intervals. -/
theorem pk_mono {j' a b a' b' : Nat} (hp : Pk f j' a b) (h1 : a ≤ a') (h2 : b' ≤ b) :
    Pk f j' a' b' := by
  obtain ⟨t, ht, c1, c2⟩ := hp
  exact ⟨t, ht, by omega, by omega⟩

/-- **The first leg at a vertex.** -/
theorem q1_first {s : Bool} {v x : Nat} (hx : At f s v x)
    (hfirst : ∀ z, At f s v z → z ≠ x → key f x < key f z) :
    gapR f s v = clauseLbl f x := by
  have ax := at_occ h hx
  have k2 := h.len2 _ ax.1
  have contra : ∀ z, At f s v z → z ≠ x → before f z x → False := fun z hz hne hb => by
    have := before_lt h hz hx hne hb
    have := hfirst z hz hne
    omega
  unfold clauseLbl
  split
  · next hlt =>
    -- the first leg starts or passes through: its own pocket covers the gap
    have hgt := ov_strict h _ ax.1 (ot f x) (ot f x + 1) (by omega) hlt
    rw [hx.2.2] at hgt
    apply gap_eq h ax.1 hx.2.1 hlt (Nat.le_of_eq hx.2.2) (by omega)
    intro j' hj' hs' hp' hne
    have c := chain h ax.1 hj' (Ne.symm hne) (by rw [hx.2.1, hs']) (show v < v + 1 by omega)
      ⟨ot f x, hlt, Nat.le_of_eq hx.2.2, by omega⟩ hp'
    rcases c with c | c
    · exact c
    · exfalso
      have c0 := c
      obtain ⟨_, ⟨t1, ht1, c1, c2⟩, _⟩ := c
      obtain ⟨t', ht', d1, d2⟩ := hp'
      have l1 := lo_le_ov h j' t' hj' (by omega)
      have l2 := ov_le_hi h j' (t' + 1) hj' ht'
      have := pocket_unique h _ ax.1 (show v < v + 1 by omega) ht1 hlt (by omega) (by omega)
        (Nat.le_of_eq hx.2.2) (by omega)
      subst this
      rw [hx.2.2] at c1
      have hlo : lo f j' = v := by omega
      obtain ⟨hz, hzj, hzt⟩ := mk_at (s := s) (v := v) hj' (show 0 < kl f j' by
        have := h.len2 j' hj'; omega) hs' hlo
      apply contra _ hz (fun he => hne (by rw [← hzj, he]))
      unfold before
      rw [hzj, hzt]
      rcases Nat.eq_zero_or_pos (ot f x) with h0 | h0
      · left; exact ⟨rfl, h0, c0⟩
      · right; left; exact ⟨rfl, by omega⟩
  · next hge =>
    -- the first leg ends its clause: the gap lies in the region outside the clause
    have hL : ot f x + 1 = kl f (oj f x) := by omega
    have h0 : ot f x ≠ 0 := by omega
    obtain ⟨hhi, hlo⟩ := at_L h hx hL
    unfold gapR parent
    apply sel_label_congr
    · intro j' hj'
      constructor
      · rintro ⟨hs', t', ht', d1, d2⟩
        have hne : j' ≠ oj f x := by
          intro he; subst he
          have := ov_le_hi h _ (t' + 1) hj' ht'; omega
        refine ⟨by rw [hs', hx.2.1], ?_⟩
        have l1 := lo_le_ov h j' t' hj' (by omega)
        have l2 := ov_le_hi h j' (t' + 1) hj' ht'
        rcases h.lam _ _ ax.1 hj' (Ne.symm hne) (by rw [hx.2.1, hs']) with n | n | n
        · exact ⟨Ne.symm hne, n, fun ⟨n', _⟩ => by have := nest_lo_hi h ax.1 n'; omega⟩
        · exfalso; have := nest_lo_hi h ax.1 n; omega
        · exfalso
          unfold Disj at n
          rcases n with n | n
          · have hl : lo f j' = v := by omega
            obtain ⟨hz, hzj, hzt⟩ := mk_at (s := s) (v := v) hj'
              (show 0 < kl f j' by have := h.len2 j' hj'; omega) hs' hl
            apply contra _ hz (fun he => hne (by rw [← hzj, he]))
            unfold before; rw [hzj, hzt]; right; left; exact ⟨rfl, h0⟩
          · omega
      · rintro ⟨hs', hi'⟩
        refine ⟨by rw [hs', hx.2.1], ?_⟩
        have hi0 := hi'
        obtain ⟨hne, ⟨t2, ht2, c1, c2⟩, _⟩ := hi'
        refine ⟨t2, ht2, by omega, ?_⟩
        rcases Nat.lt_or_ge v (ov f j' (t2 + 1)) with d | d
        · omega
        · exfalso
          have heq : ov f j' (t2 + 1) = v := by omega
          obtain ⟨hz, hzj, hzt⟩ := mk_at (s := isTop f j') (v := v) hj' ht2 rfl heq
          rw [hs'.trans hx.2.1] at hz
          apply contra _ hz (fun he => hne (by rw [← hzj, he]))
          unfold before; rw [hzj, hzt]
          rcases Nat.lt_or_ge (t2 + 1 + 1) (kl f j') with d2 | d2
          · right; right; left; exact ⟨by omega, d2, hL, h0⟩
          · right; right; right; exact ⟨by omega, by omega, h0, hL, hi0⟩
    · intro j' hj' ⟨hs', t', ht', d1, d2⟩
      have hne : j' ≠ oj f x := by
        intro he; subst he
        have := ov_le_hi h _ (t' + 1) hj' ht'; omega
      have l2 := ov_le_hi h j' (t' + 1) hj' ht'
      rw [pidx_eq h hj' (show v < v + 1 by omega) ht' d1 d2]
      -- the pocket containing the clause is the pocket containing the gap
      rcases h.lam _ _ ax.1 hj' (Ne.symm hne) (by rw [hx.2.1, hs']) with n | n | n
      · obtain ⟨t2, ht2, c1, c2⟩ := n
        rw [pidx_eq h hj' (lo_lt_hi h _ ax.1) ht2 c1 c2]
        rcases Nat.lt_trichotomy t2 t' with e | e | e
        · exfalso
          have := ov_le h j' hj' (show t2 + 1 ≤ t' by omega) (by omega)
          have heq : ov f j' t' = v := by omega
          obtain ⟨hz, hzj, hzt⟩ := mk_at (s := s) (v := v) hj' (by omega) hs' heq
          apply contra _ hz (fun he => hne (by rw [← hzj, he]))
          unfold before; rw [hzj, hzt]
          right; right; left; exact ⟨by omega, ht', hL, h0⟩
        · exact e.symm
        · exfalso
          have := ov_le h j' hj' (show t' + 1 ≤ t2 by omega) (by omega)
          omega
      · exfalso; have := nest_lo_hi h ax.1 n; omega
      · exfalso
        unfold Disj at n
        rcases n with n | n
        · have l1 := lo_le_ov h j' t' hj' (by omega)
          have hl : lo f j' = v := by omega
          obtain ⟨hz, hzj, hzt⟩ := mk_at (s := s) (v := v) hj'
            (show 0 < kl f j' by have := h.len2 j' hj'; omega) hs' hl
          apply contra _ hz (fun he => hne (by rw [← hzj, he]))
          unfold before; rw [hzj, hzt]; right; left; exact ⟨rfl, h0⟩
        · omega


/-- An overlap of positive length with a pocket forces the pocket. -/
theorem pocket_of_overlap {j a b t t' : Nat} (hj : j < f.length) (hab : a < b)
    (ht : t + 1 < kl f j) (ht' : t' + 1 < kl f j)
    (h1 : ov f j t ≤ a) (h2 : b ≤ ov f j (t + 1)) (h1' : ov f j t' ≤ a) (h2' : b ≤ ov f j (t' + 1)) :
    t = t' := pocket_unique h j hj hab ht ht' h1 h2 h1' h2'

/-- **The leg before a leg at a vertex.** -/
theorem q1_pred {s : Bool} {v y x : Nat} (hy : At f s v y) (hx : At f s v x)
    (hyx : key f y < key f x)
    (hcons : ∀ z, At f s v z → z ≠ y → z ≠ x → key f y < key f z → key f z < key f x → False) :
    legLbl f y = clauseLbl f x := by
  have hne : y ≠ x := fun e => by subst e; omega
  have ay := at_occ h hy
  have ax := at_occ h hx
  have ky := h.len2 _ ay.1
  have kx := h.len2 _ ax.1
  have hb := lt_before h hy hx hne hyx
  have contra : ∀ z, At f s v z → z ≠ y → z ≠ x → before f y z → before f z x → False :=
    fun z hz h1 h2 b1 b2 => hcons z hz h1 h2 (before_lt h hy hz (Ne.symm h1) b1)
      (before_lt h hz hx h2 b2)
  have hside : isTop f (oj f x) = isTop f (oj f y) := by rw [hx.2.1, hy.2.1]
  unfold before at hb
  unfold legLbl clauseLbl
  rcases hb with ⟨ty, tx, hin⟩ | ⟨ty, tx⟩ | ⟨ty, my, lx, tx⟩ | ⟨ty, ly, tx, lx, hin⟩
  · -- two legs starting clauses
    simp only [ty, ite_true, tx, show 0 + 1 < kl f (oj f x) by omega]
    obtain ⟨ry1, ry2⟩ := at_R h hy ty
    obtain ⟨rx1, rx2⟩ := at_R h hx tx
    have hin0 := hin
    obtain ⟨hjne, ⟨t1, ht1, c1, c2⟩, _⟩ := hin
    have t10 : t1 = 0 := by
      rcases Nat.eq_zero_or_pos t1 with e | e
      · exact e
      · have := ov_strict h _ ax.1 0 t1 e (by omega); unfold lo at rx1; omega
    subst t10
    apply parent_eq h ay.1 ax.1 hside hin0 ht1 c1 c2
    intro j' hj' hs' hin' hne'
    have hin1 := hin'
    have hlt := lo_lt_hi h _ ay.1
    obtain ⟨_, ⟨t2, ht2, d1, d2⟩, _⟩ := hin'
    rcases chain h ax.1 hj' (Ne.symm hne') (by rw [hside, hs']) hlt ⟨0, ht1, c1, c2⟩
      ⟨t2, ht2, d1, d2⟩ with c | c
    · exact c
    · exfalso
      have c0 := c
      obtain ⟨_, ⟨t3, ht3, e1, e2⟩, _⟩ := c
      have l1 := lo_le_ov h j' t2 hj' (by omega)
      have l2 := ov_le_hi h j' (t2 + 1) hj' ht2
      have := pocket_of_overlap h ax.1 hlt ht3 ht1 (by omega) (by omega) c1 c2
      subst this
      have q1 : lo f j' = ov f j' 0 := rfl
      have q2 : lo f (oj f x) = ov f (oj f x) 0 := rfl
      have hl : lo f j' = v := by omega
      obtain ⟨hz, hzj, hzt⟩ := mk_at (s := s) (v := v) hj' (by omega) (by rw [hs', hy.2.1]) hl
      apply contra _ hz (fun e => by rw [e] at hzj; exact hin1.1 hzj)
        (fun e => by rw [e] at hzj; exact hne' hzj.symm)
      · unfold before; rw [hzj, hzt]; left; exact ⟨ty, rfl, hin1⟩
      · unfold before; rw [hzj, hzt]; left; exact ⟨rfl, tx, c0⟩
  · rcases Nat.lt_or_ge (ot f x + 1) (kl f (oj f x)) with mx | lx
    · -- a starting leg before the passing leg
      simp only [ty, ite_true, mx]
      obtain ⟨ry1, ry2⟩ := at_R h hy ty
      obtain ⟨mx1, mx2⟩ := at_M h hx tx mx
      have hjne : oj f y ≠ oj f x := fun e => by rw [e] at ry1; omega
      have n : NestIn f (oj f y) (oj f x) := by
        rcases h.lam _ _ ay.1 ax.1 hjne hside.symm with n | n | n
        · exact n
        · have := nest_lo_hi h ay.1 n; omega
        · unfold Disj at n; omega
      have hin : ins f (oj f y) (oj f x) :=
        ⟨hjne, n, fun ⟨n', _⟩ => by have := nest_lo_hi h ay.1 n'; omega⟩
      obtain ⟨t1, ht1, c1, c2⟩ := n
      have hpos := ov_strict h _ ax.1 (ot f x) (ot f x + 1) (by omega) mx
      have t1e : t1 = ot f x := by
        rcases Nat.lt_trichotomy t1 (ot f x) with e | e | e
        · have := ov_le h _ ax.1 (show t1 + 1 ≤ ot f x by omega) ax.2
          rw [hx.2.2] at this; omega
        · exact e
        · have := ov_strict h _ ax.1 (ot f x) t1 e (by omega)
          rw [hx.2.2] at this; omega
      subst t1e
      apply parent_eq h ay.1 ax.1 hside hin ht1 c1 c2
      intro j' hj' hs' hin' hne'
      have hin1 := hin'
      have hlt := lo_lt_hi h _ ay.1
      obtain ⟨_, ⟨t2, ht2, d1, d2⟩, _⟩ := hin'
      rcases chain h ax.1 hj' (Ne.symm hne') (by rw [hside, hs']) hlt ⟨_, ht1, c1, c2⟩
        ⟨t2, ht2, d1, d2⟩ with c | c
      · exact c
      · exfalso
        obtain ⟨_, ⟨t3, ht3, e1, e2⟩, _⟩ := c
        have l1 := lo_le_ov h j' t2 hj' (by omega)
        have l2 := ov_le_hi h j' (t2 + 1) hj' ht2
        have := pocket_of_overlap h ax.1 hlt ht3 ht1 (by omega) (by omega) c1 c2
        subst this
        rw [hx.2.2] at e1
        have q1 : lo f j' = ov f j' 0 := rfl
        have hl : lo f j' = v := by omega
        obtain ⟨hz, hzj, hzt⟩ := mk_at (s := s) (v := v) hj' (by omega) (by rw [hs', hy.2.1]) hl
        apply contra _ hz (fun e => by rw [e] at hzj; exact hin1.1 hzj)
          (fun e => by rw [e] at hzj; exact hne' hzj.symm)
        · unfold before; rw [hzj, hzt]; left; exact ⟨ty, rfl, hin1⟩
        · unfold before; rw [hzj, hzt]; right; left; exact ⟨rfl, tx⟩
    · -- a starting leg before an ending leg: both clauses have the same surroundings
      have lx' : ot f x + 1 = kl f (oj f x) := by have := ax.2; omega
      simp only [ty, ite_true, show ¬ (ot f x + 1 < kl f (oj f x)) by omega, ite_false]
      obtain ⟨ry1, ry2⟩ := at_R h hy ty
      obtain ⟨lx1, lx2⟩ := at_L h hx lx'
      unfold parent
      apply sel_label_congr
      · intro j' hj'
        constructor
        · rintro ⟨hs', hin'⟩
          refine ⟨by rw [hs', hside], ?_⟩
          have hin1 := hin'
          obtain ⟨hne', ⟨p, hp, d1, d2⟩, _⟩ := hin'
          have l1 := lo_le_ov h j' p hj' (by omega)
          have l2 := ov_le_hi h j' (p + 1) hj' hp
          have ha : ov f j' p < v := by
            rcases Nat.lt_or_ge (ov f j' p) v with e | e
            · exact e
            · exfalso
              have heq : ov f j' p = v := by omega
              obtain ⟨hz, hzj, hzt⟩ := mk_at (s := s) (v := v) hj' (by omega)
                (by rw [hs', hy.2.1]) heq
              apply contra _ hz (fun e => by rw [e] at hzj; exact hne' hzj)
                (fun e => by rw [e] at hzj; rw [hzj] at lx1; omega)
              · unfold before; rw [hzj, hzt]
                rcases Nat.eq_zero_or_pos p with p0 | p0
                · left; exact ⟨ty, p0, hin1⟩
                · right; left; exact ⟨ty, by omega⟩
              · unfold before; rw [hzj, hzt]
                rcases Nat.eq_zero_or_pos p with p0 | p0
                · right; left; exact ⟨p0, tx⟩
                · right; right; left; exact ⟨by omega, hp, lx', tx⟩
          have hjx : j' ≠ oj f x := fun e => by subst e; omega
          rcases h.lam _ _ ax.1 hj' (Ne.symm hjx) (by rw [hside, hs']) with n | n | n
          · exact ⟨Ne.symm hjx, n, fun ⟨n', _⟩ => by have := nest_lo_hi h ax.1 n'; omega⟩
          · exfalso; have := nest_lo_hi h ax.1 n; omega
          · exfalso; unfold Disj at n; omega
        · rintro ⟨hs', hin'⟩
          refine ⟨by rw [hs', hside], ?_⟩
          have hin0 := hin'
          obtain ⟨hne', ⟨q, hq, d1, d2⟩, _⟩ := hin'
          have l1 := lo_le_ov h j' q hj' (by omega)
          have l2 := ov_le_hi h j' (q + 1) hj' hq
          have hb : v < ov f j' (q + 1) := by
            rcases Nat.lt_or_ge v (ov f j' (q + 1)) with e | e
            · exact e
            · exfalso
              have heq : ov f j' (q + 1) = v := by omega
              obtain ⟨hz, hzj, hzt⟩ := mk_at (s := s) (v := v) hj' hq
                (by rw [hs', hx.2.1]) heq
              apply contra _ hz (fun e => by rw [e] at hzj; rw [hzj] at ry1; omega)
                (fun e => by rw [e] at hzj; exact hne' hzj)
              · unfold before; rw [hzj, hzt]; right; left; exact ⟨ty, by omega⟩
              · unfold before; rw [hzj, hzt]
                rcases Nat.lt_or_ge (q + 1 + 1) (kl f j') with e2 | e2
                · right; right; left; exact ⟨by omega, e2, lx', tx⟩
                · right; right; right; exact ⟨by omega, by omega, tx, lx', hin0⟩
          have hjy : j' ≠ oj f y := fun e => by subst e; omega
          rcases h.lam _ _ ay.1 hj' (Ne.symm hjy) (by rw [hs', hside]) with n | n | n
          · exact ⟨Ne.symm hjy, n, fun ⟨n', _⟩ => by have := nest_lo_hi h ay.1 n'; omega⟩
          · exfalso; have := nest_lo_hi h ay.1 n; omega
          · exfalso; unfold Disj at n; omega
      · rintro j' hj' ⟨hs', hin'⟩
        have hin2 := hin'
        obtain ⟨hne', ⟨p, hp, d1, d2⟩, _⟩ := hin'
        have l1 := lo_le_ov h j' p hj' (by omega)
        have l2 := ov_le_hi h j' (p + 1) hj' hp
        rw [pidx_eq h hj' (lo_lt_hi h _ ay.1) hp d1 d2]
        -- the left end of the pocket lies left of the vertex (as in the first direction)
        have ha : ov f j' p < v := by
          rcases Nat.lt_or_ge (ov f j' p) v with e | e
          · exact e
          · exfalso
            have heq : ov f j' p = v := by omega
            obtain ⟨hz, hzj, hzt⟩ := mk_at (s := s) (v := v) hj' (by omega)
              (by rw [hs', hy.2.1]) heq
            have hin1 := hin2
            apply contra _ hz (fun e => by rw [e] at hzj; exact hne' hzj)
              (fun e => by rw [e] at hzj; rw [hzj] at lx1; omega)
            · unfold before; rw [hzj, hzt]
              rcases Nat.eq_zero_or_pos p with p0 | p0
              · left; exact ⟨ty, p0, hin1⟩
              · right; left; exact ⟨ty, by omega⟩
            · unfold before; rw [hzj, hzt]
              rcases Nat.eq_zero_or_pos p with p0 | p0
              · right; left; exact ⟨p0, tx⟩
              · right; right; left; exact ⟨by omega, hp, lx', tx⟩
        have hjx : j' ≠ oj f x := fun e => by subst e; omega
        rcases h.lam _ _ ax.1 hj' (Ne.symm hjx) (by rw [hside, hs']) with n | n | n
        · obtain ⟨q, hq, e1, e2⟩ := n
          rw [pidx_eq h hj' (lo_lt_hi h _ ax.1) hq e1 e2]
          exact pocket_of_overlap h hj' (show max (ov f j' p) (lo f (oj f x)) < v by omega)
            hp hq (by omega) (by omega) (by omega) (by omega)
        · exfalso; have := nest_lo_hi h ax.1 n; omega
        · exfalso; unfold Disj at n; omega
  · -- the passing leg before an ending leg
    simp only [ty, ite_false, show ¬ (ot f x + 1 < kl f (oj f x)) by omega]
    obtain ⟨my1, my2⟩ := at_M h hy ty my
    obtain ⟨lx1, lx2⟩ := at_L h hx lx
    have hjne : oj f x ≠ oj f y := fun e => by rw [e] at lx1; omega
    have n : NestIn f (oj f x) (oj f y) := by
      rcases h.lam _ _ ax.1 ay.1 hjne hside with n | n | n
      · exact n
      · have := nest_lo_hi h ax.1 n; omega
      · unfold Disj at n; omega
    have hin : ins f (oj f x) (oj f y) :=
      ⟨hjne, n, fun ⟨n', _⟩ => by have := nest_lo_hi h ax.1 n'; omega⟩
    obtain ⟨t1, ht1, c1, c2⟩ := n
    have t1e : t1 = ot f y - 1 := by
      have a1 : t1 < ot f y := by
        rcases Nat.lt_or_ge t1 (ot f y) with e | e
        · exact e
        · have := ov_le h _ ay.1 e (by omega); rw [hy.2.2] at this; omega
      have a2 : ot f y ≤ t1 + 1 := by
        rcases Nat.lt_or_ge (t1 + 1) (ot f y) with e | e
        · have := ov_strict h _ ay.1 (t1 + 1) (ot f y) e ay.2; rw [hy.2.2] at this; omega
        · exact e
      omega
    subst t1e
    symm
    apply parent_eq h ax.1 ay.1 hside.symm hin ht1 c1 c2
    intro j' hj' hs' hin' hne'
    have hin1 := hin'
    have hlt := lo_lt_hi h _ ax.1
    obtain ⟨_, ⟨t2, ht2, d1, d2⟩, _⟩ := hin'
    rcases chain h ay.1 hj' (Ne.symm hne') (by rw [← hside, hs']) hlt ⟨_, ht1, c1, c2⟩
      ⟨t2, ht2, d1, d2⟩ with c | c
    · exact c
    · exfalso
      have c0 := c
      obtain ⟨_, ⟨t3, ht3, e1, e2⟩, _⟩ := c
      have l1 := lo_le_ov h j' t2 hj' (by omega)
      have l2 := ov_le_hi h j' (t2 + 1) hj' ht2
      have := pocket_of_overlap h ay.1 hlt ht3 ht1 (by omega) (by omega) c1 c2
      subst this
      rw [show ot f y - 1 + 1 = ot f y by omega, hy.2.2] at e2
      have hh : hi f j' = v := by omega
      have k' := h.len2 j' hj'
      obtain ⟨hz, hzj, hzt⟩ := mk_at (s := s) (v := v) hj' (show kl f j' - 1 < kl f j' by omega)
        (by rw [hs', hx.2.1]) hh
      apply contra _ hz (fun e => by rw [e] at hzj; exact hne' hzj.symm)
        (fun e => by rw [e] at hzj; exact hin1.1 hzj)
      · unfold before; rw [hzj, hzt]; right; right; left; exact ⟨ty, my, by omega, by omega⟩
      · unfold before; rw [hzj, hzt]; right; right; right; exact ⟨by omega, by omega, tx, lx, hin1⟩
  · -- two legs ending clauses
    simp only [ty, ite_false, show ¬ (ot f x + 1 < kl f (oj f x)) by omega]
    obtain ⟨ly1, ly2⟩ := at_L h hy ly
    obtain ⟨lx1, lx2⟩ := at_L h hx lx
    have hin0 := hin
    obtain ⟨hjne, ⟨t1, ht1, c1, c2⟩, _⟩ := hin
    have t1e : t1 = ot f y - 1 := by
      have := ov_le_hi h _ (t1 + 1) ay.1 ht1
      rcases Nat.lt_or_ge (t1 + 1) (kl f (oj f y) - 1) with e | e
      · have := ov_strict h _ ay.1 (t1 + 1) (kl f (oj f y) - 1) e (by omega)
        have e1 : hi f (oj f y) = ov f (oj f y) (kl f (oj f y) - 1) := rfl
        omega
      · omega
    subst t1e
    symm
    apply parent_eq h ax.1 ay.1 hside.symm hin0 ht1 c1 c2
    intro j' hj' hs' hin' hne'
    have hin1 := hin'
    have hlt := lo_lt_hi h _ ax.1
    obtain ⟨_, ⟨t2, ht2, d1, d2⟩, _⟩ := hin'
    rcases chain h ay.1 hj' (Ne.symm hne') (by rw [← hside, hs']) hlt ⟨_, ht1, c1, c2⟩
      ⟨t2, ht2, d1, d2⟩ with c | c
    · exact c
    · exfalso
      have c0 := c
      obtain ⟨_, ⟨t3, ht3, e1, e2⟩, _⟩ := c
      have l1 := lo_le_ov h j' t2 hj' (by omega)
      have l2 := ov_le_hi h j' (t2 + 1) hj' ht2
      have := pocket_of_overlap h ay.1 hlt ht3 ht1 (by omega) (by omega) c1 c2
      subst this
      rw [show ot f y - 1 + 1 = ot f y by omega, hy.2.2] at e2
      have hh : hi f j' = v := by omega
      have k' := h.len2 j' hj'
      obtain ⟨hz, hzj, hzt⟩ := mk_at (s := s) (v := v) hj' (show kl f j' - 1 < kl f j' by omega)
        (by rw [hs', hx.2.1]) hh
      apply contra _ hz (fun e => by rw [e] at hzj; exact hne' hzj.symm)
        (fun e => by rw [e] at hzj; exact hin1.1 hzj)
      · unfold before; rw [hzj, hzt]; right; right; right; exact ⟨ty, ly, by omega, by omega, c0⟩
      · unfold before; rw [hzj, hzt]; right; right; right; exact ⟨by omega, by omega, tx, lx, hin1⟩


/-- **Across an empty vertex** the gap regions agree. -/
theorem q2_empty {s : Bool} {u : Nat} (hno : ∀ z, ¬ At f s (u + 1) z) :
    gapR f s (u + 1) = gapR f s u := by
  unfold gapR
  have noleg : ∀ j' t, j' < f.length → t < kl f j' → isTop f j' = s → ov f j' t ≠ u + 1 :=
    fun j' t hj' ht hs heq => hno _ (mk_at hj' ht hs heq).1
  apply sel_label_congr
  · intro j' hj'
    constructor
    · rintro ⟨hs, t, ht, c1, c2⟩
      have := noleg j' t hj' (by omega) hs
      exact ⟨hs, t, ht, by omega, by omega⟩
    · rintro ⟨hs, t, ht, c1, c2⟩
      have := noleg j' (t + 1) hj' ht hs
      exact ⟨hs, t, ht, by omega, by omega⟩
  · rintro j' hj' ⟨hs, t, ht, c1, c2⟩
    have := noleg j' t hj' (by omega) hs
    rw [pidx_eq h hj' (by omega) ht c1 c2, pidx_eq h hj' (by omega) ht (by omega) (by omega)]

/-- **The last leg at a vertex** bounds the gap before it. -/
theorem q2_last {s : Bool} {u y : Nat} (hy : At f s (u + 1) y)
    (hlast : ∀ z, At f s (u + 1) z → z ≠ y → key f z < key f y) :
    legLbl f y = gapR f s u := by
  have ay := at_occ h hy
  have ky := h.len2 _ ay.1
  have contra : ∀ z, At f s (u + 1) z → z ≠ y → before f y z → False := fun z hz hne hb => by
    have := before_lt h hy hz (Ne.symm hne) hb
    have := hlast z hz hne
    omega
  unfold legLbl
  split
  · next ty =>
    obtain ⟨ry1, ry2⟩ := at_R h hy ty
    unfold parent gapR
    apply sel_label_congr
    · intro j' hj'
      constructor
      · rintro ⟨hs, hin⟩
        have hin1 := hin
        obtain ⟨hne, ⟨p, hp, c1, c2⟩, _⟩ := hin
        refine ⟨by rw [hs, hy.2.1], p, hp, ?_, by omega⟩
        have l1 := lo_le_ov h j' p hj' (by omega)
        rcases Nat.lt_or_ge (ov f j' p) (u + 1) with e | e
        · omega
        · exfalso
          obtain ⟨hz, hzj, hzt⟩ := mk_at (s := s) (v := u + 1) (t := p) hj' (by omega)
            (by rw [hs, hy.2.1]) (by omega)
          apply contra _ hz (fun e => by rw [e] at hzj; exact hne hzj)
          unfold before; rw [hzj, hzt]
          rcases Nat.eq_zero_or_pos p with p0 | p0
          · left; exact ⟨ty, p0, hin1⟩
          · right; left; exact ⟨ty, by omega⟩
      · rintro ⟨hs, t, ht, c1, c2⟩
        refine ⟨by rw [hs, hy.2.1], ?_⟩
        have l1 := lo_le_ov h j' t hj' (by omega)
        have l2 := ov_le_hi h j' (t + 1) hj' ht
        have hne : oj f y ≠ j' := fun e => by subst e; omega
        have hb : u + 2 ≤ ov f j' (t + 1) := by
          rcases Nat.lt_or_ge (u + 1) (ov f j' (t + 1)) with e | e
          · omega
          · exfalso
            obtain ⟨hz, hzj, hzt⟩ := mk_at (s := s) (v := u + 1) hj' ht
              (by rw [hs]) (by omega)
            apply contra _ hz (fun e => by rw [e] at hzj; exact hne hzj)
            unfold before; rw [hzj, hzt]; right; left; exact ⟨ty, by omega⟩
        rcases h.lam _ _ ay.1 hj' hne (by rw [hy.2.1, hs]) with n | n | n
        · exact ⟨hne, n, fun ⟨n', _⟩ => by have := nest_lo_hi h ay.1 n'; omega⟩
        · exfalso; have := nest_lo_hi h ay.1 n; omega
        · exfalso; unfold Disj at n; omega
    · rintro j' hj' ⟨hs, hin⟩
      have hin1 := hin
      obtain ⟨hne, ⟨p, hp, c1, c2⟩, _⟩ := hin
      have l1 := lo_le_ov h j' p hj' (by omega)
      have hp0 : ov f j' p ≤ u := by
        rcases Nat.lt_or_ge (ov f j' p) (u + 1) with e | e
        · omega
        · exfalso
          obtain ⟨hz, hzj, hzt⟩ := mk_at (s := s) (v := u + 1) (t := p) hj' (by omega)
            (by rw [hs, hy.2.1]) (by omega)
          apply contra _ hz (fun e => by rw [e] at hzj; exact hne hzj)
          unfold before; rw [hzj, hzt]
          rcases Nat.eq_zero_or_pos p with p0 | p0
          · left; exact ⟨ty, p0, hin1⟩
          · right; left; exact ⟨ty, by omega⟩
      rw [pidx_eq h hj' (lo_lt_hi h _ ay.1) hp c1 c2, pidx_eq h hj' (by omega) hp hp0 (by omega)]
  · next ty =>
    have hlt := ov_strict h _ ay.1 (ot f y - 1) (ot f y) (by omega) ay.2
    rw [hy.2.2] at hlt
    symm
    apply gap_eq h ay.1 hy.2.1 (by omega) (by omega)
      (by rw [show ot f y - 1 + 1 = ot f y by omega, hy.2.2]; exact Nat.le_refl _)
    intro j' hj' hs hp hne
    rcases chain h ay.1 hj' (Ne.symm hne) (by rw [hy.2.1, hs]) (show u < u + 1 by omega)
      ⟨ot f y - 1, by omega, by omega, by rw [show ot f y - 1 + 1 = ot f y by omega, hy.2.2]; exact Nat.le_refl _⟩
      hp with c | c
    · exact c
    · exfalso
      have c0 := c
      obtain ⟨_, ⟨t3, ht3, e1, e2⟩, _⟩ := c
      obtain ⟨t', ht', d1, d2⟩ := hp
      have l1 := lo_le_ov h j' t' hj' (by omega)
      have l2 := ov_le_hi h j' (t' + 1) hj' ht'
      have := pocket_of_overlap h ay.1 (show u < u + 1 by omega) ht3 (show ot f y - 1 + 1 <
        kl f (oj f y) by omega) (by omega) (by omega) (by omega)
        (by rw [show ot f y - 1 + 1 = ot f y by omega, hy.2.2]; exact Nat.le_refl _)
      subst this
      rw [show ot f y - 1 + 1 = ot f y by omega, hy.2.2] at e2
      have hh : hi f j' = u + 1 := by omega
      have k' := h.len2 j' hj'
      obtain ⟨hz, hzj, hzt⟩ := mk_at (s := s) (v := u + 1) hj'
        (show kl f j' - 1 < kl f j' by omega) hs hh
      apply contra _ hz (fun e => by rw [e] at hzj; exact hne hzj.symm)
      unfold before; rw [hzj, hzt]
      rcases Nat.lt_or_ge (ot f y + 1) (kl f (oj f y)) with my | ly
      · right; right; left; exact ⟨ty, my, by omega, by omega⟩
      · right; right; right; exact ⟨ty, by omega, by omega, by omega, c0⟩

/-- No pocket reaches beyond the last spine position. -/
theorem gap_top {s : Bool} : gapR f s (nK f - 1) = 0 := by
  apply gap_out
  rintro j' hj' _ ⟨t, ht, c1, c2⟩
  have := ov_lt h j' (t + 1) hj' ht
  have := h.K3
  omega

theorem q2_empty0 {s : Bool} (hno : ∀ z, ¬ At f s 0 z) : gapR f s 0 = 0 := by
  apply gap_out
  rintro j' hj' hs ⟨t, ht, c1, c2⟩
  exact hno _ (mk_at hj' (show t < kl f j' by omega) hs (by omega)).1

theorem q2_last0 {s : Bool} {y : Nat} (hy : At f s 0 y)
    (hlast : ∀ z, At f s 0 z → z ≠ y → key f z < key f y) : legLbl f y = 0 := by
  have ay := at_occ h hy
  have ty : ot f y = 0 := by
    apply Classical.byContradiction
    intro h0
    have := ov_strict h _ ay.1 0 (ot f y) (by omega) ay.2
    rw [hy.2.2] at this; omega
  unfold legLbl
  simp only [ty, ite_true]
  apply parent_out
  intro j' hj' hs hin
  have hin1 := hin
  obtain ⟨hne, ⟨p, hp, c1, c2⟩, _⟩ := hin
  obtain ⟨ry1, _⟩ := at_R h hy ty
  have hz0 : ov f j' p = 0 := by omega
  obtain ⟨hz, hzj, hzt⟩ := mk_at (s := s) (v := 0) hj' (show p < kl f j' by omega)
    (by rw [hs, hy.2.1]) hz0
  have := hlast _ hz (fun e => by rw [e] at hzj; exact hne hzj)
  have hp0 : p = 0 := by
    apply Classical.byContradiction
    intro h0
    have := ov_strict h _ hj' 0 p (by omega) (by omega)
    omega
  have := before_lt h hy hz (fun e => by rw [← e] at hzj; exact hne hzj)
    (by unfold before; rw [hzj, hzt]; left; exact ⟨ty, hp0, hin1⟩)
  omega
end q
end Complexity.Planar.Comb
