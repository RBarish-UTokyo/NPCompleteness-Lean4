module

public import Complexity.Planar.CombFaces
public import Complexity.Planar.Rot
public import Complexity.Planar.EmbedCert
import Lean.Elab.Tactic.Omega

/-!
# The rotation system of a comb drawing

The half-edges of `incidenceGraph f ++ variableCycle f` are numbered as in `halfEdgeEnd`: for an
occurrence `e`, `2 e` is at the variable and `2 e + 1` at the clause; for the cycle edge `i`,
`2 (M + i)` is at variable `i` and `2 (M + i) + 1` at the next variable.  At a variable `v` the
counterclockwise rotation is: the spine dart towards `v + 1`, the top legs (in key order), the
spine dart towards `v - 1`, the bottom legs.  At a clause the rotation follows its literals.
-/

@[expose] public section

-- Section hypotheses stay in the signatures of lemmas that do not use them, so that all
-- lemmas of a section take the same arguments.
set_option linter.unusedSectionVars false

namespace Complexity.Planar.Comb

open SAT

section groups

variable (f : CNF)

/-- The legs at oriented position `v` on side `s`, in counterclockwise order. -/
def group (s : Bool) (v : Nat) : List Nat :=
  ((List.range (nM f)).filter
    (fun e => decide (e < nM f ∧ isTop f (oj f e) = s ∧ ov f (oj f e) (ot f e) = v))).mergeSort
    (fun a b => decide (key f a ≤ key f b))

variable {f}

theorem mem_group {s : Bool} {v e : Nat} : e ∈ group f s v ↔ At f s v e := by
  unfold group
  rw [List.mem_mergeSort, List.mem_filter, List.mem_range, decide_eq_true_iff]
  exact ⟨fun h => h.2, fun h => ⟨h.1, h⟩⟩

theorem group_nodup {s : Bool} {v : Nat} : (group f s v).Nodup := by
  unfold group
  exact (List.mergeSort_perm _ _).nodup_iff.mpr (List.nodup_range.filter _)

theorem group_sorted (h : CombOK f) {s : Bool} {v : Nat} :
    (group f s v).Pairwise (fun a b => key f a < key f b) := by
  have hs : (group f s v).Pairwise (fun a b => decide (key f a ≤ key f b) = true) := by
    unfold group
    apply List.pairwise_mergeSort
    · intro a b c h1 h2
      simp only [decide_eq_true_eq] at h1 h2 ⊢; omega
    · intro a b
      simp only [Bool.or_eq_true, decide_eq_true_eq]; omega
  have hn := (group_nodup (f := f) (s := s) (v := v))
  have hboth := hs.and hn
  apply hboth.imp_of_mem
  intro a b ha hb ⟨h1, h2⟩
  simp only [decide_eq_true_eq] at h1
  have := key_ne h (mem_group.mp ha) (mem_group.mp hb) h2
  omega

theorem group_first (h : CombOK f) {s : Bool} {v : Nat} (hp : 0 < (group f s v).length)
    {z : Nat} (hz : At f s v z) (hne : z ≠ (group f s v)[0]) :
    key f (group f s v)[0] < key f z := by
  obtain ⟨r, hr, rfl⟩ := mem_getElem (mem_group.mpr hz)
  have hr0 : r ≠ 0 := fun e => by subst e; exact hne rfl
  exact List.pairwise_iff_getElem.mp (group_sorted h) 0 r hp hr (by omega)

theorem group_last (h : CombOK f) {s : Bool} {v : Nat} (hp : 0 < (group f s v).length)
    {z : Nat} (hz : At f s v z) (hne : z ≠ (group f s v)[(group f s v).length - 1]) :
    key f z < key f (group f s v)[(group f s v).length - 1] := by
  obtain ⟨r, hr, rfl⟩ := mem_getElem (mem_group.mpr hz)
  have hr0 : r ≠ (group f s v).length - 1 := fun e => by subst e; exact hne rfl
  exact List.pairwise_iff_getElem.mp (group_sorted h) r _ hr (by omega) (by omega)

theorem group_consec (h : CombOK f) {s : Bool} {v p : Nat} (hp : p < (group f s v).length)
    (hp0 : 0 < p) :
    key f (group f s v)[p - 1] < key f (group f s v)[p] ∧
      ∀ z, At f s v z → z ≠ (group f s v)[p - 1] → z ≠ (group f s v)[p] →
        key f (group f s v)[p - 1] < key f z → key f z < key f (group f s v)[p] → False := by
  have hsort := List.pairwise_iff_getElem.mp (group_sorted (s := s) (v := v) h)
  refine ⟨hsort (p - 1) p (by omega) hp (by omega), ?_⟩
  intro z hz h1 h2 k1 k2
  obtain ⟨r, hr, rfl⟩ := mem_getElem (mem_group.mpr hz)
  rcases Nat.lt_trichotomy r (p - 1) with c | c | c
  · have := hsort r (p - 1) hr (by omega) c; omega
  · subst c; exact h1 rfl
  · rcases Nat.lt_trichotomy r p with d | d | d
    · omega
    · subst d; exact h2 rfl
    · have := hsort p r hp hr d; omega

end groups

/-! ## Darts -/

section darts

variable (f : CNF)

/-- The spine vertex of a dart that is not at a clause. -/
def vtx (d : Nat) : Nat :=
  if d < 2 * nM f then vr f (oj f (d / 2)) (ot f (d / 2))
  else if d % 2 = 0 then d / 2 - nM f else (d / 2 - nM f + 1) % nK f

/-- The dart is at a clause. -/
def isCl (d : Nat) : Prop := d < 2 * nM f ∧ d % 2 = 1

/-- The spine darts at `v` towards `v + 1` and towards `v - 1`. -/
def spE (v : Nat) : Nat := 2 * (nM f + v)
def spW (v : Nat) : Nat := 2 * (nM f + (v + nK f - 1) % nK f) + 1

/-- The leg darts at oriented position `v` on side `s`. -/
def legs (s : Bool) (v : Nat) : List Nat := (group f s v).map (2 * ·)

/-- The rotation at the spine vertex `v`. -/
def rot (v : Nat) : List Nat :=
  [spE f v] ++ legs f true v ++ [spW f v] ++ legs f false (nK f - 1 - v)

/-- The rotation at clause vertices. -/
def clNext (d : Nat) : Nat :=
  2 * (off f (oj f (d / 2)) + (ot f (d / 2) + 1) % kl f (oj f (d / 2))) + 1
def clPrev (d : Nat) : Nat :=
  2 * (off f (oj f (d / 2)) + (ot f (d / 2) + kl f (oj f (d / 2)) - 1) % kl f (oj f (d / 2))) + 1

open Classical in
/-- The node permutation and its inverse. -/
noncomputable def nxt (d : Nat) : Nat := if isCl f d then clNext f d else rnext (rot f (vtx f d)) d
open Classical in
noncomputable def prv (d : Nat) : Nat := if isCl f d then clPrev f d else rprev (rot f (vtx f d)) d

open Classical in
/-- The end of a dart. -/
noncomputable def endOf (d : Nat) : Sum Nat Nat :=
  if isCl f d then .inr (oj f (d / 2)) else .inl (vtx f d)

end darts

section dartlemmas

variable {f : CNF} (h : CombOK f)
include h

theorem K_pos : 0 < nK f := by have := h.K3; omega

omit h in
theorem legs_mem {s : Bool} {v x : Nat} : x ∈ legs f s v ↔ ∃ e, At f s v e ∧ x = 2 * e := by
  unfold legs
  rw [List.mem_map]
  constructor
  · rintro ⟨e, he, rfl⟩; exact ⟨e, mem_group.mp he, rfl⟩
  · rintro ⟨e, he, rfl⟩; exact ⟨e, mem_group.mpr he, rfl⟩

omit h in
theorem opos_inj {s : Bool} {a b : Nat} (ha : a < nK f) (hb : b < nK f)
    (he : opos f s a = opos f s b) : a = b := by
  unfold opos at he; split at he <;> omega

omit h in
theorem vtx_leg {e : Nat} (he : e < nM f) : vtx f (2 * e) = vr f (oj f e) (ot f e) := by
  unfold vtx; simp [show 2 * e < 2 * nM f by omega]

/-- Leg darts lie in the rotation of their variable. -/
theorem leg_in_rot {e : Nat} (he : e < nM f) :
    2 * e ∈ rot f (vtx f (2 * e)) ∧ vtx f (2 * e) < nK f := by
  obtain ⟨hj, ht, _⟩ := occ_spec f e he
  rw [vtx_leg he]
  refine ⟨?_, vr_lt _ _ hj ht⟩
  unfold rot
  simp only [List.mem_append, List.mem_singleton, legs_mem]
  cases hs : isTop f (oj f e)
  · right
    refine ⟨e, ⟨he, hs, ?_⟩, rfl⟩
    unfold ov opos; rw [hs]; rfl
  · left; left; right
    refine ⟨e, ⟨he, hs, ?_⟩, rfl⟩
    unfold ov opos; rw [hs]; rfl

/-- Elements of a rotation are darts at its vertex. -/
theorem rot_mem {v x : Nat} (hv : v < nK f) (hx : x ∈ rot f v) :
    x < 2 * (nM f + nK f) ∧ ¬ isCl f x ∧ vtx f x = v := by
  have hK := K_pos h
  unfold rot at hx
  simp only [List.mem_append, List.mem_singleton, legs_mem] at hx
  rcases hx with ((rfl | ⟨e, he, rfl⟩) | rfl) | ⟨e, he, rfl⟩
  · refine ⟨by unfold spE; omega, fun hc => by unfold isCl spE at hc; omega, ?_⟩
    unfold vtx spE
    simp [show ¬ 2 * (nM f + v) < 2 * nM f by omega]
  · obtain ⟨hj, ht, _⟩ := occ_spec f e he.1
    have he1 := he.1
    refine ⟨by omega, fun hc => by unfold isCl at hc; omega, ?_⟩
    rw [vtx_leg he.1]
    have := he.2.2
    unfold ov at this
    rw [he.2.1] at this
    unfold opos at this; simpa using this
  · refine ⟨by unfold spW; have := Nat.mod_lt (v + nK f - 1) hK; omega,
      fun hc => by unfold isCl spW at hc; omega, ?_⟩
    unfold vtx spW
    have hm := Nat.mod_lt (v + nK f - 1) hK
    simp only [show ¬ 2 * (nM f + (v + nK f - 1) % nK f) + 1 < 2 * nM f by omega, ite_false]
    rw [ite_eq_right (by omega), show (2 * (nM f + (v + nK f - 1) % nK f) + 1) / 2 - nM f =
      (v + nK f - 1) % nK f by omega]
    rcases Nat.eq_zero_or_pos v with h0 | h0
    · subst h0
      rw [Nat.zero_add, Nat.mod_eq_of_lt (show nK f - 1 < nK f by omega),
        Nat.sub_add_cancel (show 1 ≤ nK f by omega), Nat.mod_self]
    · rw [show v + nK f - 1 = (v - 1) + nK f by omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt (show v - 1 < nK f by omega), Nat.sub_add_cancel h0, Nat.mod_eq_of_lt hv]
  · obtain ⟨hj, ht, _⟩ := occ_spec f e he.1
    have he1 := he.1
    refine ⟨by omega, fun hc => by unfold isCl at hc; omega, ?_⟩
    rw [vtx_leg he.1]
    have := he.2.2
    unfold ov at this
    rw [he.2.1] at this
    unfold opos at this
    simp only [Bool.false_eq_true, ite_false] at this
    have := vr_lt _ _ hj ht
    omega

/-- Spine darts lie in the rotation of their vertex. -/
theorem spine_in_rot {d : Nat} (hd1 : 2 * nM f ≤ d) (hd2 : d < 2 * (nM f + nK f)) :
    d ∈ rot f (vtx f d) ∧ vtx f d < nK f := by
  have hK := K_pos h
  unfold rot
  simp only [List.mem_append, List.mem_singleton]
  rcases Nat.mod_two_eq_zero_or_one d with h2 | h2
  · have hv : vtx f d = d / 2 - nM f := by unfold vtx; simp [show ¬ d < 2 * nM f by omega, h2]
    rw [hv]
    refine ⟨Or.inl (Or.inl (Or.inl (by unfold spE; omega))), by omega⟩
    -- placeholder replaced below
  · have hv : vtx f d = (d / 2 - nM f + 1) % nK f := by
      unfold vtx; simp [show ¬ d < 2 * nM f by omega, h2]
    rw [hv]
    refine ⟨Or.inl (Or.inr (by
      unfold spW
      have hi : d / 2 - nM f < nK f := by omega
      rcases Nat.lt_or_ge (d / 2 - nM f + 1) (nK f) with c | c
      · rw [Nat.mod_eq_of_lt c, show d / 2 - nM f + 1 + nK f - 1 = (d / 2 - nM f) + nK f by omega,
          Nat.add_mod_right, Nat.mod_eq_of_lt hi]
        omega
      · rw [show d / 2 - nM f + 1 = nK f by omega, Nat.mod_self, Nat.zero_add,
          Nat.mod_eq_of_lt (show nK f - 1 < nK f by omega)]
        omega)), Nat.mod_lt _ hK⟩

theorem rot_nodup {v : Nat} : (rot f v).Nodup := by
  unfold rot
  have gl : ∀ s w, (legs f s w).Nodup := fun s w => by
    unfold legs
    exact List.Pairwise.map _ (fun a b (hab : a ≠ b) => by omega) group_nodup
  have lt : ∀ s w x, x ∈ legs f s w → x < 2 * nM f ∧ x % 2 = 0 := fun s w x hx => by
    obtain ⟨e, he, rfl⟩ := legs_mem.mp hx
    exact ⟨by have := he.1; omega, by omega⟩
  rw [List.nodup_append, List.nodup_append, List.nodup_append]
  refine ⟨⟨⟨List.pairwise_singleton _ _, gl _ _, ?_⟩, List.pairwise_singleton _ _, ?_⟩, gl _ _, ?_⟩
  · intro a ha b hb
    rw [List.mem_singleton] at ha
    subst ha
    have := lt _ _ _ hb; unfold spE; omega
  · intro a ha b hb
    rw [List.mem_singleton] at hb
    subst hb
    rw [List.mem_append, List.mem_singleton] at ha
    rcases ha with rfl | ha
    · unfold spE spW; omega
    · have := lt _ _ _ ha; unfold spW; omega
  · intro a ha b hb hab
    subst hab
    have := lt _ _ _ hb
    rw [List.mem_append, List.mem_append, List.mem_singleton, List.mem_singleton] at ha
    rcases ha with (rfl | ha) | rfl
    · unfold spE at this; omega
    · obtain ⟨e1, he1, rfl⟩ := legs_mem.mp ha
      obtain ⟨e2, he2, he⟩ := legs_mem.mp hb
      have : e1 = e2 := by omega
      subst this
      have c1 := he1.2.1
      have c2 := he2.2.1
      rw [c1] at c2
      exact absurd c2 (by simp)
    · unfold spW at this; omega

end dartlemmas


section dartlemmas2

variable {f : CNF} (h : CombOK f)
include h

/-- Darts not at clauses lie in the rotation of their vertex. -/
theorem in_rot {d : Nat} (hd : d < 2 * (nM f + nK f)) (hc : ¬ isCl f d) :
    d ∈ rot f (vtx f d) ∧ vtx f d < nK f := by
  rcases Nat.lt_or_ge d (2 * nM f) with h1 | h1
  · have h2 : d % 2 = 0 := by unfold isCl at hc; omega
    have := leg_in_rot h (e := d / 2) (by omega)
    rwa [show 2 * (d / 2) = d by omega] at this
  · exact spine_in_rot h h1 hd

omit h in
theorem cl_dart {d : Nat} (hc : isCl f d) :
    oj f (d / 2) < f.length ∧ ot f (d / 2) < kl f (oj f (d / 2)) ∧
      d = 2 * (off f (oj f (d / 2)) + ot f (d / 2)) + 1 := by
  obtain ⟨h1, h2⟩ := hc
  obtain ⟨a, b, c⟩ := occ_spec f (d / 2) (by omega)
  exact ⟨a, b, by omega⟩

omit h in
theorem clNext_eq {j t : Nat} (hj : j < f.length) (ht : t < kl f j) :
    clNext f (2 * (off f j + t) + 1) = 2 * (off f j + (t + 1) % kl f j) + 1 := by
  unfold clNext
  rw [show (2 * (off f j + t) + 1) / 2 = off f j + t by omega, (occ_eq f j t hj ht).1,
    (occ_eq f j t hj ht).2]

omit h in
theorem clPrev_eq {j t : Nat} (hj : j < f.length) (ht : t < kl f j) :
    clPrev f (2 * (off f j + t) + 1) = 2 * (off f j + (t + kl f j - 1) % kl f j) + 1 := by
  unfold clPrev
  rw [show (2 * (off f j + t) + 1) / 2 = off f j + t by omega, (occ_eq f j t hj ht).1,
    (occ_eq f j t hj ht).2]

omit h in
theorem isCl_clause {j t : Nat} (hj : j < f.length) (ht : t < kl f j) :
    isCl f (2 * (off f j + t) + 1) := ⟨by have := off_add_lt f j t hj ht; omega, by omega⟩

omit h in
theorem not_isCl_even {d : Nat} (he : d % 2 = 0) : ¬ isCl f d := fun hc => by
  unfold isCl at hc; omega

omit h in
theorem mod_succ_pred {k t : Nat} (hk : 0 < k) (ht : t < k) :
    ((t + k - 1) % k + 1) % k = t ∧ ((t + 1) % k + k - 1) % k = t := by
  constructor
  · rcases Nat.eq_zero_or_pos t with h0 | h0
    · subst h0
      rw [Nat.zero_add, Nat.mod_eq_of_lt (show k - 1 < k by omega),
        Nat.sub_add_cancel (show 1 ≤ k by omega), Nat.mod_self]
    · rw [show t + k - 1 = (t - 1) + k by omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt (show t - 1 < k by omega), Nat.sub_add_cancel h0, Nat.mod_eq_of_lt ht]
  · rcases Nat.lt_or_ge (t + 1) k with h1 | h1
    · rw [Nat.mod_eq_of_lt h1, show t + 1 + k - 1 = t + k by omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt ht]
    · rw [show t + 1 = k by omega, Nat.mod_self, Nat.zero_add,
        Nat.mod_eq_of_lt (show k - 1 < k by omega)]
      omega

theorem nxt_cl {j t : Nat} (hj : j < f.length) (ht : t < kl f j) :
    nxt f (2 * (off f j + t) + 1) = 2 * (off f j + (t + 1) % kl f j) + 1 := by
  unfold nxt
  rw [ite_eq_left (isCl_clause hj ht), clNext_eq hj ht]

theorem prv_cl {j t : Nat} (hj : j < f.length) (ht : t < kl f j) :
    prv f (2 * (off f j + t) + 1) = 2 * (off f j + (t + kl f j - 1) % kl f j) + 1 := by
  unfold prv
  rw [ite_eq_left (isCl_clause hj ht), clPrev_eq hj ht]

theorem nxt_rot {d : Nat} (hc : ¬ isCl f d) : nxt f d = rnext (rot f (vtx f d)) d := by
  unfold nxt; rw [ite_eq_right hc]

theorem prv_rot {d : Nat} (hc : ¬ isCl f d) : prv f d = rprev (rot f (vtx f d)) d := by
  unfold prv; rw [ite_eq_right hc]

/-- The node map and its inverse are inverse permutations of the darts. -/
theorem nxt_spec {d : Nat} (hd : d < 2 * (nM f + nK f)) :
    nxt f d < 2 * (nM f + nK f) ∧ prv f d < 2 * (nM f + nK f) ∧
      nxt f (prv f d) = d ∧ prv f (nxt f d) = d ∧ endOf f (nxt f d) = endOf f d := by
  by_cases hc : isCl f d
  · obtain ⟨hj, ht, hdd⟩ := cl_dart hc
    generalize oj f (d / 2) = j at hj ht hdd
    generalize ot f (d / 2) = t at ht hdd
    subst hdd
    have hk := h.len2 j hj
    have m1 := Nat.mod_lt (t + 1) (show 0 < kl f j by omega)
    have m2 := Nat.mod_lt (t + kl f j - 1) (show 0 < kl f j by omega)
    obtain ⟨q1, q2⟩ := mod_succ_pred (show 0 < kl f j by omega) ht
    rw [nxt_cl h hj ht, prv_cl h hj ht, nxt_cl h hj m2, prv_cl h hj m1, q1, q2]
    have a1 := off_add_lt f j _ hj m1
    have a2 := off_add_lt f j _ hj m2
    refine ⟨by omega, by omega, rfl, rfl, ?_⟩
    unfold endOf
    rw [ite_eq_left ⟨by omega, by omega⟩, ite_eq_left ⟨by have := off_add_lt f j t hj ht; omega, by omega⟩]
    rw [show (2 * (off f j + (t + 1) % kl f j) + 1) / 2 = off f j + (t + 1) % kl f j by omega,
      show (2 * (off f j + t) + 1) / 2 = off f j + t by omega, (occ_eq f j _ hj m1).1,
      (occ_eq f j t hj ht).1]
  · obtain ⟨hm, hv⟩ := in_rot h hd hc
    have hnd := rot_nodup h (v := vtx f d)
    have n1 := rnext_mem hnd hm
    have p1 := rprev_mem hnd hm
    obtain ⟨a1, b1, c1⟩ := rot_mem h hv n1
    obtain ⟨a2, b2, c2⟩ := rot_mem h hv p1
    rw [nxt_rot h hc, prv_rot h hc, nxt_rot h b2, prv_rot h b1, c1, c2, rnext_rprev hnd hm,
      rprev_rnext hnd hm]
    refine ⟨a1, a2, rfl, rfl, ?_⟩
    unfold endOf
    rw [ite_eq_right (fun hh => b1 hh), ite_eq_right (fun hh => hc hh), c1]

/-- Iterating the node map stays at the vertex. -/
theorem iterate_end {d : Nat} (hd : d < 2 * (nM f + nK f)) (k : Nat) :
    iterate (nxt f) k d < 2 * (nM f + nK f) ∧ endOf f (iterate (nxt f) k d) = endOf f d := by
  induction k generalizing d with
  | zero => exact ⟨hd, rfl⟩
  | succ k ih =>
    simp only [iterate]
    obtain ⟨a, _, _, _, b⟩ := nxt_spec h hd
    obtain ⟨c, e⟩ := ih a
    exact ⟨c, e.trans b⟩

theorem iterate_cl {j t : Nat} (hj : j < f.length) (ht : t < kl f j) (k : Nat) :
    iterate (nxt f) k (2 * (off f j + t) + 1) = 2 * (off f j + (t + k) % kl f j) + 1 := by
  induction k generalizing t with
  | zero => simp [iterate, Nat.mod_eq_of_lt ht]
  | succ k ih =>
    simp only [iterate]
    have hk := h.len2 j hj
    rw [nxt_cl h hj ht, ih (Nat.mod_lt _ (by omega))]
    congr 3
    rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod, Nat.add_assoc, Nat.add_comm 1 k]

theorem iterate_rot {v x : Nat} (hv : v < nK f) (hx : x ∈ rot f v) (k : Nat) :
    iterate (nxt f) k x = iterate (rnext (rot f v)) k x := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
    simp only [iterate]
    obtain ⟨_, hc, hvx⟩ := rot_mem h hv hx
    rw [nxt_rot h hc, hvx]
    exact ih (rnext_mem (rot_nodup h) hx)

/-- Darts with the same end are in one node cycle. -/
theorem reach_of_end {d d' : Nat} (hd : d < 2 * (nM f + nK f)) (hd' : d' < 2 * (nM f + nK f))
    (he : endOf f d = endOf f d') : ∃ k, iterate (nxt f) k d = d' := by
  by_cases hc : isCl f d
  · have hc' : isCl f d' := by
      apply Classical.byContradiction; intro hc'
      unfold endOf at he; rw [ite_eq_left hc, ite_eq_right hc'] at he; simp at he
    unfold endOf at he
    rw [ite_eq_left hc, ite_eq_left hc'] at he
    simp only [Sum.inr.injEq] at he
    obtain ⟨hj, ht, hdd⟩ := cl_dart hc
    obtain ⟨hj', ht', hdd'⟩ := cl_dart hc'
    rw [he] at hj ht hdd
    generalize oj f (d' / 2) = j at *
    generalize ot f (d / 2) = t at *
    generalize ot f (d' / 2) = t' at *
    subst hdd hdd'
    refine ⟨t' + kl f j - t, ?_⟩
    rw [iterate_cl h hj ht]
    congr 3
    rw [show t + (t' + kl f j - t) = t' + kl f j by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt ht']
  · have hc' : ¬ isCl f d' := by
      intro hc'
      unfold endOf at he; rw [ite_eq_right hc, ite_eq_left hc'] at he; simp at he
    unfold endOf at he
    rw [ite_eq_right hc, ite_eq_right hc'] at he
    simp only [Sum.inl.injEq] at he
    obtain ⟨hm, hv⟩ := in_rot h hd hc
    obtain ⟨hm', _⟩ := in_rot h hd' hc'
    rw [← he] at hm'
    obtain ⟨k, hk⟩ := rnext_reach (rot_nodup h) hm hm'
    exact ⟨k, by rw [iterate_rot h hv hm]; exact hk⟩

end dartlemmas2
end Complexity.Planar.Comb
