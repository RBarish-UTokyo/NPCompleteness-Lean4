module

public import Complexity.Planar.CombDarts
import Lean.Elab.Tactic.Omega

/-!
# Comb formulas are planar with their variable cycle

The rotation system of `CombDarts` and the face permutation it determines carry the sector
labels `tau`: each dart is labeled by the region counterclockwise after it.  The labels are
constant along faces (`tau_face`), so there are at least as many faces as labels: one for each
pocket and one for the outer region.  With one component, Euler's bound holds.
-/

@[expose] public section

-- Section hypotheses stay in the signatures of lemmas that do not use them, so that all
-- lemmas of a section take the same arguments.
set_option linter.unusedSectionVars false

namespace Complexity.Planar.Comb

open SAT

section tau

variable (f : CNF)

/-- The sector label of a dart. -/
noncomputable def tau (d : Nat) : Nat :=
  if d < 2 * nM f then (if d % 2 = 0 then legLbl f (d / 2) else clauseLbl f (d / 2))
  else if d % 2 = 0 then gapR f true (d / 2 - nM f) else gapR f false (nK f - 1 - vtx f d)

end tau

/-! ## Predecessors in concatenations -/

theorem getElem_mid {A C B : List Nat} {p : Nat} (hp : p < C.length) :
    (A ++ C ++ B)[A.length + p]'(by simp; omega) = C[p] := by
  rw [List.getElem_append_left (by simp; omega), List.getElem_append_right (by omega)]
  simp

theorem rprev_mid {A C B : List Nat} (hnd : (A ++ C ++ B).Nodup) (hA : A ≠ []) {p : Nat}
    (hp : p < C.length) :
    rprev (A ++ C ++ B) C[p] = if _hp0 : p = 0 then A.getLast hA
      else C[p - 1]'(by omega) := by
  have hAl : 0 < A.length := List.length_pos_iff.mpr hA
  have hlen : A.length + p < (A ++ C ++ B).length := by simp; omega
  rw [← getElem_mid (B := B) hp, rprev_getElem hnd hlen]
  have e1 : (A.length + p + (A ++ C ++ B).length - 1) % (A ++ C ++ B).length =
      A.length + p - 1 := by
    rw [show A.length + p + (A ++ C ++ B).length - 1 = (A.length + p - 1) + (A ++ C ++ B).length
      by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  simp only [e1]
  split
  · next h0 =>
    subst h0
    rw [List.getElem_append_left (by simp; omega), List.getElem_append_left (by omega),
      List.getLast_eq_getElem]
    simp only [Nat.add_zero]
  · next h0 =>
    simp only [show A.length + p - 1 = A.length + (p - 1) by omega]
    exact getElem_mid (by omega)

theorem rprev_first {L : List Nat} (hnd : L.Nodup) (hL : 0 < L.length) :
    rprev L L[0] = L[L.length - 1] := by
  rw [rprev_getElem hnd hL]
  congr 1
  rw [Nat.zero_add, Nat.mod_eq_of_lt (by omega)]

section face

variable {f : CNF} (h : CombOK f)
include h

/-- Legs of a vertex appear in its rotation after the leading spine dart (top) or after the
second spine dart (bottom). -/
theorem rot_top (v : Nat) :
    rot f v = [spE f v] ++ legs f true v ++ ([spW f v] ++ legs f false (nK f - 1 - v)) := by
  unfold rot; simp

theorem rot_bot (v : Nat) :
    rot f v = ([spE f v] ++ legs f true v ++ [spW f v]) ++ legs f false (nK f - 1 - v) ++ [] := by
  unfold rot; simp

theorem legs_getElem {s : Bool} {v p : Nat} (hp : p < (legs f s v).length) :
    (legs f s v)[p] = 2 * (group f s v)[p]'(by unfold legs at hp; simpa using hp) := by
  simp [legs]

theorem legs_length {s : Bool} {v : Nat} : (legs f s v).length = (group f s v).length := by
  unfold legs; simp

omit h in
theorem tau_leg {e : Nat} (he : e < nM f) : tau f (2 * e) = legLbl f e := by
  unfold tau; simp [show 2 * e < 2 * nM f by omega]

omit h in
theorem tau_cl {e : Nat} (he : e < nM f) : tau f (2 * e + 1) = clauseLbl f e := by
  unfold tau
  simp only [show 2 * e + 1 < 2 * nM f by omega, ite_true, show (2 * e + 1) % 2 = 1 by omega,
    show (2 * e + 1) / 2 = e by omega]
  simp

omit h in
theorem tau_spE {v : Nat} : tau f (spE f v) = gapR f true v := by
  unfold tau spE
  simp only [show ¬ 2 * (nM f + v) < 2 * nM f by omega, ite_false,
    show 2 * (nM f + v) % 2 = 0 by omega, ite_true]
  congr 1; omega

theorem tau_spW {v : Nat} (hv : v < nK f) : tau f (spW f v) = gapR f false (nK f - 1 - v) := by
  have hK := K_pos h
  have hm : spW f v ∈ rot f v := by unfold rot; simp
  obtain ⟨_, _, hvx⟩ := rot_mem h hv hm
  unfold tau
  rw [hvx]
  unfold spW
  have := Nat.mod_lt (v + nK f - 1) hK
  simp only [show ¬ 2 * (nM f + (v + nK f - 1) % nK f) + 1 < 2 * nM f by omega, ite_false,
    show (2 * (nM f + (v + nK f - 1) % nK f) + 1) % 2 = 1 by omega]
  simp


theorem rprev_top {v p : Nat} (hp : p < (group f true v).length) :
    rprev (rot f v) (2 * (group f true v)[p]) =
      if p = 0 then spE f v else 2 * (group f true v)[p - 1]'(by omega) := by
  have hnd := rot_nodup h (v := v)
  rw [rot_top h v] at hnd ⊢
  have hp' : p < (legs f true v).length := by rw [legs_length h]; exact hp
  rw [← legs_getElem h hp', rprev_mid hnd (by simp) hp']
  by_cases h0 : p = 0
  · rw [dite_eq_left h0, ite_eq_left h0]; simp
  · rw [dite_eq_right h0, ite_eq_right h0, legs_getElem h]

omit h in
theorem getLast_snoc (A : List Nat) (x : Nat) (hne : A ++ [x] ≠ []) : (A ++ [x]).getLast hne = x := by
  simp

theorem rprev_bot {v p : Nat} (hp : p < (group f false (nK f - 1 - v)).length) :
    rprev (rot f v) (2 * (group f false (nK f - 1 - v))[p]) =
      if p = 0 then spW f v else 2 * (group f false (nK f - 1 - v))[p - 1]'(by omega) := by
  have hnd := rot_nodup h (v := v)
  rw [rot_bot h v] at hnd ⊢
  have hp' : p < (legs f false (nK f - 1 - v)).length := by rw [legs_length h]; exact hp
  rw [← legs_getElem h hp', rprev_mid hnd (by simp) hp']
  by_cases h0 : p = 0
  · rw [dite_eq_left h0, ite_eq_left h0]; exact getLast_snoc _ _ _
  · rw [dite_eq_right h0, ite_eq_right h0, legs_getElem h]

theorem rprev_spW {v : Nat} :
    rprev (rot f v) (spW f v) =
      if hg : (group f true v).length = 0 then spE f v
      else 2 * (group f true v)[(group f true v).length - 1]'(by omega) := by
  have hnd := rot_nodup h (v := v)
  have hl : (legs f true v).length = (group f true v).length := legs_length h
  have hidx : (rot f v)[1 + (legs f true v).length]'(by unfold rot; simp <;> omega) = spW f v := by
    unfold rot
    rw [List.getElem_append_left (by simp <;> omega), List.getElem_append_right (by simp <;> omega)]
    simp
  rw [← hidx, rprev_getElem hnd]
  have hlen : (rot f v).length = 1 + (legs f true v).length + 1 +
      (legs f false (nK f - 1 - v)).length := by unfold rot; simp; omega
  have e1 : (1 + (legs f true v).length + (rot f v).length - 1) % (rot f v).length =
      (legs f true v).length := by
    rw [show 1 + (legs f true v).length + (rot f v).length - 1 =
      (legs f true v).length + (rot f v).length by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega)]
  simp only [e1]
  by_cases hg : (group f true v).length = 0
  · rw [dite_eq_left hg]
    have h0 : (legs f true v).length = 0 := by omega
    simp only [h0]
    unfold rot; simp
  · rw [dite_eq_right hg]
    unfold rot
    rw [List.getElem_append_left (by simp <;> omega), List.getElem_append_left (by simp <;> omega),
      List.getElem_append_right (by simp <;> omega)]
    simp only [List.length_singleton]
    rw [legs_getElem h]
    congr 2
    omega

theorem rprev_spE {v : Nat} :
    rprev (rot f v) (spE f v) =
      if hg : (group f false (nK f - 1 - v)).length = 0 then spW f v
      else 2 * (group f false (nK f - 1 - v))[(group f false (nK f - 1 - v)).length - 1]'
        (by omega) := by
  have hnd := rot_nodup h (v := v)
  have hl1 : (legs f true v).length = (group f true v).length := legs_length h
  have hl2 : (legs f false (nK f - 1 - v)).length = (group f false (nK f - 1 - v)).length :=
    legs_length h
  have hlen : (rot f v).length = 1 + (legs f true v).length + 1 +
      (legs f false (nK f - 1 - v)).length := by unfold rot; simp; omega
  have h0 : (rot f v)[0]'(by omega) = spE f v := by unfold rot; simp
  rw [← h0, rprev_first hnd (by omega)]
  by_cases hg : (group f false (nK f - 1 - v)).length = 0
  · rw [dite_eq_left hg]
    have hz : (legs f false (nK f - 1 - v)).length = 0 := by omega
    have : (rot f v).length - 1 = 1 + (legs f true v).length := by omega
    simp only [this]
    unfold rot
    rw [List.getElem_append_left (by simp <;> omega), List.getElem_append_right (by simp <;> omega)]
    simp
  · rw [dite_eq_right hg]
    have : (rot f v).length - 1 = (1 + (legs f true v).length + 1) +
        ((legs f false (nK f - 1 - v)).length - 1) := by omega
    simp only [this]
    unfold rot
    rw [List.getElem_append_right (by simp <;> omega)]
    simp only [List.length_append, List.length_singleton]
    rw [legs_getElem h]
    congr 2
    omega

/-- Labels at the clause end of the previous leg. -/
theorem clauseLbl_prev {j t : Nat} (hj : j < f.length) (ht : t < kl f j) :
    clauseLbl f (off f j + (t + kl f j - 1) % kl f j) = legLbl f (off f j + t) := by
  have hk := h.len2 j hj
  have hm := Nat.mod_lt (t + kl f j - 1) (show 0 < kl f j by omega)
  unfold clauseLbl legLbl
  rw [(occ_eq f j _ hj hm).1, (occ_eq f j _ hj hm).2, (occ_eq f j t hj ht).1,
    (occ_eq f j t hj ht).2]
  rcases Nat.eq_zero_or_pos t with h0 | h0
  · subst h0
    rw [Nat.zero_add, Nat.mod_eq_of_lt (show kl f j - 1 < kl f j by omega)]
    simp [show ¬ (kl f j - 1 + 1 < kl f j) by omega]
  · rw [show t + kl f j - 1 = (t - 1) + kl f j by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt (show t - 1 < kl f j by omega)]
    simp [show t - 1 + 1 < kl f j by omega, show t ≠ 0 by omega]

/-- The label before a leg at its vertex is the label after the leg at its clause. -/
theorem tau_leg_prev {s : Bool} {v p : Nat} (hp : p < (group f s v).length)
    (hfirst : p = 0 → tau f (if s then spE f (opos f s v) else spW f (opos f s v)) = gapR f s v) :
    tau f (if p = 0 then (if s then spE f (opos f s v) else spW f (opos f s v))
      else 2 * (group f s v)[p - 1]'(by omega)) = clauseLbl f (group f s v)[p] := by
  have hat := mem_group.mp (List.getElem_mem hp)
  by_cases h0 : p = 0
  · rw [ite_eq_left h0, hfirst h0]
    subst h0
    exact q1_first h hat (fun z hz hne => group_first h hp hz hne)
  · rw [ite_eq_right h0]
    have hat' := mem_group.mp (List.getElem_mem (show p - 1 < (group f s v).length by omega))
    rw [tau_leg hat'.1]
    obtain ⟨k1, k2⟩ := group_consec h hp (by omega)
    exact q1_pred h hat' hat k1 k2


theorem spW_succ {i : Nat} (hi : i < nK f) : spW f ((i + 1) % nK f) = 2 * (nM f + i) + 1 := by
  have hK := K_pos h
  unfold spW
  congr 2
  rcases Nat.lt_or_ge (i + 1) (nK f) with c | c
  · rw [Nat.mod_eq_of_lt c, show i + 1 + nK f - 1 = i + nK f by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt hi]
  · rw [show i + 1 = nK f by omega, Nat.mod_self, Nat.zero_add,
      Nat.mod_eq_of_lt (show nK f - 1 < nK f by omega)]
    omega

theorem prv_spine_W {w : Nat} (hw : w < nK f) : prv f (spW f w) = rprev (rot f w) (spW f w) := by
  have hm : spW f w ∈ rot f w := by unfold rot; simp
  obtain ⟨_, hc, hv⟩ := rot_mem h hw hm
  rw [prv_rot h hc, hv]

theorem prv_spine_E {i : Nat} (hi : i < nK f) : prv f (spE f i) = rprev (rot f i) (spE f i) := by
  have hm : spE f i ∈ rot f i := by unfold rot; simp
  obtain ⟨_, hc, hv⟩ := rot_mem h hi hm
  rw [prv_rot h hc, hv]

omit h in
theorem no_at_of_empty {s : Bool} {v : Nat} (hg : (group f s v).length = 0) :
    ∀ z, ¬ At f s v z := fun z hz => by
  have := List.length_pos_of_mem (mem_group.mpr hz)
  omega

/-- At a leg, the face steps from the clause to the previous dart at the variable. -/
theorem tau_leg_step {s : Bool} {v e : Nat} (hat : At f s v e)
    (hrot : ∀ p, ∀ hp : p < (group f s v).length,
      prv f (2 * (group f s v)[p]) = if p = 0 then (if s then spE f (opos f s v) else spW f
        (opos f s v)) else 2 * (group f s v)[p - 1]'(by omega))
    (hspine : tau f (if s then spE f (opos f s v) else spW f (opos f s v)) = gapR f s v) :
    tau f (prv f (2 * e)) = clauseLbl f e := by
  obtain ⟨p, hp, hpe⟩ := mem_getElem (mem_group.mpr hat)
  rw [← hpe, hrot p hp]
  have hat0 := mem_group.mp (List.getElem_mem hp)
  by_cases h0 : p = 0
  · rw [ite_eq_left h0, hspine]
    subst h0
    exact q1_first h hat0 (fun z hz hne => group_first h hp hz hne)
  · rw [ite_eq_right h0]
    have hat' := mem_group.mp (List.getElem_mem (show p - 1 < (group f s v).length by omega))
    rw [tau_leg hat'.1]
    obtain ⟨k1, k2⟩ := group_consec h hp (by omega)
    exact q1_pred h hat' hat0 k1 k2

/-- **The labels are constant along faces.** -/
theorem tau_face {d : Nat} (hd : d < 2 * (nM f + nK f)) : tau f (prv f (ed d)) = tau f d := by
  have hK := K_pos h
  rcases Nat.lt_or_ge d (2 * nM f) with hdM | hdM
  · rcases Nat.mod_two_eq_zero_or_one d with h2 | h2
    · obtain ⟨e, rfl⟩ : ∃ e, d = 2 * e := ⟨d / 2, by omega⟩
      have he : e < nM f := by omega
      obtain ⟨hj, ht, hoff⟩ := occ_spec f e he
      have hm := Nat.mod_lt (ot f e + kl f (oj f e) - 1) (show 0 < kl f (oj f e) by omega)
      rw [ed_even, show 2 * e + 1 = 2 * (off f (oj f e) + ot f e) + 1 by omega,
        prv_cl h hj ht, tau_cl (off_add_lt f _ _ hj hm), clauseLbl_prev h hj ht, hoff, tau_leg he]
    · obtain ⟨e, rfl⟩ : ∃ e, d = 2 * e + 1 := ⟨d / 2, by omega⟩
      have he : e < nM f := by omega
      rw [ed_odd, tau_cl he]
      obtain ⟨hj, ht, _⟩ := occ_spec f e he
      have hv := vr_lt _ _ hj ht
      obtain ⟨w, hw⟩ : ∃ w, vr f (oj f e) (ot f e) = w := ⟨_, rfl⟩
      rw [hw] at hv
      have hvtx : ∀ x, x ∈ rot f w → ¬ isCl f x ∧ vtx f x = w := fun x hx =>
        ⟨(rot_mem h hv hx).2.1, (rot_mem h hv hx).2.2⟩
      cases hs : isTop f (oj f e)
      · have hat : At f false (nK f - 1 - w) e :=
          ⟨he, hs, by unfold ov opos; rw [hs, hw]; rfl⟩
        apply tau_leg_step h hat
        · intro p hp
          have hm : 2 * (group f false (nK f - 1 - w))[p] ∈ rot f w := by
            unfold rot; simp only [List.mem_append, List.mem_singleton, legs_mem]
            right; exact ⟨_, mem_group.mp (List.getElem_mem hp), rfl⟩
          rw [prv_rot h (hvtx _ hm).1, (hvtx _ hm).2, rprev_bot h hp]
          simp only [Bool.false_eq_true, ite_false]
          unfold opos
          simp only [Bool.false_eq_true, ite_false, show nK f - 1 - (nK f - 1 - w) = w by omega]
        · simp only [Bool.false_eq_true, ite_false]
          unfold opos
          simp only [Bool.false_eq_true, ite_false, show nK f - 1 - (nK f - 1 - w) = w by omega]
          exact tau_spW h hv
      · have hat : At f true w e := ⟨he, hs, by unfold ov opos; rw [hs, hw]; rfl⟩
        apply tau_leg_step h hat
        · intro p hp
          have hm : 2 * (group f true w)[p] ∈ rot f w := by
            unfold rot; simp only [List.mem_append, List.mem_singleton, legs_mem]
            left; left; right; exact ⟨_, mem_group.mp (List.getElem_mem hp), rfl⟩
          rw [prv_rot h (hvtx _ hm).1, (hvtx _ hm).2, rprev_top h hp]
          simp [opos]
        · simp only [ite_true]
          unfold opos; simp only [ite_true]
          exact tau_spE
  · have hi : d / 2 - nM f < nK f := by omega
    obtain ⟨i, hid⟩ : ∃ i, d / 2 - nM f = i := ⟨_, rfl⟩
    rw [hid] at hi
    rcases Nat.mod_two_eq_zero_or_one d with h2 | h2
    · -- the spine dart towards the next vertex
      have hdE : d = spE f i := by unfold spE; omega
      rw [hdE, tau_spE]
      have hed : ed (spE f i) = spW f ((i + 1) % nK f) := by
        unfold spE; rw [ed_even, spW_succ h hi]
      have hw := Nat.mod_lt (i + 1) hK
      rw [hed, prv_spine_W h hw, rprev_spW h]
      rcases Nat.lt_or_ge (i + 1) (nK f) with c | c
      · rw [Nat.mod_eq_of_lt c]
        split
        · next hg =>
          rw [tau_spE]; exact q2_empty h (no_at_of_empty hg)
        · next hg =>
          have hy := mem_group.mp (List.getElem_mem (show (group f true (i + 1)).length - 1 <
            (group f true (i + 1)).length by omega))
          rw [tau_leg hy.1]
          exact q2_last h hy (fun z hz hne => group_last h (by omega) hz hne)
      · have ci : i = nK f - 1 := by omega
        rw [show i + 1 = nK f by omega, Nat.mod_self, ci, gap_top h]
        split
        · next hg => rw [tau_spE]; exact q2_empty0 h (no_at_of_empty hg)
        · next hg =>
          have hy := mem_group.mp (List.getElem_mem (show (group f true 0).length - 1 <
            (group f true 0).length by omega))
          rw [tau_leg hy.1]
          exact q2_last0 h hy (fun z hz hne => group_last h (by omega) hz hne)
    · -- the spine dart towards the previous vertex
      have hdW : d = spW f ((i + 1) % nK f) := by rw [spW_succ h hi]; omega
      have hw := Nat.mod_lt (i + 1) hK
      rw [hdW, tau_spW h hw]
      have hed : ed (spW f ((i + 1) % nK f)) = spE f i := by
        rw [spW_succ h hi, ed_odd]; rfl
      rw [hed, prv_spine_E h hi, rprev_spE h]
      rcases Nat.lt_or_ge (i + 1) (nK f) with c | c
      · rw [Nat.mod_eq_of_lt c]
        obtain ⟨u, hu1, hu2⟩ : ∃ u, nK f - 1 - i = u + 1 ∧ nK f - 1 - (i + 1) = u :=
          ⟨_, by omega, rfl⟩
        simp only [hu1, hu2]
        split
        · next hg =>
          rw [tau_spW h hi, hu1]
          exact q2_empty h (no_at_of_empty hg)
        · next hg =>
          have hy := mem_group.mp (List.getElem_mem (show (group f false (u + 1)).length - 1 <
            (group f false (u + 1)).length by omega))
          rw [tau_leg hy.1]
          exact q2_last h hy (fun z hz hne => group_last h (by omega) hz hne)
      · have ci : i = nK f - 1 := by omega
        subst ci
        have e0 : (nK f - 1 + 1) % nK f = 0 := by
          rw [Nat.sub_add_cancel (show 1 ≤ nK f by omega), Nat.mod_self]
        simp only [e0, Nat.sub_zero, Nat.sub_self]
        rw [gap_top h]
        split
        · next hg =>
          rw [tau_spW h (by omega), Nat.sub_self]
          exact q2_empty0 h (no_at_of_empty hg)
        · next hg =>
          have hy := mem_group.mp (List.getElem_mem (show (group f false 0).length - 1 <
            (group f false 0).length by omega))
          rw [tau_leg hy.1]
          exact q2_last0 h hy (fun z hz hne => group_last h (by omega) hz hne)

end face


/-! ## The planar embedding -/

/-- Lists of numbers below `N` as lists of `Fin N`. -/
def toFin {N : Nat} (l : List Nat) (hl : ∀ x ∈ l, x < N) : List (Fin N) :=
  l.attach.map fun x => ⟨x.1, hl x.1 x.2⟩

theorem toFin_map {N : Nat} {β : Type} (l : List Nat) (hl : ∀ x ∈ l, x < N) (g : Nat → β) :
    (toFin l hl).map (fun x => g x.val) = l.map g := by
  unfold toFin
  rw [List.map_map]
  conv => rhs; rw [← List.attach_map_subtype_val l]
  rw [List.map_map]
  rfl

theorem toFin_length {N : Nat} (l : List Nat) (hl : ∀ x ∈ l, x < N) :
    (toFin l hl).length = l.length := by
  simp [toFin]

theorem sum_sub_one (l : List Nat) (g : Nat → Nat) (hg : ∀ x ∈ l, 1 ≤ g x) :
    (l.map (fun x => g x - 1)).sum + l.length = (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have := hg a (by simp)
    have := ih (fun x hx => hg x (by simp [hx]))
    omega

section final

variable {f : CNF} (h : CombOK f)
include h

omit h in
theorem es_length : (incidenceGraph f ++ variableCycle f).length = nM f + nK f := by
  rw [List.length_append, incidenceGraph_length, variableCycle_length]; rfl

omit h in
theorem sum_kl : ((List.range f.length).map (kl f)).sum = nM f := by
  have : (List.range f.length).map (kl f) = lens f := by
    apply List.ext_getElem
    · simp [lens]
    · intro i h1 h2
      simp only [List.getElem_map, List.getElem_range, lens]
      simp at h1
      exact kl_of_lt f i h1
  rw [this]; rfl

theorem m_le_M : f.length ≤ nM f := by
  have := sum_sub_one (List.range f.length) (kl f) (fun x hx => by
    have := h.len2 x (List.mem_range.mp hx); omega)
  rw [sum_kl] at this
  simp at this
  omega

theorem pockets_count :
    ((List.range f.length).map (fun j => kl f j - 1)).sum + f.length = nM f := by
  have := sum_sub_one (List.range f.length) (kl f) (fun x hx => by
    have := h.len2 x (List.mem_range.mp hx); omega)
  rw [sum_kl] at this
  simpa using this

theorem end_eq {d : Nat} (hd : d < 2 * (nM f + nK f)) :
    halfEdgeEnd (incidenceGraph f ++ variableCycle f) d = some (endOf f d) := by
  have hil : (incidenceGraph f).length = nM f := by rw [incidenceGraph_length]; rfl
  rcases Nat.lt_or_ge d (2 * nM f) with h1 | h1
  · rw [halfEdgeEnd_append_left _ _ d (by omega)]
    have he : d / 2 < nM f := by omega
    obtain ⟨hj, ht, hoff⟩ := occ_spec f (d / 2) he
    have ht' : ot f (d / 2) < f[oj f (d / 2)].length := by rw [← kl_of_lt f _ hj]; exact ht
    have hg := incidenceGraph_getElem? f (oj f (d / 2)) (ot f (d / 2)) hj ht'
    rw [show ((f.map List.length).take (oj f (d / 2))).sum + ot f (d / 2) = d / 2 from hoff] at hg
    obtain ⟨g0, g1⟩ := halfEdgeEnd_of_getElem? _ _ _ _ hg
    rcases Nat.mod_two_eq_zero_or_one d with h2 | h2
    · rw [show d = 2 * (d / 2) by omega, g0]
      unfold endOf
      rw [ite_eq_right (fun hc => by unfold isCl at hc; omega), vtx_leg he, vr_of_lt f _ _ hj ht]
    · rw [show d = 2 * (d / 2) + 1 by omega, g1]
      unfold endOf
      rw [ite_eq_left ⟨by omega, by omega⟩, show (2 * (d / 2) + 1) / 2 = d / 2 by omega]
  · rw [halfEdgeEnd_append_right _ _ d (by omega), hil]
    have hK := K_pos h
    obtain ⟨i, hi_def⟩ : ∃ i, d / 2 - nM f = i := ⟨_, rfl⟩
    have hi : i < variableCount f := by
      have : nK f = variableCount f := rfl
      omega
    obtain ⟨g0, g1⟩ := halfEdgeEnd_of_getElem? _ _ _ _ (variableCycle_getElem? f i hi)
    unfold endOf
    rw [ite_eq_right (fun hc => by unfold isCl at hc; omega)]
    have hv : vtx f d = if d % 2 = 0 then i else (i + 1) % nK f := by
      unfold vtx; rw [ite_eq_right (by omega), hi_def]
    rw [hv]
    rcases Nat.mod_two_eq_zero_or_one d with h2 | h2
    · rw [show d - 2 * nM f = 2 * i by omega, g0, ite_eq_left h2]
    · rw [show d - 2 * nM f = 2 * i + 1 by omega, g1, ite_eq_right (show ¬ d % 2 = 0 by omega)]
      have : nK f = variableCount f := rfl
      rw [← this]
      by_cases he : i + 1 = nK f
      · rw [ite_eq_left he, he, Nat.mod_self]
      · rw [ite_eq_right he, Nat.mod_eq_of_lt (by omega)]

theorem ed_lt {d : Nat} (hd : d < 2 * (nM f + nK f)) : ed d < 2 * (nM f + nK f) := by
  rcases Nat.mod_two_eq_zero_or_one d with h2 | h2
  · rw [show d = 2 * (d / 2) by omega, ed_even]; omega
  · rw [show d = 2 * (d / 2) + 1 by omega, ed_odd]; omega

omit h in
theorem ed_ed (d : Nat) : ed (ed d) = d := by
  rcases Nat.mod_two_eq_zero_or_one d with h2 | h2
  · rw [show d = 2 * (d / 2) by omega, ed_even, ed_odd]
  · rw [show d = 2 * (d / 2) + 1 by omega, ed_odd, ed_even]

theorem dart_lt (d : Fin (2 * (incidenceGraph f ++ variableCycle f).length)) :
    d.val < 2 * (nM f + nK f) := by
  have := d.isLt
  have := es_length (f := f)
  omega

theorem lt_darts {x : Nat} (hx : x < 2 * (nM f + nK f)) :
    x < 2 * (incidenceGraph f ++ variableCycle f).length := by
  have := es_length (f := f)
  omega

/-- The hypermap of the comb drawing. -/
noncomputable def hmap : Hypermap (2 * (incidenceGraph f ++ variableCycle f).length) where
  edge d := ⟨ed d.val, lt_darts h (ed_lt h (dart_lt h d))⟩
  node d := ⟨nxt f d.val, lt_darts h (nxt_spec h (dart_lt h d)).1⟩
  face d := ⟨prv f (ed d.val), lt_darts h (nxt_spec h (ed_lt h (dart_lt h d))).2.1⟩
  edgeK x := by
    apply Fin.ext
    simp only [ed_ed]
    exact (nxt_spec h (dart_lt h x)).2.2.1

theorem iterate_val (k : Nat) (d : Fin (2 * (incidenceGraph f ++ variableCycle f).length)) :
    (iterate (hmap h).node k d).val = iterate (nxt f) k d.val := by
  induction k generalizing d with
  | zero => rfl
  | succ k ih => simp only [iterate]; rw [ih]; rfl

end final

/-! ## Counting -/

theorem flatMap_congr' {α β : Type} {l : List α} {f1 f2 : α → List β}
    (hf : ∀ a ∈ l, f1 a = f2 a) : l.flatMap f1 = l.flatMap f2 := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.flatMap_cons]
    rw [hf a (by simp), ih (fun b hb => hf b (by simp [hb]))]

section main

variable {f : CNF} (h : CombOK f)
include h

/-- The pocket darts at the clauses. -/
def pocketDarts (f : CNF) : List Nat :=
  (List.range f.length).flatMap fun j => (List.range (kl f j - 1)).map fun t => 2 * (off f j + t) + 1

theorem pocketDarts_lt {x : Nat} (hx : x ∈ pocketDarts f) : x < 2 * nM f := by
  unfold pocketDarts at hx
  simp only [List.mem_flatMap, List.mem_range, List.mem_map] at hx
  obtain ⟨j, hj, t, ht, rfl⟩ := hx
  have := off_add_lt f j t hj (by omega)
  omega

theorem pocketDarts_tau :
    (pocketDarts f).map (tau f) =
      (List.range f.length).flatMap fun j => (List.range (kl f j - 1)).map fun t => off f j + t + 1 := by
  unfold pocketDarts
  rw [List.map_flatMap]
  apply flatMap_congr'
  intro j hj
  rw [List.mem_range] at hj
  rw [List.map_map]
  apply List.map_congr_left
  intro t ht
  rw [List.mem_range] at ht
  have hlt := off_add_lt f j t hj (by omega)
  simp only [Function.comp_apply]
  rw [tau_cl hlt]
  unfold clauseLbl
  rw [(occ_eq f j t hj (by omega)).1, (occ_eq f j t hj (by omega)).2, ite_eq_left (by omega)]
  rfl

theorem pocket_labels_sorted :
    ((List.range f.length).flatMap fun j =>
      (List.range (kl f j - 1)).map fun t => off f j + t + 1).Pairwise (· < ·) := by
  rw [List.pairwise_flatMap]
  constructor
  · intro j _
    exact List.Pairwise.map _ (fun a b hab => by omega) List.pairwise_lt_range
  · apply List.Pairwise.imp_of_mem _ List.pairwise_lt_range
    intro j1 j2 hj1 hj2 hlt x hx y hy
    rw [List.mem_range] at hj1 hj2
    simp only [List.mem_map, List.mem_range] at hx hy
    obtain ⟨t1, ht1, rfl⟩ := hx
    obtain ⟨t2, ht2, rfl⟩ := hy
    have := off_succ f j1 hj1
    have := off_mono f (show j1 + 1 ≤ j2 by omega)
    omega

theorem pocket_labels_length :
    ((List.range f.length).flatMap fun j =>
      (List.range (kl f j - 1)).map fun t => off f j + t + 1).length = nM f - f.length := by
  rw [List.length_flatMap]
  have := pockets_count h
  simp only [List.length_map, List.length_range]
  omega

theorem faces_ge : nM f - f.length + 1 ≤ cycleCount (hmap h).face := by
  let l := pocketDarts f ++ [spE f (nK f - 1)]
  have hl : ∀ x ∈ l, x < 2 * (incidenceGraph f ++ variableCycle f).length := by
    intro x hx
    apply lt_darts h
    simp only [l, List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | rfl
    · have := pocketDarts_lt h hx; omega
    · unfold spE; have := K_pos h; omega
  have key := cycleCount_ge (hmap h).face (fun x => tau f x.val)
    (fun x => tau_face h (dart_lt h x)) (toFin l hl) (by
      rw [toFin_map l hl (tau f)]
      simp only [l, List.map_append, List.map_singleton, pocketDarts_tau h, tau_spE, gap_top h]
      rw [List.nodup_append]
      refine ⟨pocket_labels_sorted h |>.imp (fun hab => Nat.ne_of_lt hab),
        List.pairwise_singleton _ _, ?_⟩
      intro a ha b hb
      rw [List.mem_singleton] at hb
      subst hb
      simp only [List.mem_flatMap, List.mem_range, List.mem_map] at ha
      obtain ⟨_, _, _, _, rfl⟩ := ha
      omega)
  rw [toFin_length] at key
  simp only [l, List.length_append, List.length_singleton] at key
  have := pocket_labels_length h
  rw [← pocketDarts_tau h, List.length_map] at this
  omega


theorem endOf_spE {v : Nat} (hv : v < nK f) : endOf f (spE f v) = .inl v := by
  have hm : spE f v ∈ rot f v := by unfold rot; simp
  obtain ⟨_, hc, hvx⟩ := rot_mem h hv hm
  unfold endOf; rw [ite_eq_right hc, hvx]

theorem endOf_cl {j : Nat} (hj : j < f.length) : endOf f (2 * off f j + 1) = .inr j := by
  have hk := h.len2 j hj
  have hc : isCl f (2 * off f j + 1) :=
    ⟨by have := off_add_lt f j 0 hj (by omega); omega, by omega⟩
  unfold endOf
  rw [ite_eq_left hc, show (2 * off f j + 1) / 2 = off f j + 0 by omega,
    (occ_eq f j 0 hj (by omega)).1]

theorem nodes_ge : nK f + f.length ≤ cycleCount (hmap h).node := by
  let l := (List.range (nK f)).map (spE f) ++ (List.range f.length).map (fun j => 2 * off f j + 1)
  have hl : ∀ x ∈ l, x < 2 * (incidenceGraph f ++ variableCycle f).length := by
    intro x hx
    apply lt_darts h
    simp only [l, List.mem_append, List.mem_map, List.mem_range] at hx
    rcases hx with ⟨v, hv, rfl⟩ | ⟨j, hj, rfl⟩
    · unfold spE; omega
    · have := off_add_lt f j 0 hj (by have := h.len2 j hj; omega); omega
  have hmap_eq : l.map (endOf f) =
      (List.range (nK f)).map Sum.inl ++ (List.range f.length).map Sum.inr := by
    simp only [l, List.map_append, List.map_map]
    congr 1
    · apply List.map_congr_left
      intro v hv; rw [List.mem_range] at hv
      exact endOf_spE h hv
    · apply List.map_congr_left
      intro j hj; rw [List.mem_range] at hj
      exact endOf_cl h hj
  have key := cycleCount_ge (hmap h).node (fun x => endOf f x.val)
    (fun x => (nxt_spec h (dart_lt h x)).2.2.2.2) (toFin l hl) (by
      rw [toFin_map l hl (endOf f), hmap_eq, List.nodup_append]
      refine ⟨List.Pairwise.map _ (fun a b hab => by simpa using hab) List.nodup_range,
        List.Pairwise.map _ (fun a b hab => by simpa using hab) List.nodup_range, ?_⟩
      intro a ha b hb
      simp only [List.mem_map] at ha hb
      obtain ⟨_, _, rfl⟩ := ha
      obtain ⟨_, _, rfl⟩ := hb
      simp)
  rw [toFin_length] at key
  simpa [l] using key

/-- Linked darts. -/
def Lk (x y : Fin (2 * (incidenceGraph f ++ variableCycle f).length)) : Prop :=
  ∃ k, (hmap h).linked k x y = true

theorem lk_trans {x y z : Fin (2 * (incidenceGraph f ++ variableCycle f).length)}
    (h1 : Lk h x y) (h2 : Lk h y z) : Lk h x z := by
  obtain ⟨a, ha⟩ := h1
  obtain ⟨b, hb⟩ := h2
  exact ⟨a + b, Linked.linked_trans _ ha hb⟩

theorem lk_symm {x y : Fin (2 * (incidenceGraph f ++ variableCycle f).length)}
    (h1 : Lk h x y) : Lk h y x := by
  obtain ⟨a, ha⟩ := h1
  exact hm_linked_symm _ ha

theorem lk_edge (x : Fin (2 * (incidenceGraph f ++ variableCycle f).length)) :
    Lk h x ((hmap h).edge x) :=
  ⟨1, Linked.linked_step _ (Linked.linked_refl _ 0 x) (Or.inl rfl)⟩

theorem lk_iter (x : Fin (2 * (incidenceGraph f ++ variableCycle f).length)) (k : Nat) :
    Lk h x (iterate (hmap h).node k x) := by
  induction k generalizing x with
  | zero => exact ⟨0, Linked.linked_refl _ 0 x⟩
  | succ k ih =>
    simp only [iterate]
    exact lk_trans h ⟨1, Linked.linked_step _ (Linked.linked_refl _ 0 x) (Or.inr (Or.inl rfl))⟩
      (ih _)

theorem lk_end {x y : Fin (2 * (incidenceGraph f ++ variableCycle f).length)}
    (he : endOf f x.val = endOf f y.val) : Lk h x y := by
  obtain ⟨k, hk⟩ := reach_of_end h (dart_lt h x) (dart_lt h y) he
  have : iterate (hmap h).node k x = y := Fin.ext (by rw [iterate_val h]; exact hk)
  rw [← this]
  exact lk_iter h x k

/-- The spine dart at `v` as a dart. -/
def spF (v : Nat) (hv : v < nK f) : Fin (2 * (incidenceGraph f ++ variableCycle f).length) :=
  ⟨spE f v, lt_darts h (by unfold spE; omega)⟩

theorem lk_spine (v : Nat) (hv : v < nK f) : Lk h (spF h v hv) (spF h 0 (K_pos h)) := by
  induction v with
  | zero => exact ⟨0, Linked.linked_refl _ 0 _⟩
  | succ v ih =>
    have hv' : v < nK f := by omega
    have hW : spW f (v + 1) = 2 * (nM f + v) + 1 := by
      have := spW_succ h hv'
      rwa [Nat.mod_eq_of_lt hv] at this
    let w : Fin (2 * (incidenceGraph f ++ variableCycle f).length) :=
      ⟨spW f (v + 1), lt_darts h (by rw [hW]; omega)⟩
    have hmW : spW f (v + 1) ∈ rot f (v + 1) := by unfold rot; simp
    obtain ⟨_, hcW, hvW⟩ := rot_mem h hv hmW
    have e1 : Lk h (spF h (v + 1) hv) w := lk_end h (by
      show endOf f (spE f (v + 1)) = endOf f (spW f (v + 1))
      rw [endOf_spE h hv]
      unfold endOf; rw [ite_eq_right hcW, hvW])
    have e2 : (hmap h).edge w = spF h v hv' := by
      apply Fin.ext
      show ed (spW f (v + 1)) = spE f v
      rw [hW, ed_odd]; rfl
    exact lk_trans h e1 (lk_trans h (e2 ▸ lk_edge h w) (ih hv'))

theorem lk_all (x : Fin (2 * (incidenceGraph f ++ variableCycle f).length)) :
    Lk h x (spF h 0 (K_pos h)) := by
  have to_spine : ∀ y : Fin (2 * (incidenceGraph f ++ variableCycle f).length),
      ¬ isCl f y.val → Lk h y (spF h 0 (K_pos h)) := by
    intro y hy
    obtain ⟨_, hv⟩ := in_rot h (dart_lt h y) hy
    have : Lk h y (spF h (vtx f y.val) hv) := lk_end h (by
      show endOf f y.val = endOf f (spE f (vtx f y.val))
      rw [endOf_spE h hv]; unfold endOf; rw [ite_eq_right hy])
    exact lk_trans h this (lk_spine h _ hv)
  by_cases hc : isCl f x.val
  · have hne : ¬ isCl f ((hmap h).edge x).val := by
      show ¬ isCl f (ed x.val)
      obtain ⟨_, h2⟩ := hc
      rw [show x.val = 2 * (x.val / 2) + 1 by omega, ed_odd]
      exact not_isCl_even (by omega)
    exact lk_trans h (lk_edge h x) (to_spine _ hne)
  · exact to_spine x hc

theorem components_le : (hmap h).componentCount ≤ 1 := by
  have hpos : 0 < 2 * (incidenceGraph f ++ variableCycle f).length :=
    lt_darts h (by have := K_pos h; omega)
  have := componentCount_le (hmap h) (fun x => x.val == 0) (by
    intro x hx
    simp only [beq_eq_false_iff_ne, ne_eq] at hx
    refine ⟨⟨0, hpos⟩, by show 0 < x.val; omega, ?_⟩
    exact lk_trans h (lk_all h x) (lk_symm h (lk_all h ⟨0, hpos⟩)))
  refine Nat.le_trans this ?_
  rw [countP_finRange_val (fun x => x == 0)]
  have : (List.range (2 * (incidenceGraph f ++ variableCycle f).length)).countP (fun x => x == 0) =
      1 := by
    rw [show 2 * (incidenceGraph f ++ variableCycle f).length =
      (2 * (incidenceGraph f ++ variableCycle f).length - 1) + 1 by omega, List.range_succ_eq_map,
      List.countP_cons]
    simp [List.countP_eq_zero]
  omega

/-- **A comb formula is planar together with its variable cycle.** -/
theorem comb_planar : PlanarGraph (incidenceGraph f ++ variableCycle f) := by
  refine ⟨hmap h, fun d => rfl, ?_, ?_⟩
  · intro d d'
    rw [end_eq h (dart_lt h d), end_eq h (dart_lt h d')]
    constructor
    · rintro ⟨k, hk⟩
      have := (iterate_end h (dart_lt h d) k).2
      rw [← iterate_val h, hk] at this
      rw [this]
    · intro he
      simp only [Option.some.injEq] at he
      obtain ⟨k, hk⟩ := reach_of_end h (dart_lt h d) (dart_lt h d') he
      exact ⟨k, Fin.ext (by rw [iterate_val h]; exact hk)⟩
  · apply planar_of_bounds _ (nM f + nK f) (nK f + f.length) (nM f - f.length + 1) 1
    · have := cycleCount_graphEdge_ge (E := (incidenceGraph f ++ variableCycle f).length)
        (edge := (hmap h).edge) (fun d => rfl)
      have e := es_length (f := f)
      omega
    · exact nodes_ge h
    · exact faces_ge h
    · exact components_le h
    · have := m_le_M h
      have := es_length (f := f)
      omega
end main
end Complexity.Planar.Comb
