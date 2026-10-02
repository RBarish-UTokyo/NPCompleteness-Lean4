module

public import Complexity.Planar.GridDef
import Lean.Elab.Tactic.Omega

/-!
# The grid formula is a comb formula

Clauses of a cell stay within the ten spine positions of the cell, and the template is laminar
on each side and never passes over the incoming variable on its side or the outgoing variable on
its side; rainbow pairs between two columns nest.  Hence any two clauses on the same side are
laminar, and `combOK_of` applies.
-/

@[expose] public section

namespace Complexity.Planar.Grid

open SAT Comb

/-! ## Laminarity criteria -/

/-- The smallest and largest variable of a clause. -/
def smin (c : Clause) : Nat := (svars c).headD 0
def smax (c : Clause) : Nat := (svars c).getLastD 0

/-- The pairwise condition of `combOK_of`. -/
def R (c d : Clause) : Prop := sideOf c = sideOf d → LamRaw (svars c) (svars d)

theorem R_symm {c d : Clause} (h : R c d) : R d c := by
  intro hs
  have := h hs.symm
  unfold LamRaw DisjRaw at this ⊢
  rcases this with h1 | h1 | h1
  · exact Or.inr (Or.inl h1)
  · exact Or.inl h1
  · exact Or.inr (Or.inr (by omega))

theorem R_disj {c d : Clause} (h : smax c ≤ smin d ∨ smax d ≤ smin c) : R c d :=
  fun _ => Or.inr (Or.inr h)

theorem R_side {c d : Clause} (h : sideOf c ≠ sideOf d) : R c d := fun hs => absurd hs h

theorem headD_eq {l : List Nat} (h : 0 < l.length) : l.headD 0 = l[0] := by
  rw [List.headD_eq_head?_getD, List.head?_eq_getElem?, List.getElem?_eq_getElem h]; rfl

theorem getLastD_eq {l : List Nat} (h : 0 < l.length) : l.getLastD 0 = l[l.length - 1] := by
  rw [List.getLastD_eq_getLast?, List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)]
  rfl

/-- A clause within the span of a two-variable clause lies in its pocket. -/
theorem R_nest2 {c d : Clause} (hd : (svars d).length = 2) (h1 : smin d ≤ smin c)
    (h2 : smax c ≤ smax d) : R c d := by
  intro _
  left
  unfold smin at h1
  unfold smax at h2
  rw [headD_eq (show 0 < (svars d).length by omega)] at h1
  rw [getLastD_eq (show 0 < (svars d).length by omega)] at h2
  refine ⟨0, by omega, h1, ?_⟩
  simpa [hd] using h2

/-- Laminarity is invariant under shifts. -/
theorem lamRaw_shift {a b : List Nat} (o : Nat) (ha : a ≠ []) (hb : b ≠ []) (h : LamRaw a b) :
    LamRaw (a.map (o + ·)) (b.map (o + ·)) := by
  have ha' : 0 < a.length := List.length_pos_iff.mpr ha
  have hb' : 0 < b.length := List.length_pos_iff.mpr hb
  have hd : ∀ l : List Nat, 0 < l.length → (l.map (o + ·)).headD 0 = o + l.headD 0 := by
    intro l hl
    rw [headD_eq (by simpa using hl), headD_eq hl, List.getElem_map]
  have hl : ∀ l : List Nat, 0 < l.length → (l.map (o + ·)).getLastD 0 = o + l.getLastD 0 := by
    intro l hl
    rw [getLastD_eq (by simpa using hl), getLastD_eq hl, List.getElem_map]
    simp
  unfold LamRaw NestRaw DisjRaw at h ⊢
  rw [hd a ha', hd b hb', hl a ha', hl b hb']
  rcases h with ⟨t, ht, c1, c2⟩ | ⟨t, ht, c1, c2⟩ | c
  · left
    exact ⟨t, by simpa using ht, by rw [List.getElem_map]; omega, by rw [List.getElem_map]; omega⟩
  · right; left
    exact ⟨t, by simpa using ht, by rw [List.getElem_map]; omega, by rw [List.getElem_map]; omega⟩
  · right; right; omega

/-! ## Shapes of the clauses -/

/-- A list of positions increasing with at least two entries. -/
theorem inst_facts {c : TCl} (h2 : 2 ≤ c.1.length) (hinc : (tpos c).Pairwise (· < ·))
    (o : Nat) (odd : Bool) :
    sideOf (inst o odd c) = (c.2 != odd) ∧ svars (inst o odd c) = (tpos c).map (o + ·) := by
  have hl : (tpos c).length = c.1.length := by simp [tpos]
  have h01 : (tpos c)[0]'(by omega) < (tpos c)[1]'(by omega) :=
    List.pairwise_iff_getElem.mp hinc 0 1 (by omega) (by omega) (by omega)
  have hvars : (c.1.map (fun l => (⟨o + l.1, l.2⟩ : Literal))).map Literal.var =
      (tpos c).map (o + ·) := by simp [tpos]
  unfold inst
  by_cases hs : (c.2 != odd) = true
  · rw [ite_eq_left hs]
    have hside : sideOf (c.1.map (fun l => (⟨o + l.1, l.2⟩ : Literal))) = true := by
      unfold sideOf
      simp only [List.getElem?_map, decide_eq_true_eq]
      rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega)]
      simp only [Option.map_some, Option.getD_some]
      have := h01
      simp only [tpos, List.getElem_map] at this
      omega
    refine ⟨by rw [hside, hs], ?_⟩
    unfold svars; rw [hside, ite_eq_left rfl, hvars]
  · rw [ite_eq_right hs]
    have hside : sideOf (c.1.map (fun l => (⟨o + l.1, l.2⟩ : Literal))).reverse = false := by
      unfold sideOf
      simp only [decide_eq_false_iff_not, Nat.not_lt]
      rw [List.getElem?_reverse (by simp; omega), List.getElem?_reverse (by simp; omega)]
      simp only [List.length_map, List.getElem?_map]
      rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega)]
      simp only [Option.map_some, Option.getD_some]
      have := List.pairwise_iff_getElem.mp hinc (c.1.length - 1 - 1) (c.1.length - 1 - 0)
        (by omega) (by omega) (by omega)
      simp only [tpos, List.getElem_map] at this
      omega
    simp only [Bool.not_eq_true] at hs
    refine ⟨by rw [hside, hs], ?_⟩
    unfold svars
    rw [hside]
    simp only [Bool.false_eq_true, ite_false, List.map_reverse, List.reverse_reverse]
    exact hvars

/-- Shape facts of a cell clause. -/
theorem cell_facts {bp bn : Bool} {t : TCl} (ht : t ∈ cellT bp bn) (o : Nat) (odd : Bool) :
    sideOf (inst o odd t) = (t.2 != odd) ∧ svars (inst o odd t) = (tpos t).map (o + ·) ∧
      o ≤ smin (inst o odd t) ∧ smin (inst o odd t) < smax (inst o odd t) ∧
      smax (inst o odd t) ≤ o + 9 ∧
      (t.2 = false → ¬ (smin (inst o odd t) < o + 1 ∧ o + 1 < smax (inst o odd t))) ∧
      (t.2 = true → ¬ (smin (inst o odd t) < o + 8 ∧ o + 8 < smax (inst o odd t))) := by
  obtain ⟨h2, h3, hinc, hlt, hp0, hp1⟩ := cellT_shape bp bn t ht
  obtain ⟨hs, hv⟩ := inst_facts h2 hinc o odd
  have hl : (tpos t).length = t.1.length := by simp [tpos]
  have hhd : smin (inst o odd t) = o + (tpos t).headD 0 := by
    unfold smin; rw [hv]
    cases h : tpos t with
    | nil => simp [h] at hl; omega
    | cons x l => simp
  have hlast : smax (inst o odd t) = o + (tpos t).getLastD 0 := by
    unfold smax; rw [hv, List.getLastD_eq_getLast?, List.getLastD_eq_getLast?, List.getLast?_map]
    cases h : (tpos t).getLast? with
    | none => simp [List.getLast?_eq_none_iff] at h; simp [h] at hl; omega
    | some x => simp
  have hhd' : (tpos t).headD 0 = (tpos t)[0]'(by omega) := by
    rw [List.headD_eq_head?_getD, List.head?_eq_getElem?, List.getElem?_eq_getElem (by omega)]; rfl
  have hlast' : (tpos t).getLastD 0 = (tpos t)[(tpos t).length - 1]'(by omega) := by
    rw [List.getLastD_eq_getLast?, List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)]
    rfl
  have hlt0 := List.pairwise_iff_getElem.mp hinc 0 ((tpos t).length - 1) (by omega) (by omega)
    (by omega)
  have hle9 := hlt _ (List.getElem_mem (show (tpos t).length - 1 < (tpos t).length by omega))
  refine ⟨hs, hv, by omega, by rw [hhd, hlast, hhd', hlast']; omega, by rw [hlast, hlast']; omega,
    ?_, ?_⟩
  · intro hp ⟨c1, c2⟩; exact hp0 hp ⟨by omega, by omega⟩
  · intro hp ⟨c1, c2⟩; exact hp1 hp ⟨by omega, by omega⟩

/-- Facts of a two-literal clause with increasing or decreasing variables. -/
theorem two_facts {a b : Nat} {s1 s2 : Bool} (hab : a < b) :
    sideOf [⟨a, s1⟩, ⟨b, s2⟩] = true ∧ svars [⟨a, s1⟩, ⟨b, s2⟩] = [a, b] ∧
      sideOf [⟨b, s1⟩, ⟨a, s2⟩] = false ∧ svars [⟨b, s1⟩, ⟨a, s2⟩] = [a, b] := by
  have h1 : sideOf [⟨a, s1⟩, ⟨b, s2⟩] = true := by simp [sideOf, hab]
  have h2 : sideOf [⟨b, s1⟩, ⟨a, s2⟩] = false := by simp [sideOf]; omega
  refine ⟨h1, ?_, h2, ?_⟩
  · simp [svars, h1]
  · simp [svars, h2]


/-! ## Layout arithmetic -/

theorem colBase_succ (W j : Nat) : colBase W (j + 1) = colBase W j + (9 * W + 3) := by
  unfold colBase colLen; rw [Nat.succ_mul]

theorem colBase_lt {W j j' : Nat} (h : j < j') : colBase W j + (9 * W + 3) ≤ colBase W j' := by
  rw [← colBase_succ]
  unfold colBase
  exact Nat.mul_le_mul_right _ h

/-! ## Clauses of a column -/

theorem start_facts {W j : Nat} {c : Clause} (hc : c ∈ startG W j) :
    smin c = colBase W j ∧ smax c = colBase W j + 1 ∧ (svars c).length = 2 := by
  have := two_facts (a := colBase W j) (b := colBase W j + 1) (s1 := false) (s2 := false) (by omega)
  have := two_facts (a := colBase W j) (b := colBase W j + 1) (s1 := true) (s2 := false) (by omega)
  unfold startG at hc
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hc
  rcases hc with rfl | rfl <;> simp_all [smin, smax]

theorem end_facts {W j : Nat} {c : Clause} (hc : c ∈ endG W j) :
    smin c = cellOff W j W ∧ smax c = cellOff W j W + 1 ∧ (svars c).length = 2 := by
  have := two_facts (a := cellOff W j W) (b := cellOff W j W + 1) (s1 := true) (s2 := true)
    (by omega)
  have := two_facts (a := cellOff W j W) (b := cellOff W j W + 1) (s1 := false) (s2 := true)
    (by omega)
  unfold endG at hc
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hc
  rcases hc with rfl | rfl <;> simp_all [smin, smax]

theorem mem_column {W j : Nat} {odd : Bool} {bits : Nat → Nat → Bool × Bool} {c : Clause}
    (hc : c ∈ column W j odd bits) :
    c ∈ startG W j ∨
      (∃ idx, idx < W ∧ ∃ t ∈ cellT (bits j (row W odd idx)).1 (bits j (row W odd idx)).2,
        c = inst (cellOff W j idx) odd t) ∨ c ∈ endG W j := by
  unfold column at hc
  simp only [List.mem_append, List.mem_flatMap, List.mem_reverse, List.mem_range] at hc
  rcases hc with (hc | ⟨idx, hidx, hc⟩) | hc
  · exact Or.inl hc
  · unfold cellCNF at hc
    rw [List.mem_map] at hc
    obtain ⟨t, ht, rfl⟩ := hc
    exact Or.inr (Or.inl ⟨idx, hidx, t, ht, rfl⟩)
  · exact Or.inr (Or.inr hc)

/-- Every clause of a column lies within the column. -/
theorem column_span {W j : Nat} {odd : Bool} {bits : Nat → Nat → Bool × Bool} {c : Clause}
    (hc : c ∈ column W j odd bits) :
    colBase W j ≤ smin c ∧ smin c < smax c ∧ smax c ≤ cellOff W j W + 1 := by
  rcases mem_column hc with h | ⟨idx, hidx, t, ht, rfl⟩ | h
  · have := start_facts h; unfold cellOff; omega
  · have := cell_facts ht (cellOff W j idx) odd
    unfold cellOff at this ⊢; omega
  · have := end_facts h; unfold cellOff at this ⊢; omega

/-- Two clauses in different columns are laminar. -/
theorem R_columns {W j j' : Nat} {odd odd' : Bool} {bits : Nat → Nat → Bool × Bool}
    {c d : Clause} (hc : c ∈ column W j odd bits) (hd : d ∈ column W j' odd' bits)
    (hne : j ≠ j') : R c d := by
  have a := column_span hc
  have b := column_span hd
  apply R_disj
  unfold cellOff at a b
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · have := colBase_lt (W := W) h; left; omega
  · have := colBase_lt (W := W) h; right; omega

/-- A cell is laminar. -/
theorem cell_pairwise (o : Nat) (odd bp bn : Bool) :
    ((cellT bp bn).map (inst o odd)).Pairwise R := by
  rw [List.pairwise_map]
  apply (cellT_lam bp bn).imp_of_mem
  intro t1 t2 h1 h2 hl hs
  obtain ⟨s1, v1, _⟩ := cell_facts h1 o odd
  obtain ⟨s2, v2, _⟩ := cell_facts h2 o odd
  rw [s1, s2] at hs
  have hp : t1.2 = t2.2 := by cases h3 : t1.2 <;> cases h4 : t2.2 <;> cases odd <;> simp_all
  rw [v1, v2]
  have n1 : tpos t1 ≠ [] := by
    have := (cellT_shape bp bn t1 h1).1
    intro e
    have hl : (tpos t1).length = t1.1.length := by simp [tpos]
    rw [e] at hl; simp at hl; omega
  have n2 : tpos t2 ≠ [] := by
    have := (cellT_shape bp bn t2 h2).1
    intro e
    have hl : (tpos t2).length = t2.1.length := by simp [tpos]
    rw [e] at hl; simp at hl; omega
  exact lamRaw_shift o n1 n2 (lamRaw_of_lamB (hl hp))

theorem pairwise_of_ne {α : Type} {P : α → α → Prop} {l : List α} (hnd : l.Nodup)
    (h : ∀ a ∈ l, ∀ b ∈ l, a ≠ b → P a b) : l.Pairwise P :=
  hnd.imp_of_mem (fun ha hb hab => h _ ha _ hb hab)

/-- A column is laminar. -/
theorem column_pairwise (W j : Nat) (odd : Bool) (bits : Nat → Nat → Bool × Bool) :
    (column W j odd bits).Pairwise R := by
  unfold column
  rw [List.pairwise_append, List.pairwise_append]
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · unfold startG
    refine List.Pairwise.cons ?_ (List.pairwise_singleton _ _)
    intro y hy
    rw [List.mem_singleton] at hy
    subst hy
    apply R_side
    have := two_facts (a := colBase W j) (b := colBase W j + 1) (s1 := false) (s2 := false)
      (by omega)
    have := two_facts (a := colBase W j) (b := colBase W j + 1) (s1 := true) (s2 := false)
      (by omega)
    simp_all
  · rw [List.pairwise_flatMap]
    refine ⟨fun idx _ => cell_pairwise _ _ _ _, ?_⟩
    apply pairwise_of_ne (List.pairwise_reverse.mpr (List.nodup_range.imp fun h => Ne.symm h))
    intro i1 h1 i2 h2 hne x hx y hy
    simp only [List.mem_reverse, List.mem_range] at h1 h2
    unfold cellCNF at hx hy
    rw [List.mem_map] at hx hy
    obtain ⟨t1, ht1, rfl⟩ := hx
    obtain ⟨t2, ht2, rfl⟩ := hy
    have a := cell_facts ht1 (cellOff W j i1) odd
    have b := cell_facts ht2 (cellOff W j i2) odd
    apply R_disj
    unfold cellOff at a b ⊢
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · left; omega
    · right; omega
  · intro x hx y hy
    obtain ⟨a1, a2, _⟩ := start_facts hx
    simp only [List.mem_flatMap, List.mem_reverse, List.mem_range] at hy
    obtain ⟨idx, _, hy⟩ := hy
    unfold cellCNF at hy
    rw [List.mem_map] at hy
    obtain ⟨t, ht, rfl⟩ := hy
    have b := cell_facts ht (cellOff W j idx) odd
    apply R_disj; unfold cellOff at b ⊢; left; omega
  · unfold endG
    refine List.Pairwise.cons ?_ (List.pairwise_singleton _ _)
    intro y hy
    rw [List.mem_singleton] at hy
    subst hy
    apply R_side
    have := two_facts (a := cellOff W j W) (b := cellOff W j W + 1) (s1 := true) (s2 := true)
      (by omega)
    have := two_facts (a := cellOff W j W) (b := cellOff W j W + 1) (s1 := false) (s2 := true)
      (by omega)
    simp_all
  · intro x hx y hy
    obtain ⟨b1, b2, _⟩ := end_facts hy
    simp only [List.mem_append, List.mem_flatMap, List.mem_reverse, List.mem_range] at hx
    rcases hx with hx | ⟨idx, hidx, hx⟩
    · obtain ⟨a1, a2, _⟩ := start_facts hx
      apply R_disj; unfold cellOff at b1; left; omega
    · unfold cellCNF at hx
      rw [List.mem_map] at hx
      obtain ⟨t, ht, rfl⟩ := hx
      have a := cell_facts ht (cellOff W j idx) odd
      apply R_disj; unfold cellOff at a b1 ⊢; left; omega

/-! ## Rainbows -/

theorem cellOff_lt_next {W j iL : Nat} (hiL : iL < W) :
    cellOff W j iL + 9 ≤ cellOff W j W ∧ cellOff W j W + 2 ≤ colBase W (j + 1) := by
  have := colBase_succ W j
  unfold cellOff; omega

theorem rbEven_facts {W j v : Nat} (hv : v < W) {c : Clause} (hc : c ∈ rbEven W j v) :
    smin c = cellOff W j v + 8 ∧ smax c = cellOff W (j + 1) (W - 1 - v) + 1 ∧
      (svars c).length = 2 ∧ sideOf c = true := by
  have h1 := cellOff_lt_next (W := W) (j := j) hv
  have hlt : cellOff W j v + 8 < cellOff W (j + 1) (W - 1 - v) + 1 := by
    have := colBase_succ W j; unfold cellOff at h1 ⊢; omega
  have a := two_facts (s1 := false) (s2 := true) hlt
  have b := two_facts (s1 := true) (s2 := false) hlt
  unfold rbEven at hc
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hc
  rcases hc with rfl | rfl <;> simp_all [smin, smax]

theorem rbOdd_facts {W j v : Nat} (hv : v < W) {c : Clause} (hc : c ∈ rbOdd W j v) :
    smin c = cellOff W j (W - 1 - v) + 8 ∧ smax c = cellOff W (j + 1) v + 1 ∧
      (svars c).length = 2 ∧ sideOf c = false := by
  have h1 := cellOff_lt_next (W := W) (j := j) (iL := W - 1 - v) (by omega)
  have hlt : cellOff W j (W - 1 - v) + 8 < cellOff W (j + 1) v + 1 := by
    have := colBase_succ W j; unfold cellOff at h1 ⊢; omega
  have a := two_facts (s1 := true) (s2 := false) hlt
  have b := two_facts (s1 := false) (s2 := true) hlt
  unfold rbOdd at hc
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hc
  rcases hc with rfl | rfl <;> simp_all [smin, smax]

/-- **A column clause against a rainbow clause.** -/
theorem col_rb {W j : Nat} {odd : Bool} {bits : Nat → Nat → Bool × Bool} {c d : Clause}
    (hc : c ∈ column W j odd bits) {jL iL iR : Nat} (hiL : iL < W) (hiR : iR < W)
    (hd2 : (svars d).length = 2) (hdmin : smin d = cellOff W jL iL + 8)
    (hdmax : smax d = cellOff W (jL + 1) iR + 1)
    (hL : j = jL → sideOf d = !odd) (hR : j = jL + 1 → sideOf d = odd) : R c d := by
  have sp := column_span hc
  have n1 := cellOff_lt_next (j := jL) hiL
  have n2 := cellOff_lt_next (j := jL + 1) hiR
  have s1 := colBase_succ W jL
  have s2 := colBase_succ W (jL + 1)
  rcases Nat.lt_or_ge j jL with h1 | h1
  · have := colBase_lt (W := W) h1
    apply R_disj; left; unfold cellOff at sp hdmin n1; omega
  rcases Nat.lt_or_ge (jL + 1) j with h2 | h2
  · have := colBase_lt (W := W) h2
    apply R_disj; right; unfold cellOff at sp hdmax n2; omega
  rcases Nat.lt_or_ge jL j with h3 | h3
  · -- the column to the right
    have hj : j = jL + 1 := by omega
    subst hj
    rcases mem_column hc with hs | ⟨idx, hidx, t, ht, rfl⟩ | he
    · have := start_facts hs
      apply R_nest2 hd2 <;> unfold cellOff at hdmin hdmax n1 n2 <;> omega
    · have cf := cell_facts ht (cellOff W (jL + 1) idx) odd
      rcases Nat.lt_trichotomy idx iR with c1 | c1 | c1
      · apply R_nest2 hd2 <;> unfold cellOff at cf hdmin hdmax n1 n2 ⊢ <;> omega
      · subst c1
        by_cases hsd : sideOf (inst (cellOff W (jL + 1) idx) odd t) = sideOf d
        · have hpage : t.2 = false := by
            have := hR rfl
            rw [cf.1] at hsd
            rw [this] at hsd
            cases h5 : t.2 <;> cases odd <;> simp_all
          have := cf.2.2.2.2.2.1 hpage
          rcases Nat.lt_or_ge (cellOff W (jL + 1) idx + 1) (smax (inst (cellOff W (jL + 1) idx)
            odd t)) with c2 | c2
          · apply R_disj; right; rw [hdmax]; omega
          · apply R_nest2 hd2
            · rw [hdmin]; unfold cellOff at cf n1 ⊢; omega
            · rw [hdmax]; exact c2
        · exact R_side hsd
      · apply R_disj; right; rw [hdmax]; unfold cellOff at cf ⊢; omega
    · have := end_facts he
      apply R_disj; right; rw [hdmax]; unfold cellOff at this n2 ⊢; omega
  · -- the column to the left
    have hj : j = jL := by omega
    subst hj
    rcases mem_column hc with hs | ⟨idx, hidx, t, ht, rfl⟩ | he
    · have := start_facts hs
      apply R_disj; left; rw [hdmin]; unfold cellOff at this ⊢; omega
    · have cf := cell_facts ht (cellOff W j idx) odd
      rcases Nat.lt_trichotomy idx iL with c1 | c1 | c1
      · apply R_disj; left; rw [hdmin]; unfold cellOff at cf ⊢; omega
      · subst c1
        by_cases hsd : sideOf (inst (cellOff W j idx) odd t) = sideOf d
        · have hpage : t.2 = true := by
            have := hL rfl
            rw [cf.1] at hsd
            rw [this] at hsd
            cases h5 : t.2 <;> cases odd <;> simp_all
          have := cf.2.2.2.2.2.2 hpage
          rcases Nat.lt_or_ge (smin (inst (cellOff W j idx) odd t)) (cellOff W j idx + 8)
            with c2 | c2
          · apply R_disj; left; rw [hdmin]; omega
          · apply R_nest2 hd2
            · rw [hdmin]; exact c2
            · rw [hdmax]; unfold cellOff at cf n1 n2 ⊢; omega
        · exact R_side hsd
      · apply R_nest2 hd2 <;> unfold cellOff at cf hdmin hdmax n1 n2 ⊢ <;> omega
    · have := end_facts he
      apply R_nest2 hd2 <;> unfold cellOff at this hdmin hdmax n1 n2 <;> omega

/-- Two-variable clauses with nested spans. -/
theorem R_two {c d : Clause} (hc : (svars c).length = 2) (hd : (svars d).length = 2)
    (h : (smin d ≤ smin c ∧ smax c ≤ smax d) ∨ (smin c ≤ smin d ∧ smax d ≤ smax c) ∨
      smax c ≤ smin d ∨ smax d ≤ smin c) : R c d := by
  rcases h with ⟨a, b⟩ | ⟨a, b⟩ | h | h
  · exact R_nest2 hd a b
  · exact R_symm (R_nest2 hc a b)
  · exact R_disj (Or.inl h)
  · exact R_disj (Or.inr h)

/-! ## Lists of pieces -/

theorem pairwise_of_all {α : Type} {P : α → α → Prop} :
    ∀ {l : List α}, (∀ x ∈ l, ∀ y ∈ l, P x y) → l.Pairwise P
  | [], _ => List.Pairwise.nil
  | _ :: _, h => List.Pairwise.cons
      (fun y hy => h _ List.mem_cons_self y (List.mem_cons_of_mem _ hy))
      (pairwise_of_all fun x hx y hy => h x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy))

theorem pairwise_range_flatMap {α : Type} {P : α → α → Prop} (n : Nat) (F : Nat → List α)
    (h1 : ∀ k, k < n → (F k).Pairwise P)
    (h2 : ∀ k k', k < n → k' < n → k ≠ k' → ∀ x ∈ F k, ∀ y ∈ F k', P x y) :
    ((List.range n).reverse.flatMap F).Pairwise P := by
  rw [List.pairwise_flatMap]
  refine ⟨fun k hk => h1 k (by simpa using hk), ?_⟩
  apply pairwise_of_ne (List.pairwise_reverse.mpr (List.nodup_range.imp fun h => Ne.symm h))
  intro k hk k' hk' hne
  simp only [List.mem_reverse, List.mem_range] at hk hk'
  exact h2 k k' hk hk' hne

theorem mem_range_flatMap {α : Type} {n : Nat} {F : Nat → List α} {x : α} :
    x ∈ (List.range n).reverse.flatMap F ↔ ∃ k, k < n ∧ x ∈ F k := by
  simp only [List.mem_flatMap, List.mem_reverse, List.mem_range]

theorem mem_ite_nil {α : Type} {p : Prop} [Decidable p] {l : List α} {x : α} :
    x ∈ (if p then l else []) ↔ p ∧ x ∈ l := by
  split <;> simp_all

/-! ## The four parts of the grid formula -/

/-- The even columns. -/
def colsE (W m : Nat) (bits : Nat → Nat → Bool × Bool) : CNF :=
  (List.range m).reverse.flatMap fun k =>
    if 2 * k + 1 ≤ m then column W (2 * k) false bits else []

/-- The odd columns. -/
def colsO (W m : Nat) (bits : Nat → Nat → Bool × Bool) : CNF :=
  (List.range m).reverse.flatMap fun k =>
    if 2 * k + 2 ≤ m then column W (2 * k + 1) true bits else []

/-- The rainbows on top. -/
def rbsE (W m : Nat) : CNF :=
  (List.range m).reverse.flatMap fun k =>
    if 2 * k + 2 ≤ m then (List.range W).reverse.flatMap (rbEven W (2 * k)) else []

/-- The rainbows below. -/
def rbsO (W m : Nat) : CNF :=
  (List.range m).reverse.flatMap fun k =>
    if 2 * k + 3 ≤ m then (List.range W).reverse.flatMap (rbOdd W (2 * k + 1)) else []

theorem gridCNF_eq (W m : Nat) (bits : Nat → Nat → Bool × Bool) :
    gridCNF W m bits = colsE W m bits ++ colsO W m bits ++ rbsE W m ++ rbsO W m := rfl

theorem mem_colsE {W m : Nat} {bits : Nat → Nat → Bool × Bool} {x : Clause} :
    x ∈ colsE W m bits ↔ ∃ k, 2 * k + 1 ≤ m ∧ x ∈ column W (2 * k) false bits := by
  unfold colsE; rw [mem_range_flatMap]
  constructor
  · rintro ⟨k, _, hx⟩; rw [mem_ite_nil] at hx; exact ⟨k, hx⟩
  · rintro ⟨k, hk, hx⟩; exact ⟨k, by omega, mem_ite_nil.mpr ⟨hk, hx⟩⟩

theorem mem_colsO {W m : Nat} {bits : Nat → Nat → Bool × Bool} {x : Clause} :
    x ∈ colsO W m bits ↔ ∃ k, 2 * k + 2 ≤ m ∧ x ∈ column W (2 * k + 1) true bits := by
  unfold colsO; rw [mem_range_flatMap]
  constructor
  · rintro ⟨k, _, hx⟩; rw [mem_ite_nil] at hx; exact ⟨k, hx⟩
  · rintro ⟨k, hk, hx⟩; exact ⟨k, by omega, mem_ite_nil.mpr ⟨hk, hx⟩⟩

theorem mem_rbsE {W m : Nat} {x : Clause} :
    x ∈ rbsE W m ↔ ∃ k, 2 * k + 2 ≤ m ∧ ∃ v, v < W ∧ x ∈ rbEven W (2 * k) v := by
  unfold rbsE; rw [mem_range_flatMap]
  constructor
  · rintro ⟨k, _, hx⟩; rw [mem_ite_nil, mem_range_flatMap] at hx; exact ⟨k, hx⟩
  · rintro ⟨k, hk, hx⟩
    exact ⟨k, by omega, mem_ite_nil.mpr ⟨hk, mem_range_flatMap.mpr hx⟩⟩

theorem mem_rbsO {W m : Nat} {x : Clause} :
    x ∈ rbsO W m ↔ ∃ k, 2 * k + 3 ≤ m ∧ ∃ v, v < W ∧ x ∈ rbOdd W (2 * k + 1) v := by
  unfold rbsO; rw [mem_range_flatMap]
  constructor
  · rintro ⟨k, _, hx⟩; rw [mem_ite_nil, mem_range_flatMap] at hx; exact ⟨k, hx⟩
  · rintro ⟨k, hk, hx⟩
    exact ⟨k, by omega, mem_ite_nil.mpr ⟨hk, mem_range_flatMap.mpr hx⟩⟩

/-! ## Laminarity of the grid formula -/

theorem rbEven_group (W j : Nat) : ((List.range W).reverse.flatMap (rbEven W j)).Pairwise R := by
  have := colBase_succ W j
  apply pairwise_range_flatMap
  · intro v hv
    apply pairwise_of_all
    intro x hx y hy
    have a := rbEven_facts hv hx
    have b := rbEven_facts hv hy
    exact R_two a.2.2.1 b.2.2.1 (Or.inl ⟨by omega, by omega⟩)
  · intro v v' hv hv' hne x hx y hy
    have a := rbEven_facts hv hx
    have b := rbEven_facts hv' hy
    apply R_two a.2.2.1 b.2.2.1
    rw [a.1, a.2.1, b.1, b.2.1]
    unfold cellOff
    omega

theorem rbOdd_group (W j : Nat) : ((List.range W).reverse.flatMap (rbOdd W j)).Pairwise R := by
  have := colBase_succ W j
  apply pairwise_range_flatMap
  · intro v hv
    apply pairwise_of_all
    intro x hx y hy
    have a := rbOdd_facts hv hx
    have b := rbOdd_facts hv hy
    exact R_two a.2.2.1 b.2.2.1 (Or.inl ⟨by omega, by omega⟩)
  · intro v v' hv hv' hne x hx y hy
    have a := rbOdd_facts hv hx
    have b := rbOdd_facts hv' hy
    apply R_two a.2.2.1 b.2.2.1
    rw [a.1, a.2.1, b.1, b.2.1]
    unfold cellOff
    omega

theorem colsE_pairwise (W m : Nat) (bits : Nat → Nat → Bool × Bool) :
    (colsE W m bits).Pairwise R := by
  apply pairwise_range_flatMap
  · intro k _
    split
    · exact column_pairwise _ _ _ _
    · exact List.Pairwise.nil
  · intro k k' _ _ hne x hx y hy
    simp only [mem_ite_nil] at hx hy
    exact R_columns hx.2 hy.2 (by omega)

theorem colsO_pairwise (W m : Nat) (bits : Nat → Nat → Bool × Bool) :
    (colsO W m bits).Pairwise R := by
  apply pairwise_range_flatMap
  · intro k _
    split
    · exact column_pairwise _ _ _ _
    · exact List.Pairwise.nil
  · intro k k' _ _ hne x hx y hy
    simp only [mem_ite_nil] at hx hy
    exact R_columns hx.2 hy.2 (by omega)

theorem rbsE_pairwise (W m : Nat) : (rbsE W m).Pairwise R := by
  apply pairwise_range_flatMap
  · intro k _
    split
    · exact rbEven_group W (2 * k)
    · exact List.Pairwise.nil
  · intro k k' _ _ hne x hx y hy
    simp only [mem_ite_nil, mem_range_flatMap] at hx hy
    obtain ⟨_, v, hv, hx⟩ := hx
    obtain ⟨_, v', hv', hy⟩ := hy
    have a := rbEven_facts hv hx
    have b := rbEven_facts hv' hy
    apply R_disj
    rw [a.1, a.2.1, b.1, b.2.1]
    have s1 := colBase_succ W (2 * k)
    have s2 := colBase_succ W (2 * k')
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · have := colBase_lt (W := W) (show 2 * k + 1 < 2 * k' by omega)
      unfold cellOff; omega
    · have := colBase_lt (W := W) (show 2 * k' + 1 < 2 * k by omega)
      unfold cellOff; omega

theorem rbsO_pairwise (W m : Nat) : (rbsO W m).Pairwise R := by
  apply pairwise_range_flatMap
  · intro k _
    split
    · exact rbOdd_group W (2 * k + 1)
    · exact List.Pairwise.nil
  · intro k k' _ _ hne x hx y hy
    simp only [mem_ite_nil, mem_range_flatMap] at hx hy
    obtain ⟨_, v, hv, hx⟩ := hx
    obtain ⟨_, v', hv', hy⟩ := hy
    have a := rbOdd_facts hv hx
    have b := rbOdd_facts hv' hy
    apply R_disj
    rw [a.1, a.2.1, b.1, b.2.1]
    have s1 := colBase_succ W (2 * k + 1)
    have s2 := colBase_succ W (2 * k' + 1)
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · have := colBase_lt (W := W) (show 2 * k + 1 + 1 < 2 * k' + 1 by omega)
      unfold cellOff; omega
    · have := colBase_lt (W := W) (show 2 * k' + 1 + 1 < 2 * k + 1 by omega)
      unfold cellOff; omega

theorem col_rbEven {W j k v : Nat} {odd : Bool} {bits : Nat → Nat → Bool × Bool} {c d : Clause}
    (hc : c ∈ column W j odd bits) (hpar : odd = true ↔ j % 2 = 1) (hv : v < W)
    (hd : d ∈ rbEven W (2 * k) v) : R c d := by
  obtain ⟨h1, h2, h3, h4⟩ := rbEven_facts hv hd
  apply col_rb hc hv (show W - 1 - v < W by omega) h3 h1 h2
  · intro hj; rw [h4]; cases odd
    · rfl
    · have := hpar.mp rfl; omega
  · intro hj; rw [h4]; cases odd
    · have := hpar.mpr (by omega); simp at this
    · rfl

theorem col_rbOdd {W j k v : Nat} {odd : Bool} {bits : Nat → Nat → Bool × Bool} {c d : Clause}
    (hc : c ∈ column W j odd bits) (hpar : odd = true ↔ j % 2 = 1) (hv : v < W)
    (hd : d ∈ rbOdd W (2 * k + 1) v) : R c d := by
  obtain ⟨h1, h2, h3, h4⟩ := rbOdd_facts hv hd
  apply col_rb hc (show W - 1 - v < W by omega) hv h3 h1 h2
  · intro hj; rw [h4]; cases odd
    · have := hpar.mpr (by omega); simp at this
    · rfl
  · intro hj; rw [h4]; cases odd
    · rfl
    · have := hpar.mp rfl; omega

/-- Membership in one of the two column parts. -/
theorem mem_cols {W m : Nat} {bits : Nat → Nat → Bool × Bool} {x : Clause}
    (hx : x ∈ colsE W m bits ∨ x ∈ colsO W m bits) :
    ∃ j, j < m ∧ ∃ odd : Bool, (odd = true ↔ j % 2 = 1) ∧ x ∈ column W j odd bits := by
  rcases hx with hx | hx
  · obtain ⟨k, hk, hx⟩ := mem_colsE.mp hx
    exact ⟨2 * k, by omega, false, ⟨fun h => by simp at h, fun h => by omega⟩, hx⟩
  · obtain ⟨k, hk, hx⟩ := mem_colsO.mp hx
    exact ⟨2 * k + 1, by omega, true, ⟨fun _ => by omega, fun _ => rfl⟩, hx⟩

/-- **The grid formula is laminar.** -/
theorem grid_pairwise (W m : Nat) (bits : Nat → Nat → Bool × Bool) :
    (gridCNF W m bits).Pairwise R := by
  rw [gridCNF_eq, List.pairwise_append, List.pairwise_append, List.pairwise_append]
  refine ⟨⟨⟨colsE_pairwise W m bits, colsO_pairwise W m bits, ?_⟩, rbsE_pairwise W m, ?_⟩,
    rbsO_pairwise W m, ?_⟩
  · intro x hx y hy
    obtain ⟨k, _, hx⟩ := mem_colsE.mp hx
    obtain ⟨k', _, hy⟩ := mem_colsO.mp hy
    exact R_columns hx hy (by omega)
  · intro x hx y hy
    rw [List.mem_append] at hx
    obtain ⟨j, _, odd, hpar, hx⟩ := mem_cols hx
    obtain ⟨k, _, v, hv, hy⟩ := mem_rbsE.mp hy
    exact col_rbEven hx hpar hv hy
  · intro x hx y hy
    obtain ⟨k, _, v, hv, hy⟩ := mem_rbsO.mp hy
    rw [List.mem_append, List.mem_append] at hx
    rcases hx with hx | hx
    · obtain ⟨j, _, odd, hpar, hx⟩ := mem_cols hx
      exact col_rbOdd hx hpar hv hy
    · obtain ⟨k', _, v', hv', hx⟩ := mem_rbsE.mp hx
      apply R_side
      rw [(rbEven_facts hv' hx).2.2.2, (rbOdd_facts hv hy).2.2.2]
      decide

/-! ## Shapes -/

theorem sorted_two {c : Clause} (h : (svars c).length = 2) (hlt : smin c < smax c) :
    2 ≤ (svars c).length ∧ (svars c).Pairwise (· < ·) := by
  unfold smin smax at hlt
  refine ⟨by omega, ?_⟩
  generalize svars c = l at h hlt ⊢
  match l, h with
  | [a, b], _ =>
    simp only [List.headD_cons, List.getLastD_eq_getLast?, List.getLast?_cons_cons,
      List.getLast?_singleton, Option.getD_some] at hlt
    simpa using hlt

theorem column_clause_ok {W j : Nat} {odd : Bool} {bits : Nat → Nat → Bool × Bool} {c : Clause}
    (hc : c ∈ column W j odd bits) : 2 ≤ (svars c).length ∧ (svars c).Pairwise (· < ·) := by
  rcases mem_column hc with h | ⟨idx, _, t, ht, rfl⟩ | h
  · have := start_facts h; exact sorted_two this.2.2 (by omega)
  · obtain ⟨h2, _, hinc, _⟩ := cellT_shape _ _ t ht
    obtain ⟨_, hv⟩ := inst_facts h2 hinc (cellOff W j idx) odd
    rw [hv]
    exact ⟨by simpa [tpos] using h2, List.pairwise_map.mpr (hinc.imp fun h => Nat.add_lt_add_left h _)⟩
  · have := end_facts h; exact sorted_two this.2.2 (by omega)

theorem grid_clause_ok {W m : Nat} {bits : Nat → Nat → Bool × Bool} {c : Clause}
    (hc : c ∈ gridCNF W m bits) : 2 ≤ (svars c).length ∧ (svars c).Pairwise (· < ·) := by
  rw [gridCNF_eq] at hc
  simp only [List.mem_append] at hc
  rcases hc with ((hc | hc) | hc) | hc
  · obtain ⟨_, _, _, _, hc⟩ := mem_cols (Or.inl hc); exact column_clause_ok hc
  · obtain ⟨_, _, _, _, hc⟩ := mem_cols (Or.inr hc); exact column_clause_ok hc
  · obtain ⟨k, _, v, hv, hc⟩ := mem_rbsE.mp hc
    have a := rbEven_facts hv hc
    have := colBase_succ W (2 * k)
    exact sorted_two a.2.2.1 (by rw [a.1, a.2.1]; unfold cellOff; omega)
  · obtain ⟨k, _, v, hv, hc⟩ := mem_rbsO.mp hc
    have a := rbOdd_facts hv hc
    have := colBase_succ W (2 * k + 1)
    exact sorted_two a.2.2.1 (by rw [a.1, a.2.1]; unfold cellOff; omega)

theorem shape_of {K : Nat} {c : Clause} (h2 : 2 ≤ c.length) (hs : (svars c).Pairwise (· < ·))
    (hK : ∀ l ∈ c, l.var < K) : Shape K c := by
  refine ⟨h2, hK, ?_⟩
  unfold svars at hs
  cases h : sideOf c
  · simp only [h, Bool.false_eq_true, ↓reduceIte] at hs ⊢
    exact List.pairwise_reverse.mp hs
  · simp only [h, ↓reduceIte] at hs ⊢
    exact hs

/-- **The grid formula is a comb formula.** -/
theorem gridCNF_combOK {W m : Nat} (hm : 1 ≤ m) (bits : Nat → Nat → Bool × Bool) :
    CombOK (gridCNF W m bits) := by
  have hspec := variableCount_spec (gridCNF W m bits)
  apply combOK_of
  · have hmem : [(⟨cellOff W 0 W, true⟩ : Literal), ⟨cellOff W 0 W + 1, true⟩] ∈
        gridCNF W m bits := by
      rw [gridCNF_eq]
      simp only [List.mem_append]
      left; left; left
      exact mem_colsE.mpr ⟨0, by omega, by unfold column endG; simp⟩
    have := hspec.1 _ hmem ⟨cellOff W 0 W + 1, true⟩ (by simp)
    unfold nK
    unfold cellOff colBase at this
    simp only [Nat.zero_mul] at this
    omega
  · intro c hc
    obtain ⟨h2, hs⟩ := grid_clause_ok hc
    exact shape_of (by rw [svars_length] at h2; exact h2) hs (hspec.1 c hc)
  · exact grid_pairwise W m bits

end Complexity.Planar.Grid
