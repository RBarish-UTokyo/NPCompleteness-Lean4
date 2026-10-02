module

public import Complexity.Planar.GridSat
public import Complexity.Planar.CombCycle
public import Complexity.Planar.Subdivide
import Lean.Elab.Tactic.Omega

/-!
# The target formulas of the reduction

* The grid formula `gridCNF W m bits` is a planar 3-CNF formula in Lichtenstein's sense: its
  incidence graph stays planar with the cycle through its variables (the comb drawing).
* The plain target `plainCNF W m bits` adds one clause `x_u ∨ z_u ∨ x_{u+1 mod K}` per variable
  `u < K` of the grid formula, with a fresh variable `z_u`.  Its incidence graph is the incidence
  graph of the grid formula together with the variable cycle, every cycle edge being subdivided
  by the new clause and carrying the new variable as a pendant vertex, hence planar.  The new
  clauses are satisfied by the fresh variables, so satisfiability does not change.
-/

@[expose] public section

namespace Complexity.Planar.Grid

open SAT Comb

/-! ## Variables of the grid formula -/

theorem le_getLastD_of_sorted {L : List Nat} (hs : L.Pairwise (· < ·)) {a : Nat} (ha : a ∈ L) :
    a ≤ L.getLastD 0 := by
  induction L with
  | nil => simp at ha
  | cons x xs ih =>
    rw [List.pairwise_cons] at hs
    cases xs with
    | nil =>
      simp only [List.mem_singleton] at ha
      subst ha; simp
    | cons y ys =>
      have hl : (x :: y :: ys).getLastD 0 = (y :: ys).getLastD 0 := by
        simp [List.getLastD_eq_getLast?]
      rw [hl]
      rcases List.mem_cons.mp ha with rfl | ha'
      · have hmem : (y :: ys).getLastD 0 ∈ y :: ys := by
          rw [getLastD_eq (by simp)]
          exact List.getElem_mem _
        exact Nat.le_of_lt (hs.1 _ hmem)
      · exact ih hs.2 ha'

theorem var_le_smax {c : Clause} (hs : (svars c).Pairwise (· < ·)) {l : Literal} (hl : l ∈ c) :
    l.var ≤ smax c := by
  unfold smax
  apply le_getLastD_of_sorted hs
  unfold svars
  split
  · exact List.mem_map.mpr ⟨l, hl, rfl⟩
  · exact List.mem_reverse.mpr (List.mem_map.mpr ⟨l, hl, rfl⟩)

/-- Every variable of the grid formula lies below `m * (9 * W + 3)`. -/
theorem grid_var_lt {W m : Nat} {bits : Nat → Nat → Bool × Bool} {c : Clause}
    (hc : c ∈ gridCNF W m bits) {l : Literal} (hl : l ∈ c) : l.var < m * (9 * W + 3) := by
  have hv := var_le_smax (grid_clause_ok hc).2 hl
  have hm : ∀ j, j < m → colBase W (j + 1) ≤ m * (9 * W + 3) := by
    intro j hj
    unfold colBase colLen
    exact Nat.mul_le_mul_right _ hj
  rw [gridCNF_eq] at hc
  simp only [List.mem_append] at hc
  rcases hc with ((hc | hc) | hc) | hc
  · obtain ⟨j, hj, _, _, hc⟩ := mem_cols (Or.inl hc)
    have := column_span hc
    have := hm j hj
    have := colBase_succ W j
    unfold cellOff at *; omega
  · obtain ⟨j, hj, _, _, hc⟩ := mem_cols (Or.inr hc)
    have := column_span hc
    have := hm j hj
    have := colBase_succ W j
    unfold cellOff at *; omega
  · obtain ⟨k, hk, v, hv', hc⟩ := mem_rbsE.mp hc
    have := (rbEven_facts hv' hc).2.1
    have := hm (2 * k + 1) (by omega)
    have := colBase_succ W (2 * k + 1)
    unfold cellOff at *; omega
  · obtain ⟨k, hk, v, hv', hc⟩ := mem_rbsO.mp hc
    have := (rbOdd_facts hv' hc).2.1
    have := hm (2 * k + 1 + 1) (by omega)
    have := colBase_succ W (2 * k + 1 + 1)
    unfold cellOff at *; omega

theorem grid_varCount {W m : Nat} (hm : 1 ≤ m) (bits : Nat → Nat → Bool × Bool) :
    variableCount (gridCNF W m bits) = m * (9 * W + 3) := by
  apply variableCount_eq
  · intro c hc l hl; exact grid_var_lt hc hl
  · right
    refine ⟨[⟨cellOff W (m - 1) W + 1, false⟩, ⟨cellOff W (m - 1) W, true⟩],
      column_mem (j := m - 1) (by omega) (end_mem (by simp [endG])),
      ⟨cellOff W (m - 1) W + 1, false⟩, by simp, ?_⟩
    show cellOff W (m - 1) W + 1 + 1 = m * (9 * W + 3)
    unfold cellOff colBase colLen
    have : (m - 1) * (9 * W + 3) + (9 * W + 3) = m * (9 * W + 3) := by
      rw [← Nat.succ_mul, show (m - 1).succ = m by omega]
    omega

/-! ## Clause lengths -/

theorem grid_threeCNF (W m : Nat) (bits : Nat → Nat → Bool × Bool) :
    IsThreeCNF (gridCNF W m bits) := by
  intro c hc
  have two : ∀ {c : Clause}, (svars c).length = 2 → c.length ≤ 3 := by
    intro c h; rw [svars_length] at h; omega
  rw [gridCNF_eq] at hc
  simp only [List.mem_append] at hc
  have col : ∀ {j odd}, c ∈ column W j odd bits → c.length ≤ 3 := by
    intro j odd hc
    rcases mem_column hc with h | ⟨idx, _, t, ht, rfl⟩ | h
    · exact two (start_facts h).2.2
    · have := (cellT_shape _ _ t ht).2.1
      unfold inst; split <;> simp [this]
    · exact two (end_facts h).2.2
  rcases hc with ((hc | hc) | hc) | hc
  · obtain ⟨_, _, _, _, hc⟩ := mem_cols (Or.inl hc); exact col hc
  · obtain ⟨_, _, _, _, hc⟩ := mem_cols (Or.inr hc); exact col hc
  · obtain ⟨_, _, v, hv, hc⟩ := mem_rbsE.mp hc; exact two (rbEven_facts hv hc).2.2.1
  · obtain ⟨_, _, v, hv, hc⟩ := mem_rbsO.mp hc; exact two (rbOdd_facts hv hc).2.2.1

/-! ## Planarity with the variable cycle -/

theorem planarGraph_nil {V : Type} : PlanarGraph ([] : List (V × V)) := by
  refine ⟨⟨fun x => x, fun x => x, fun x => x, fun _ => rfl⟩, fun d => d.elim0,
    fun d => d.elim0, ?_⟩
  apply planar_of_bounds _ 0 0 0 0 (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) ?_ (by simp)
  unfold Hypermap.componentCount
  simp

theorem grid_cyclePlanar (W m : Nat) (bits : Nat → Nat → Bool × Bool) :
    PlanarGraph (incidenceGraph (gridCNF W m bits) ++ variableCycle (gridCNF W m bits)) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · exact planarGraph_nil
  · exact Comb.comb_planar (gridCNF_combOK hm bits)

theorem grid_isCyclePlanar (W m : Nat) (bits : Nat → Nat → Bool × Bool) :
    IsCyclePlanarThreeCNF (gridCNF W m bits) :=
  ⟨grid_threeCNF W m bits, grid_cyclePlanar W m bits⟩

/-! ## The plain target -/

/-- The clause subdividing the cycle edge `u → u + 1 mod K`. -/
def spineClause (K u : Nat) : Clause := [⟨u, true⟩, ⟨K + u, true⟩, ⟨(u + 1) % K, true⟩]

/-- The grid formula with the subdivided variable cycle. -/
def plainCNF (W m : Nat) (bits : Nat → Nat → Bool × Bool) : CNF :=
  gridCNF W m bits ++ (List.range (m * (9 * W + 3))).map (spineClause (m * (9 * W + 3)))

theorem incidenceGraph_append (f g : CNF) :
    incidenceGraph (f ++ g) = incidenceGraph f ++
      (g.zipIdx f.length).flatMap fun p => p.1.map fun l => (Sum.inl l.var, Sum.inr p.2) := by
  unfold incidenceGraph
  rw [List.zipIdx_append, List.flatMap_append, Nat.zero_add]

theorem zipIdx_map_range {α : Type} (K i : Nat) (g : Nat → α) :
    ((List.range K).map g).zipIdx i = (List.range K).map (fun u => (g u, i + u)) := by
  apply List.ext_getElem
  · simp
  · intro n h1 h2
    simp

theorem mem_incidenceGraph {f : CNF} {e : Sum Nat Nat × Sum Nat Nat} (he : e ∈ incidenceGraph f) :
    ∃ j l, j < f.length ∧ l ∈ f[j]! ∧ e = (Sum.inl l.var, Sum.inr j) := by
  unfold incidenceGraph at he
  simp only [List.mem_flatMap, List.mem_map] at he
  obtain ⟨⟨c, j⟩, hp, l, hl, rfl⟩ := he
  obtain ⟨hj, hcj⟩ := List.mem_zipIdx' hp
  refine ⟨j, l, hj, ?_, rfl⟩
  rw [getElem!_pos f j hj, ← hcj]
  exact hl

theorem plain_incidence {W m : Nat} (hm : 1 ≤ m) (bits : Nat → Nat → Bool × Bool) :
    incidenceGraph (plainCNF W m bits) = incidenceGraph (gridCNF W m bits) ++
      Subdiv.spineEdges (variableCycle (gridCNF W m bits))
        (fun u => Sum.inr ((gridCNF W m bits).length + u))
        (fun u => Sum.inl (m * (9 * W + 3) + u)) := by
  unfold plainCNF
  rw [incidenceGraph_append]
  congr 1
  unfold Subdiv.spineEdges variableCycle
  rw [grid_varCount hm, zipIdx_map_range, zipIdx_map_range, List.flatMap_map, List.flatMap_map]
  simp [spineClause]

theorem grid_plainPlanar (W m : Nat) (bits : Nat → Nat → Bool × Bool) :
    PlanarGraph (incidenceGraph (plainCNF W m bits)) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · have : plainCNF W 0 bits = [] := by simp [plainCNF, gridCNF]
    rw [this]
    exact planarGraph_nil
  · rw [plain_incidence hm]
    apply Subdiv.planar_subdivide
    · intro u u' h; simpa using h
    · intro u u' h; simpa using h
    · intro u u' h; cases h
    · intro e he u
      have hK := grid_varCount (W := W) hm bits
      rcases List.mem_append.mp he with he | he
      · obtain ⟨j, l, hj, hl, rfl⟩ := mem_incidenceGraph he
        rw [getElem!_pos _ j hj] at hl
        have := grid_var_lt (List.getElem_mem hj) hl
        refine ⟨by simp, by simp; omega, by simp; omega, by simp⟩
      · unfold variableCycle at he
        rw [hK] at he
        simp only [List.mem_map, List.mem_range] at he
        obtain ⟨v, hv, rfl⟩ := he
        have : (v + 1) % (m * (9 * W + 3)) < m * (9 * W + 3) := Nat.mod_lt _ (by omega)
        refine ⟨by simp, by simp, by simp; omega, by simp; omega⟩
    · exact grid_cyclePlanar W m bits

theorem plain_threeCNF (W m : Nat) (bits : Nat → Nat → Bool × Bool) :
    IsThreeCNF (plainCNF W m bits) := by
  intro c hc
  unfold plainCNF at hc
  rcases List.mem_append.mp hc with hc | hc
  · exact grid_threeCNF W m bits c hc
  · simp only [List.mem_map] at hc
    obtain ⟨u, _, rfl⟩ := hc
    simp [spineClause]

theorem plain_isPlanar (W m : Nat) (bits : Nat → Nat → Bool × Bool) :
    IsPlanarThreeCNF (plainCNF W m bits) :=
  ⟨plain_threeCNF W m bits, grid_plainPlanar W m bits⟩

theorem plain_satisfiable_iff (W m : Nat) (bits : Nat → Nat → Bool × Bool) :
    Satisfiable (plainCNF W m bits) ↔ Satisfiable (gridCNF W m bits) := by
  unfold plainCNF Satisfiable evalCNF
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨a, ?_⟩
    rw [List.all_append, Bool.and_eq_true] at ha
    exact ha.1
  · rintro ⟨a, ha⟩
    refine ⟨fun v => if v < m * (9 * W + 3) then a v else true, ?_⟩
    rw [List.all_append, Bool.and_eq_true]
    constructor
    · rw [List.all_eq_true] at ha ⊢
      intro c hc
      have := ha c hc
      unfold evalClause at this ⊢
      rw [List.any_eq_true] at this ⊢
      obtain ⟨l, hl, hv⟩ := this
      refine ⟨l, hl, ?_⟩
      unfold evalLiteral at hv ⊢
      have hlt := grid_var_lt hc hl
      simpa [hlt] using hv
    · rw [List.all_eq_true]
      intro c hc
      simp only [List.mem_map] at hc
      obtain ⟨u, _, rfl⟩ := hc
      unfold evalClause spineClause
      rw [List.any_eq_true]
      refine ⟨⟨m * (9 * W + 3) + u, true⟩, by simp, ?_⟩
      unfold evalLiteral
      simp

end Complexity.Planar.Grid
