module

public import Complexity.Planar.EmbedCert
public import Complexity.Planar.Perm
import Lean.Elab.Tactic.Omega

/-!
# Every planar embedding has a certificate

Conversely to `EmbedOK.planarGraph`, the hypermap of a planar embedding yields tables passing
all local checks: ranks are positions in node cycles counted from their least dart, face and
component representatives are least darts, and depths are lengths of shortest paths to them.
The genus-zero inequality then gives the final count check.
-/

@[expose] public section

namespace Complexity.Planar

section complete

variable {n : Nat} (G : Hypermap n)

/-- A function on darts, extended by `0` to all numbers. -/
noncomputable def natOf (f : Fin n → Nat) (d : Nat) : Nat := if h : d < n then f ⟨d, h⟩ else 0

theorem natOf_lt (f : Fin n → Nat) {d : Nat} (h : d < n) : natOf f d = f ⟨d, h⟩ := by
  simp [natOf, h]

theorem exists_compMin (x : Fin n) :
    ∃ k, (∃ y : Fin n, y.val = k ∧ G.linked n x y = true) ∧
      ∀ k', k' < k → ¬ ∃ y : Fin n, y.val = k' ∧ G.linked n x y = true :=
  exists_least ⟨x.val, x, rfl, Linked.linked_refl G n x⟩

/-- The least dart reachable from `x`. -/
noncomputable def compMin (x : Fin n) : Nat := Classical.choose (exists_compMin G x)

theorem compMin_spec (x : Fin n) :
    (∃ y : Fin n, y.val = compMin G x ∧ G.linked n x y = true) ∧
      ∀ y : Fin n, G.linked n x y = true → compMin G x ≤ y.val := by
  obtain ⟨h1, h2⟩ := Classical.choose_spec (exists_compMin G x)
  refine ⟨h1, fun y hy => ?_⟩
  apply Classical.byContradiction
  intro hlt
  exact h2 y.val (by unfold compMin at hlt; omega) ⟨y, rfl, hy⟩

theorem compMin_lt (x : Fin n) : compMin G x < n := by
  obtain ⟨⟨y, hy, _⟩, _⟩ := compMin_spec G x
  rw [← hy]; exact y.isLt

/-- The reachable sets of the two ends of a step agree. -/
theorem linked_step_iff {x s : Fin n} (hs : Linked.Step G x s) (y : Fin n) :
    G.linked n x y = true ↔ G.linked n s y = true := by
  constructor
  · intro h
    obtain ⟨k, hk⟩ := hm_step_back G hs
    exact Linked.linked_stable G (Linked.linked_trans G hk h)
  · intro h
    have h1 := Linked.linked_step G (Linked.linked_refl G 0 x) hs
    exact Linked.linked_stable G (Linked.linked_trans G h1 h)

theorem compMin_step {x s : Fin n} (hs : Linked.Step G x s) : compMin G s = compMin G x := by
  obtain ⟨⟨y1, hy1, hl1⟩, hm1⟩ := compMin_spec G x
  obtain ⟨⟨y2, hy2, hl2⟩, hm2⟩ := compMin_spec G s
  apply Nat.le_antisymm
  · rw [← hy1]; exact hm2 y1 ((linked_step_iff G hs y1).mp hl1)
  · rw [← hy2]; exact hm1 y2 ((linked_step_iff G hs y2).mpr hl2)

/-- The least number of steps from `x` to its component representative. -/
theorem exists_depth (x : Fin n) :
    ∃ k, (G.linked k x ⟨compMin G x, compMin_lt G x⟩ = true) ∧
      ∀ k', k' < k → ¬ G.linked k' x ⟨compMin G x, compMin_lt G x⟩ = true := by
  apply exists_least
  obtain ⟨⟨y, hy, hl⟩, _⟩ := compMin_spec G x
  refine ⟨n, ?_⟩
  have : y = ⟨compMin G x, compMin_lt G x⟩ := Fin.ext hy
  rw [← this]; exact hl

noncomputable def depth (x : Fin n) : Nat := Classical.choose (exists_depth G x)

theorem depth_spec (x : Fin n) :
    G.linked (depth G x) x ⟨compMin G x, compMin_lt G x⟩ = true ∧
      ∀ k', k' < depth G x → ¬ G.linked k' x ⟨compMin G x, compMin_lt G x⟩ = true :=
  Classical.choose_spec (exists_depth G x)

theorem depth_le (x : Fin n) : depth G x ≤ n := by
  apply Classical.byContradiction
  intro hlt
  obtain ⟨⟨y, hy, hl⟩, _⟩ := compMin_spec G x
  have : y = ⟨compMin G x, compMin_lt G x⟩ := Fin.ext hy
  rw [this] at hl
  exact (depth_spec G x).2 n (by omega) hl

theorem depth_zero_iff (x : Fin n) : depth G x = 0 ↔ compMin G x = x.val := by
  constructor
  · intro h
    have := (depth_spec G x).1
    rw [h] at this
    have := congrArg Fin.val ((Linked.linked_zero G _ _).mp this)
    simp only at this
    exact this.symm
  · intro h
    apply Classical.byContradiction
    intro hne
    apply (depth_spec G x).2 0 (by omega)
    rw [Linked.linked_zero]
    exact Fin.ext h.symm

theorem exists_succ (x : Fin n) (hpos : 0 < depth G x) :
    ∃ s : Fin n, Linked.Step G x s ∧
      G.linked (depth G x - 1) s ⟨compMin G x, compMin_lt G x⟩ = true := by
  have h1 := (depth_spec G x).1
  rw [show depth G x = depth G x - 1 + 1 by omega] at h1
  rcases hm_linked_first G h1 with h | h
  · exact absurd h ((depth_spec G x).2 _ (by omega))
  · exact h

/-- The successor towards the component representative. -/
noncomputable def succDart (x : Fin n) : Nat :=
  if h : 0 < depth G x then (Classical.choose (exists_succ G x h)).val else 0

theorem succDart_spec (x : Fin n) (hpos : 0 < depth G x) :
    ∃ hs : succDart G x < n, Linked.Step G x ⟨succDart G x, hs⟩ ∧
      depth G ⟨succDart G x, hs⟩ + 1 = depth G x ∧
      compMin G ⟨succDart G x, hs⟩ = compMin G x := by
  have hc := Classical.choose_spec (exists_succ G x hpos)
  have hval : succDart G x = (Classical.choose (exists_succ G x hpos)).val := by
    simp [succDart, hpos]
  generalize Classical.choose (exists_succ G x hpos) = s at hc hval
  have hs' : succDart G x < n := by rw [hval]; exact s.isLt
  have hse : (⟨succDart G x, hs'⟩ : Fin n) = s := Fin.ext hval
  refine ⟨hs', by rw [hse]; exact hc.1, ?_, by rw [hse]; exact compMin_step G hc.1⟩
  rw [hse]
  have hcm := compMin_step G hc.1
  apply Nat.le_antisymm
  · -- the path of length `depth x - 1` from `s`
    have : depth G s ≤ depth G x - 1 := by
      apply Classical.byContradiction
      intro hlt
      apply (depth_spec G s).2 (depth G x - 1) (by omega)
      have := hc.2
      have he : (⟨compMin G x, compMin_lt G x⟩ : Fin n) = ⟨compMin G s, compMin_lt G s⟩ :=
        Fin.ext hcm.symm
      rw [← he]; exact this
    omega
  · -- a shorter path from `s` would give a shorter path from `x`
    apply Classical.byContradiction
    intro hlt
    have h1 := Linked.linked_step G (Linked.linked_refl G 0 x) hc.1
    have h2 := (depth_spec G s).1
    have he : (⟨compMin G s, compMin_lt G s⟩ : Fin n) = ⟨compMin G x, compMin_lt G x⟩ :=
      Fin.ext hcm
    rw [he] at h2
    have := Linked.linked_trans G h1 h2
    exact (depth_spec G x).2 _ (by omega) this

/-- Running count of a predicate on numbers. -/
def runCount (P : Nat → Bool) (d : Nat) : Nat := (List.range d).countP P

theorem runCount_succ (P : Nat → Bool) (d : Nat) :
    runCount P (d + 1) = runCount P d + (if P d then 1 else 0) := by
  simp only [runCount, List.range_succ, List.countP_append]
  by_cases h : P d = true <;> simp [h]

theorem runCount_le (P : Nat → Bool) (d : Nat) : runCount P d ≤ d := by
  have := List.countP_le_length (p := P) (l := List.range d)
  simpa [runCount] using this

end complete

/-- **Completeness of the embedding checks.** Every planar graph has certificate tables, with
all entries bounded by the number of darts (and the end codes given by `enc`). -/
theorem embed_complete {V : Type} {es : List (V × V)} (enc : V → Nat) (dec : Nat → V)
    (hde : ∀ v, dec (enc v) = v) (hp : PlanarGraph es) :
    ∃ t : EmbedTables, t.n2 = es.length ∧ EmbedOK t ∧
      (∀ d, d < 2 * t.n2 → ∃ v, halfEdgeEnd es d = some v ∧ t.EN d = enc v) ∧
      (∀ d, d < 2 * t.n2 → t.N d < 2 * t.n2 ∧ t.F d < 2 * t.n2 ∧ t.R d < 2 * t.n2 ∧
        t.FL d ≤ d ∧ t.CL d ≤ d ∧ t.D d ≤ 2 * t.n2 ∧ t.SU d < 2 * t.n2) ∧
      (∀ d, t.cR d ≤ d ∧ t.cF d ≤ d ∧ t.cC d ≤ d) ∧
      (∀ d, 2 * t.n2 ≤ d → t.EN d = 0 ∧ t.N d = 0 ∧ t.F d = 0 ∧ t.R d = 0 ∧ t.FL d = 0 ∧
        t.CL d = 0 ∧ t.D d = 0 ∧ t.SU d = 0) := by
  obtain ⟨G, hedge, horbit, hplanar⟩ := hp
  let n := 2 * es.length
  have hNinj := hm_node_inj G
  have hFinj := hm_face_inj G
  -- the end of each dart
  have hend : ∀ d : Fin n, ∃ v, halfEdgeEnd es d.val = some v := by
    intro d
    unfold halfEdgeEnd
    have : d.val / 2 < es.length := by have := d.isLt; omega
    simp [List.getElem?_eq_getElem this]
  let endv : Fin n → V := fun d => Classical.choose (hend d)
  have hendv : ∀ d, halfEdgeEnd es d.val = some (endv d) := fun d => Classical.choose_spec (hend d)
  let t : EmbedTables := {
    n2 := es.length
    EN := natOf (fun d => enc (endv d))
    N := natOf (fun d => (G.node d).val)
    F := natOf (fun d => (G.face d).val)
    R := natOf (fun d => crank G.node hNinj d)
    FL := natOf (fun d => (cmin G.face d).val)
    CL := natOf (fun d => compMin G d)
    D := natOf (fun d => depth G d)
    SU := natOf (fun d => succDart G d)
    cR := runCount (fun d => natOf (fun d => crank G.node hNinj d) d == 0)
    cF := runCount (fun d => natOf (fun d => (cmin G.face d).val) d == d)
    cC := runCount (fun d => natOf (fun d => compMin G d) d == d) }
  have hN : ∀ d (h : d < n), t.N d = (G.node ⟨d, h⟩).val := fun d h => by simp only [t]; exact natOf_lt _ h
  have hF : ∀ d (h : d < n), t.F d = (G.face ⟨d, h⟩).val := fun d h => by simp only [t]; exact natOf_lt _ h
  have hR : ∀ d (h : d < n), t.R d = crank G.node hNinj ⟨d, h⟩ := fun d h => by simp only [t]; exact natOf_lt _ h
  have hFL : ∀ d (h : d < n), t.FL d = (cmin G.face ⟨d, h⟩).val := fun d h => by simp only [t]; exact natOf_lt _ h
  have hCL : ∀ d (h : d < n), t.CL d = compMin G ⟨d, h⟩ := fun d h => by simp only [t]; exact natOf_lt _ h
  have hD : ∀ d (h : d < n), t.D d = depth G ⟨d, h⟩ := fun d h => by simp only [t]; exact natOf_lt _ h
  have hSU : ∀ d (h : d < n), t.SU d = succDart G ⟨d, h⟩ := fun d h => by simp only [t]; exact natOf_lt _ h
  have hEN : ∀ d (h : d < n), t.EN d = enc (endv ⟨d, h⟩) := fun d h => by simp only [t]; exact natOf_lt _ h
  have hencinj : ∀ a b, enc a = enc b → a = b := by
    intro a b h; rw [← hde a, ← hde b, h]
  -- the edge permutation on numbers
  have hed : ∀ d : Fin n, (G.edge d).val = ed d.val := fun d => hedge d
  -- same end iff same node orbit
  have hsame : ∀ d d' : Fin n, endv d = endv d' ↔ ∃ k, iterate G.node k d = d' := by
    intro d d'
    rw [horbit, hendv, hendv]
    constructor
    · intro h; rw [h]
    · intro h; exact Option.some.inj h
  have hnodeEnd : ∀ d : Fin n, endv (G.node d) = endv d :=
    fun d => ((hsame d (G.node d)).mpr ⟨1, rfl⟩).symm
  refine ⟨t, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · constructor
    · intro d hd
      rw [hN d hd, hF d hd]
      exact ⟨(G.node _).isLt, (G.face _).isLt⟩
    · intro h hh
      have h0 : 2 * h < n := by simp [n]; omega
      have h1 : 2 * h + 1 < n := by simp [n]; omega
      have e0 : (G.edge ⟨2 * h, h0⟩) = ⟨2 * h + 1, h1⟩ := Fin.ext (by rw [hed]; exact ed_even h)
      have e1 : (G.edge ⟨2 * h + 1, h1⟩) = ⟨2 * h, h0⟩ := Fin.ext (by rw [hed]; exact ed_odd h)
      constructor
      · rw [hF _ h1, hN _ (G.face _).isLt]
        have := G.edgeK ⟨2 * h, h0⟩
        rw [e0] at this
        rw [this]
      · rw [hF _ h0, hN _ (G.face _).isLt]
        have := G.edgeK ⟨2 * h + 1, h1⟩
        rw [e1] at this
        rw [this]
    · intro d hd
      rw [hN d hd, hEN _ (G.node _).isLt, hEN d hd]
      exact congrArg enc (hnodeEnd ⟨d, hd⟩)
    · intro d hd
      rw [hN d hd, hR _ (G.node _).isLt, hR d hd]
      exact crank_step hNinj ⟨d, hd⟩
    · intro d hd
      rw [hR d hd]; exact crank_lt hNinj _
    · intro h hh
      have h0 : 2 * h < n := by simp [n]; omega
      have h1 : 2 * h + 1 < n := by simp [n]; omega
      have e0 : (G.edge ⟨2 * h, h0⟩) = ⟨2 * h + 1, h1⟩ := Fin.ext (by rw [hed]; exact ed_even h)
      have e1 : (G.edge ⟨2 * h + 1, h1⟩) = ⟨2 * h, h0⟩ := Fin.ext (by rw [hed]; exact ed_odd h)
      constructor
      · intro hpos
        rw [hF _ h1, hR _ (G.face _).isLt, hR _ h0]
        rw [hR _ h0] at hpos
        apply crank_pred hNinj _ _ _ hpos
        have := G.edgeK ⟨2 * h, h0⟩
        rw [e0] at this; exact this
      · intro hpos
        rw [hF _ h0, hR _ (G.face _).isLt, hR _ h1]
        rw [hR _ h1] at hpos
        apply crank_pred hNinj _ _ _ hpos
        have := G.edgeK ⟨2 * h + 1, h1⟩
        rw [e1] at this; exact this
    · intro d hd d' hd' hE h0 h0'
      rw [hEN d hd, hEN d' hd'] at hE
      rw [hR d hd] at h0
      rw [hR d' hd'] at h0'
      have hz := (crank_zero_iff hNinj _).mp h0
      have hz' := (crank_zero_iff hNinj _).mp h0'
      obtain ⟨k, hk⟩ := (hsame _ _).mp (hencinj _ _ hE)
      have := cmin_iterate hNinj ⟨d, hd⟩ k
      rw [hk, hz', hz] at this
      exact congrArg Fin.val this.symm
    · intro d hd
      rw [hFL d hd, hF d hd, hFL _ (G.face _).isLt]
      exact ⟨cmin_le_self hFinj _, congrArg Fin.val (cmin_step hFinj _)⟩
    · intro d hd
      rw [hCL d hd, hD d hd, depth_zero_iff]
      refine ⟨?_, Iff.rfl⟩
      exact (compMin_spec G ⟨d, hd⟩).2 ⟨d, hd⟩ (Linked.linked_refl G n _)
    · intro d hd hpos
      rw [hD d hd] at hpos
      obtain ⟨hs, hstep, hdep, hcm⟩ := succDart_spec G ⟨d, hd⟩ hpos
      rw [hSU d hd, hD _ hs, hD d hd, hCL _ hs, hCL d hd]
      refine ⟨hs, hdep, hcm, ?_⟩
      rw [hN d hd, hF d hd]
      rcases hstep with h | h | h
      · left; have := congrArg Fin.val h; simp only at this; rw [← this, hed]
      · right; left; have := congrArg Fin.val h; simp only at this; rw [← this]
      · right; right; have := congrArg Fin.val h; simp only at this; rw [← this]
    · exact ⟨rfl, fun d _ => by simp only [t, runCount_succ, beq_iff_eq]⟩
    · exact ⟨rfl, fun d _ => by simp only [t, runCount_succ, beq_iff_eq]⟩
    · exact ⟨rfl, fun d _ => by simp only [t, runCount_succ, beq_iff_eq]⟩
    · -- the genus-zero inequality
      have hcountR : t.cR n = cycleCount G.node := by
        show runCount _ n = _
        rw [runCount, cycleCount_eq, ← countP_finRange_val]
        apply List.countP_congr
        intro x _
        rw [natOf_lt _ x.isLt]
        simp only [beq_iff_eq]
        rw [crank_zero_iff, cmin_eq_iff hNinj]
      have hcountF : t.cF n = cycleCount G.face := by
        show runCount _ n = _
        rw [runCount, cycleCount_eq, ← countP_finRange_val]
        apply List.countP_congr
        intro x _
        rw [natOf_lt _ x.isLt]
        simp only [beq_iff_eq]
        rw [← cmin_eq_iff hFinj]
        exact ⟨fun h => Fin.ext h, fun h => congrArg Fin.val h⟩
      have hcountC : t.cC n = G.componentCount := by
        show runCount _ n = _
        rw [runCount, Hypermap.componentCount, ← countP_finRange_val]
        apply List.countP_congr
        intro x _
        rw [natOf_lt _ x.isLt]
        simp only [beq_iff_eq, List.all_eq_true, List.mem_finRange, true_implies,
          Bool.or_eq_true, Bool.not_eq_true', Nat.ble_eq]
        constructor
        · intro h y
          by_cases hl : G.linked n x y = true
          · right; rw [← h]; exact (compMin_spec G x).2 y hl
          · left; simpa using hl
        · intro h
          apply Nat.le_antisymm
          · exact (compMin_spec G x).2 x (Linked.linked_refl G n x)
          · obtain ⟨⟨y, hy, hl⟩, _⟩ := compMin_spec G x
            rcases h y with h' | h'
            · rw [hl] at h'; exact absurd h' (by simp)
            · rw [← hy]; exact h'
      have hedge_le := cycleCount_graphEdge_le (E := es.length) (edge := G.edge) hedge
      have hpl := (planar_iff G).mp hplanar
      unfold Hypermap.eulerRhs at hpl
      show 2 * t.cC n + es.length ≤ t.cR n + t.cF n + 1
      rw [hcountR, hcountF, hcountC]
      omega
  · intro d hd
    exact ⟨endv ⟨d, hd⟩, hendv ⟨d, hd⟩, hEN d hd⟩
  · intro d hd
    rw [hN d hd, hF d hd, hR d hd, hFL d hd, hCL d hd, hD d hd, hSU d hd]
    refine ⟨(G.node _).isLt, (G.face _).isLt, crank_lt hNinj _, cmin_le_self hFinj _,
      (compMin_spec G ⟨d, hd⟩).2 ⟨d, hd⟩ (Linked.linked_refl G n _), depth_le G _, ?_⟩
    by_cases hpos : 0 < depth G ⟨d, hd⟩
    · exact (succDart_spec G ⟨d, hd⟩ hpos).1
    · simp [succDart, hpos]; omega
  · intro d
    exact ⟨runCount_le _ d, runCount_le _ d, runCount_le _ d⟩
  · intro d hd
    have hn : ¬ d < 2 * es.length := by simp [t] at hd; omega
    simp [t, natOf, hn]
    intro h; exact absurd h hn

end Complexity.Planar
