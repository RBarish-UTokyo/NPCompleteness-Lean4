module

public import Complexity.Planar.Hypermap
import Lean.Elab.Tactic.Omega

/-!
# Checking a planar embedding with local conditions

An embedding of a graph with `n2` edges is certified by tables on its darts `0, …, 2 n2 - 1`:
the `node` and `face` permutations `N`, `F`, an encoding `EN` of the end of each dart, a rank
`R` of each dart in its node cycle, a face representative `FL`, a component representative
`CL` with a depth `D` and a successor `SU`, and running counts.  `EmbedOK` lists the local
checks; `EmbedOK.planarGraph` proves that they imply `PlanarGraph`.  Each check only looks at
a bounded number of table entries, so it is cheap to verify.
-/

@[expose] public section

namespace Complexity.Planar

/-- The tables certifying an embedding. -/
structure EmbedTables where
  n2 : Nat
  EN : Nat → Nat
  N : Nat → Nat
  F : Nat → Nat
  R : Nat → Nat
  FL : Nat → Nat
  CL : Nat → Nat
  D : Nat → Nat
  SU : Nat → Nat
  cR : Nat → Nat
  cF : Nat → Nat
  cC : Nat → Nat

/-- The other end of the edge of dart `d`. -/
def ed (d : Nat) : Nat := cond (Nat.beq (d % 2) 0) (d + 1) (d - 1)

theorem ed_even (h : Nat) : ed (2 * h) = 2 * h + 1 := by
  simp [ed, Nat.mul_mod_right]

theorem ed_odd (h : Nat) : ed (2 * h + 1) = 2 * h := by
  have : (2 * h + 1) % 2 = 1 := by omega
  simp [ed, this]

/-- The local checks. -/
structure EmbedOK (t : EmbedTables) : Prop where
  bound : ∀ d, d < 2 * t.n2 → t.N d < 2 * t.n2 ∧ t.F d < 2 * t.n2
  edgeK : ∀ h, h < t.n2 → t.N (t.F (2 * h + 1)) = 2 * h ∧ t.N (t.F (2 * h)) = 2 * h + 1
  nodeEnd : ∀ d, d < 2 * t.n2 → t.EN (t.N d) = t.EN d
  rank_next : ∀ d, d < 2 * t.n2 → t.R (t.N d) = t.R d + 1 ∨ t.R (t.N d) = 0
  rank_lt : ∀ d, d < 2 * t.n2 → t.R d < 2 * t.n2
  rank_prev : ∀ h, h < t.n2 →
    (0 < t.R (2 * h) → t.R (t.F (2 * h + 1)) + 1 = t.R (2 * h)) ∧
    (0 < t.R (2 * h + 1) → t.R (t.F (2 * h)) + 1 = t.R (2 * h + 1))
  rank_unique : ∀ d, d < 2 * t.n2 → ∀ d', d' < 2 * t.n2 →
    t.EN d = t.EN d' → t.R d = 0 → t.R d' = 0 → d = d'
  face : ∀ d, d < 2 * t.n2 → t.FL d ≤ d ∧ t.FL (t.F d) = t.FL d
  comp : ∀ d, d < 2 * t.n2 → t.CL d ≤ d ∧ (t.D d = 0 ↔ t.CL d = d)
  succ : ∀ d, d < 2 * t.n2 → 0 < t.D d →
    t.SU d < 2 * t.n2 ∧ t.D (t.SU d) + 1 = t.D d ∧ t.CL (t.SU d) = t.CL d ∧
      (t.SU d = ed d ∨ t.SU d = t.N d ∨ t.SU d = t.F d)
  cntR : t.cR 0 = 0 ∧ ∀ d, d < 2 * t.n2 → t.cR (d + 1) = t.cR d + (if t.R d = 0 then 1 else 0)
  cntF : t.cF 0 = 0 ∧ ∀ d, d < 2 * t.n2 → t.cF (d + 1) = t.cF d + (if t.FL d = d then 1 else 0)
  cntC : t.cC 0 = 0 ∧ ∀ d, d < 2 * t.n2 → t.cC (d + 1) = t.cC d + (if t.CL d = d then 1 else 0)
  final : 2 * t.cC (2 * t.n2) + t.n2 ≤ t.cR (2 * t.n2) + t.cF (2 * t.n2) + 1

/-- Decoding a vertex: even codes are `inl`, odd codes are `inr`. -/
def decodeEnd (k : Nat) : Sum Nat Nat := if k % 2 = 0 then .inl (k / 2) else .inr (k / 2)

theorem decodeEnd_injective {a b : Nat} (h : decodeEnd a = decodeEnd b) : a = b := by
  unfold decodeEnd at h
  split at h <;> split at h <;> simp at h <;> omega

/-- A running count is the number of indices satisfying the predicate. -/
theorem runningCount (c : Nat → Nat) (P : Nat → Bool) (N : Nat) (h0 : c 0 = 0)
    (hs : ∀ d, d < N → c (d + 1) = c d + (if P d then 1 else 0)) :
    c N = (List.finRange N).countP (fun x => P x.val) := by
  rw [countP_finRange_val P]
  induction N with
  | zero => simpa using h0
  | succ N ih =>
    rw [hs N (by omega), ih (fun d hd => hs d (by omega)), List.range_succ, List.countP_append]
    by_cases hp : P N = true <;> simp [hp]

theorem nodup_map_of_injOn {α β : Type} (f : α → β) {l : List α} (hl : l.Nodup)
    (hf : ∀ a ∈ l, ∀ b ∈ l, f a = f b → a = b) : (l.map f).Nodup := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.nodup_cons] at hl
    rw [List.map_cons, List.nodup_cons]
    refine ⟨?_, ih hl.2 (fun x hx y hy => hf x (List.mem_cons_of_mem a hx) y
      (List.mem_cons_of_mem a hy))⟩
    intro hmem
    obtain ⟨b, hb, hfb⟩ := List.mem_map.mp hmem
    have := hf b (List.mem_cons_of_mem a hb) a List.mem_cons_self hfb
    subst this
    exact hl.1 hb

theorem nodup_filter_finRange (n : Nat) (P : Fin n → Bool) :
    ((List.finRange n).filter P).Nodup :=
  List.Nodup.sublist List.filter_sublist (List.nodup_finRange n)

section sound

variable {t : EmbedTables} (h : EmbedOK t)
include h

/-- The hypermap described by the tables. -/
def EmbedOK.hypermap : Hypermap (2 * t.n2) where
  edge d := ⟨ed d.val, by
    have := d.isLt
    unfold ed; cases hb : Nat.beq (d.val % 2) 0
    · simp; omega
    · have : d.val % 2 = 0 := by simpa [Nat.beq_eq] using hb
      simp; omega⟩
  node d := ⟨t.N d.val, (h.bound d.val d.isLt).1⟩
  face d := ⟨t.F d.val, (h.bound d.val d.isLt).2⟩
  edgeK d := by
    apply Fin.ext
    simp only
    rcases Nat.mod_two_eq_zero_or_one d.val with hp | hp
    · obtain ⟨k, hk⟩ : ∃ k, d.val = 2 * k := ⟨d.val / 2, by omega⟩
      rw [hk, ed_even]
      exact (h.edgeK k (by have := d.isLt; omega)).1
    · obtain ⟨k, hk⟩ : ∃ k, d.val = 2 * k + 1 := ⟨d.val / 2, by omega⟩
      rw [hk, ed_odd]
      exact (h.edgeK k (by have := d.isLt; omega)).2

theorem EmbedOK.isGraphEdge : IsGraphEdge h.hypermap.edge := by
  intro d; rfl

theorem EmbedOK.iterate_node (k : Nat) (d : Fin (2 * t.n2)) :
    (iterate h.hypermap.node k d).val = iterate t.N k d.val := by
  induction k generalizing d with
  | zero => rfl
  | succ k ih => exact ih (h.hypermap.node d)

theorem EmbedOK.iterate_N_lt (k : Nat) {d : Nat} (hd : d < 2 * t.n2) :
    iterate t.N k d < 2 * t.n2 := by
  have := h.iterate_node k ⟨d, hd⟩
  rw [← this]; exact (iterate h.hypermap.node k ⟨d, hd⟩).isLt

theorem EmbedOK.iterate_EN (k : Nat) {d : Nat} (hd : d < 2 * t.n2) :
    t.EN (iterate t.N k d) = t.EN d := by
  induction k generalizing d with
  | zero => rfl
  | succ k ih =>
    simp only [iterate]
    rw [ih (h.bound d hd).1, h.nodeEnd d hd]

/-- The node predecessor `F (ed d)` lowers the rank. -/
theorem EmbedOK.pred_spec {d : Nat} (hd : d < 2 * t.n2) :
    t.F (ed d) < 2 * t.n2 ∧ t.N (t.F (ed d)) = d ∧ t.EN (t.F (ed d)) = t.EN d ∧
      (0 < t.R d → t.R (t.F (ed d)) + 1 = t.R d) := by
  rcases Nat.mod_two_eq_zero_or_one d with hp | hp
  · obtain ⟨k, rfl⟩ : ∃ k, d = 2 * k := ⟨d / 2, by omega⟩
    rw [ed_even]
    have hk : k < t.n2 := by omega
    have hb := (h.bound (2 * k + 1) (by omega)).2
    have hN := (h.edgeK k hk).1
    refine ⟨hb, hN, ?_, (h.rank_prev k hk).1⟩
    rw [← h.nodeEnd _ hb, hN]
  · obtain ⟨k, rfl⟩ : ∃ k, d = 2 * k + 1 := ⟨d / 2, by omega⟩
    rw [ed_odd]
    have hk : k < t.n2 := by omega
    have hb := (h.bound (2 * k) (by omega)).2
    have hN := (h.edgeK k hk).2
    refine ⟨hb, hN, ?_, (h.rank_prev k hk).2⟩
    rw [← h.nodeEnd _ hb, hN]

/-- Every dart is reached from the rank-0 dart of its vertex in `R d` node steps. -/
theorem EmbedOK.from_root : ∀ r d, t.R d = r → d < 2 * t.n2 →
    ∃ z, z < 2 * t.n2 ∧ t.R z = 0 ∧ t.EN z = t.EN d ∧ iterate t.N r z = d := by
  intro r
  induction r with
  | zero => intro d hr hd; exact ⟨d, hd, hr, rfl, rfl⟩
  | succ r ih =>
    intro d hr hd
    obtain ⟨hb, hN, hE, hR⟩ := h.pred_spec hd
    obtain ⟨z, hz, hz0, hzE, hzit⟩ := ih (t.F (ed d)) (by have := hR (by omega); omega) hb
    refine ⟨z, hz, hz0, hzE.trans hE, ?_⟩
    rw [iterate_succ', hzit, hN]

/-- Forward node steps from any dart reach a rank-0 dart. -/
theorem EmbedOK.to_root : ∀ s d, 2 * t.n2 - t.R d = s → d < 2 * t.n2 →
    ∃ k z, z < 2 * t.n2 ∧ t.R z = 0 ∧ t.EN z = t.EN d ∧ iterate t.N k d = z := by
  intro s
  induction s using Nat.strongRecOn with
  | ind s ih =>
    intro d hs hd
    by_cases h0 : t.R d = 0
    · exact ⟨0, d, hd, h0, rfl, rfl⟩
    · have hNd := (h.bound d hd).1
      rcases h.rank_next d hd with hr | hr
      · have hlt := h.rank_lt _ hNd
        obtain ⟨k, z, hz, hz0, hzE, hit⟩ :=
          ih (2 * t.n2 - t.R (t.N d)) (by omega) (t.N d) rfl hNd
        exact ⟨k + 1, z, hz, hz0, hzE.trans (h.nodeEnd d hd), hit⟩
      · exact ⟨1, t.N d, hNd, hr, h.nodeEnd d hd, rfl⟩

theorem EmbedOK.orbit {d d' : Nat} (hd : d < 2 * t.n2) (hd' : d' < 2 * t.n2)
    (hE : t.EN d = t.EN d') : ∃ k, iterate t.N k d = d' := by
  obtain ⟨k, z, hz, hz0, hzE, hit⟩ := h.to_root _ d rfl hd
  obtain ⟨z', hz', hz0', hzE', hit'⟩ := h.from_root _ d' rfl hd'
  have : z = z' := h.rank_unique z hz z' hz' (by rw [hzE, hzE', hE]) hz0 hz0'
  subst this
  exact ⟨k + t.R d', by rw [iterate_add, hit, hit']⟩

/-! ### The counts -/

theorem EmbedOK.node_count : t.cR (2 * t.n2) ≤ cycleCount h.hypermap.node := by
  rw [runningCount t.cR (fun d => t.R d == 0) _ h.cntR.1 (fun d hd => by
    rw [h.cntR.2 d hd]; simp)]
  rw [List.countP_eq_length_filter]
  apply cycleCount_ge h.hypermap.node (fun d => t.EN d.val)
  · intro x; exact h.nodeEnd x.val x.isLt
  · apply nodup_map_of_injOn _ (nodup_filter_finRange _ _)
    intro a ha b hb hab
    simp only [List.mem_filter, beq_iff_eq] at ha hb
    exact Fin.ext (h.rank_unique a.val a.isLt b.val b.isLt hab ha.2 hb.2)

theorem EmbedOK.iterate_face (k : Nat) (d : Fin (2 * t.n2)) :
    (iterate h.hypermap.face k d).val = iterate t.F k d.val := by
  induction k generalizing d with
  | zero => rfl
  | succ k ih => exact ih (h.hypermap.face d)

theorem EmbedOK.face_count : t.cF (2 * t.n2) ≤ cycleCount h.hypermap.face := by
  rw [runningCount t.cF (fun d => t.FL d == d) _ h.cntF.1 (fun d hd => by
    rw [h.cntF.2 d hd]; simp)]
  rw [cycleCount_eq]
  apply List.countP_mono_left
  intro d _ hd
  simp only [beq_iff_eq] at hd
  simp only [CycleMin, List.all_eq_true, List.mem_range, Nat.ble_eq]
  intro i _
  have hinv : ∀ k, t.FL (iterate h.hypermap.face k d).val = t.FL d.val := by
    intro k
    have := iterate_invariant h.hypermap.face (fun x => t.FL x.val)
      (fun x => (h.face x.val x.isLt).2) k d
    exact this
  have := (h.face _ (iterate h.hypermap.face i d).isLt).1
  rw [hinv i, hd] at this
  exact this

theorem EmbedOK.step_linked {d s : Nat} (hd : d < 2 * t.n2) (hs : s < 2 * t.n2)
    (hstep : s = ed d ∨ s = t.N d ∨ s = t.F d) :
    h.hypermap.linked 1 ⟨d, hd⟩ ⟨s, hs⟩ = true := by
  apply Linked.linked_step h.hypermap (Linked.linked_refl h.hypermap 0 ⟨d, hd⟩)
  unfold Linked.Step
  rcases hstep with rfl | rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)

theorem EmbedOK.to_component : ∀ k d (hd : d < 2 * t.n2), t.D d = k →
    ∃ hc : t.CL d < 2 * t.n2, h.hypermap.linked k ⟨d, hd⟩ ⟨t.CL d, hc⟩ = true := by
  intro k
  induction k with
  | zero =>
    intro d hd hD
    have hcl := (h.comp d hd).2.mp hD
    refine ⟨by rw [hcl]; exact hd, ?_⟩
    have : (⟨t.CL d, by rw [hcl]; exact hd⟩ : Fin (2 * t.n2)) = ⟨d, hd⟩ := Fin.ext hcl
    rw [this]; exact Linked.linked_refl h.hypermap 0 _
  | succ k ih =>
    intro d hd hD
    obtain ⟨hs, hDs, hCs, hstep⟩ := h.succ d hd (by omega)
    obtain ⟨hc, hl⟩ := ih (t.SU d) hs (by omega)
    refine ⟨by rw [← hCs]; exact hc, ?_⟩
    have h1 := h.step_linked hd hs hstep
    have := Linked.linked_trans h.hypermap h1 hl
    rw [Nat.add_comm] at this
    have he : (⟨t.CL (t.SU d), hc⟩ : Fin (2 * t.n2)) = ⟨t.CL d, by rw [← hCs]; exact hc⟩ :=
      Fin.ext hCs
    rw [he] at this
    exact this

theorem EmbedOK.component_count :
    h.hypermap.componentCount ≤ t.cC (2 * t.n2) := by
  rw [runningCount t.cC (fun d => t.CL d == d) _ h.cntC.1 (fun d hd => by
    rw [h.cntC.2 d hd]; simp)]
  apply componentCount_le
  intro x hx
  simp only [beq_eq_false_iff_ne] at hx
  obtain ⟨hc, hl⟩ := h.to_component (t.D x.val) x.val x.isLt rfl
  refine ⟨⟨t.CL x.val, hc⟩, ?_, t.D x.val, hl⟩
  have := (h.comp x.val x.isLt).1
  simp only
  omega

end sound

theorem EmbedOK.exists_hypermap {V : Type} {es : List (V × V)} {t : EmbedTables}
    (h : EmbedOK t) (dec : Nat → V) (hdec : ∀ a b, dec a = dec b → a = b)
    (hends : ∀ d, d < 2 * t.n2 → halfEdgeEnd es d = some (dec (t.EN d))) :
    ∃ G : Hypermap (2 * t.n2),
      (∀ d, (G.edge d).val = cond (Nat.beq (d.val % 2) 0) (d.val + 1) (d.val - 1)) ∧
      (∀ d d', (∃ k, iterate G.node k d = d') ↔
        halfEdgeEnd es d.val = halfEdgeEnd es d'.val) ∧
      G.Planar := by
  refine ⟨h.hypermap, fun d => rfl, ?_, ?_⟩
  · intro d d'
    rw [hends d.val d.isLt, hends d'.val d'.isLt]
    constructor
    · rintro ⟨k, hk⟩
      have := h.iterate_EN k d.isLt
      rw [← h.iterate_node k d, hk] at this
      rw [this]
    · intro hE
      have hE' : t.EN d.val = t.EN d'.val := hdec _ _ (Option.some.inj hE)
      obtain ⟨k, hk⟩ := h.orbit d.isLt d'.isLt hE'
      exact ⟨k, Fin.ext (by rw [h.iterate_node k d, hk])⟩
  · apply planar_of_bounds h.hypermap t.n2 (t.cR (2 * t.n2)) (t.cF (2 * t.n2)) (t.cC (2 * t.n2))
      (cycleCount_graphEdge_ge h.isGraphEdge) h.node_count h.face_count h.component_count
    have := h.final
    omega

/-- **Soundness of the embedding checks.** -/
theorem EmbedOK.planarGraph {V : Type} {es : List (V × V)} {t : EmbedTables} (h : EmbedOK t)
    (hlen : es.length = t.n2) (dec : Nat → V) (hdec : ∀ a b, dec a = dec b → a = b)
    (hends : ∀ d, d < 2 * t.n2 → halfEdgeEnd es d = some (dec (t.EN d))) :
    PlanarGraph es := by
  unfold PlanarGraph
  rw [hlen]
  exact h.exists_hypermap dec hdec hends

end Complexity.Planar
