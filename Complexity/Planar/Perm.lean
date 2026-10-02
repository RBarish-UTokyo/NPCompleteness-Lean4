module

public import Complexity.Planar.Hypermap
import Lean.Elab.Tactic.Omega

/-!
# Permutations of `Fin n` and hypermap orbits

Basic facts needed to certify an arbitrary planar embedding: an injective self-map of `Fin n`
returns to every dart after at most `n` steps (pigeonhole), so it is a bijection, its cycles
have least elements, and the three permutations of a hypermap generate a symmetric
reachability relation.
-/

@[expose] public section

namespace Complexity.Planar

/-- Least witness of a predicate on `Nat`. -/
theorem exists_least {P : Nat → Prop} (h : ∃ r, P r) : ∃ r, P r ∧ ∀ r', r' < r → ¬ P r' := by
  obtain ⟨r, hr⟩ := h
  have key : ∀ k, ∀ r, r < k → P r → ∃ r, P r ∧ ∀ r', r' < r → ¬ P r' := by
    intro k
    induction k with
    | zero => intro r hr; omega
    | succ k ih =>
      intro r hrk hr
      by_cases hex : ∃ r', r' < r ∧ P r'
      · obtain ⟨r', hr', hP⟩ := hex
        exact ih r' (by omega) hP
      · exact ⟨r, hr, fun r' hr' hP => hex ⟨r', hr', hP⟩⟩
  exact key (r + 1) r (by omega) hr

theorem nodup_map_of_injOn' {α β : Type} (f : α → β) {l : List α} (hl : l.Nodup)
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

/-- **Pigeonhole**: `n + 1` values in `Fin n` repeat. -/
theorem pigeonhole {n : Nat} (g : Nat → Fin n) : ∃ i j, i < j ∧ j ≤ n ∧ g i = g j := by
  apply Classical.byContradiction
  intro hno
  have hinj : ∀ a ∈ List.range (n + 1), ∀ b ∈ List.range (n + 1), g a = g b → a = b := by
    intro a ha b hb hab
    simp only [List.mem_range] at ha hb
    apply Classical.byContradiction
    intro hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · exact hno ⟨a, b, hlt, by omega, hab⟩
    · exact hno ⟨b, a, hlt, by omega, hab.symm⟩
  have hnd := nodup_map_of_injOn' g (List.nodup_range) hinj
  have hle := List.Nodup.length_le_of_subset hnd (l₂ := List.finRange n)
    (fun x _ => List.mem_finRange x)
  simp at hle
  omega

section perm

variable {n : Nat} {p : Fin n → Fin n}

theorem iterate_inj (hp : ∀ a b, p a = p b → a = b) (k : Nat) {a b : Fin n}
    (h : iterate p k a = iterate p k b) : a = b := by
  induction k generalizing a b with
  | zero => exact h
  | succ k ih => exact hp a b (ih h)

/-- **Periodicity**: an injective map returns to every point within `n` steps. -/
theorem period (hp : ∀ a b, p a = p b → a = b) (x : Fin n) :
    ∃ T, 0 < T ∧ T ≤ n ∧ iterate p T x = x := by
  obtain ⟨i, j, hij, hj, heq⟩ := pigeonhole (fun k => iterate p k x)
  refine ⟨j - i, by omega, by omega, ?_⟩
  have h1 : iterate p i (iterate p (j - i) x) = iterate p i x := by
    rw [← iterate_add, show j - i + i = j by omega]; exact heq.symm
  exact iterate_inj hp i h1

theorem iterate_period_mul (x : Fin n) (T : Nat) (hT : iterate p T x = x) (c : Nat) :
    iterate p (c * T) x = x := by
  induction c with
  | zero => simp [iterate]
  | succ c ih => rw [Nat.succ_mul, iterate_add, ih, hT]

/-- Iterates beyond `n` repeat the first `n` iterates. -/
theorem iterate_mod (hp : ∀ a b, p a = p b → a = b) (x : Fin n) (k : Nat) :
    ∃ i, i < n ∧ iterate p k x = iterate p i x := by
  obtain ⟨T, hT0, hTn, hT⟩ := period hp x
  refine ⟨k % T, by have := Nat.mod_lt k hT0; omega, ?_⟩
  have hk : k = (k / T) * T + k % T := by
    have := Nat.div_add_mod k T; rw [Nat.mul_comm] at this; omega
  conv => lhs; rw [hk]
  rw [iterate_add, iterate_period_mul x T hT]

/-- Going backwards is going forwards: `x` is reached from `p^k x`. -/
theorem back (hp : ∀ a b, p a = p b → a = b) (k : Nat) (x : Fin n) :
    ∃ r, iterate p r (iterate p k x) = x := by
  obtain ⟨T, hT0, _, hT⟩ := period hp x
  refine ⟨k * T - k, ?_⟩
  rw [← iterate_add]
  have : k + (k * T - k) = k * T := by
    have : k ≤ k * T := Nat.le_mul_of_pos_right k hT0
    omega
  rw [this]
  exact iterate_period_mul x T hT k

/-- An injective self-map of `Fin n` is surjective. -/
theorem surj (hp : ∀ a b, p a = p b → a = b) (y : Fin n) : ∃ x, p x = y := by
  obtain ⟨T, hT0, _, hT⟩ := period hp y
  refine ⟨iterate p (T - 1) y, ?_⟩
  have := iterate_succ' p (T - 1) y
  rw [show T - 1 + 1 = T by omega, hT] at this
  exact this.symm

/-- The orbit of `x` meets every value at least as small as some fixed bound. -/
theorem exists_cycleMin (x : Fin n) :
    ∃ z : Fin n, (∃ i, i < n ∧ iterate p i x = z) ∧
      ∀ i, i < n → z.val ≤ (iterate p i x).val := by
  have hn : 0 < n := by have := x.isLt; omega
  have key : ∀ k, ∀ i, i < n → (iterate p i x).val < k →
      ∃ z : Fin n, (∃ i, i < n ∧ iterate p i x = z) ∧
        ∀ i, i < n → z.val ≤ (iterate p i x).val := by
    intro k
    induction k with
    | zero => intro i _ h; omega
    | succ k ih =>
      intro i hi hk
      by_cases hex : ∃ j, j < n ∧ (iterate p j x).val < (iterate p i x).val
      · obtain ⟨j, hj, hlt⟩ := hex
        exact ih j hj (by omega)
      · exact ⟨iterate p i x, ⟨i, hi, rfl⟩, fun j hj => by
          by_cases h : (iterate p j x).val < (iterate p i x).val
          · exact absurd ⟨j, hj, h⟩ hex
          · omega⟩
  exact key ((iterate p 0 x).val + 1) 0 hn (by omega)

/-- The least dart of the cycle of `x`. -/
noncomputable def cmin (p : Fin n → Fin n) (x : Fin n) : Fin n :=
  Classical.choose (exists_cycleMin (p := p) x)

theorem cmin_mem (x : Fin n) : ∃ i, i < n ∧ iterate p i x = cmin p x :=
  (Classical.choose_spec (exists_cycleMin (p := p) x)).1

theorem cmin_le (hp : ∀ a b, p a = p b → a = b) (x : Fin n) (k : Nat) :
    (cmin p x).val ≤ (iterate p k x).val := by
  obtain ⟨i, hi, he⟩ := iterate_mod hp x k
  rw [he]
  exact (Classical.choose_spec (exists_cycleMin (p := p) x)).2 i hi

theorem cmin_iterate (hp : ∀ a b, p a = p b → a = b) (x : Fin n) (k : Nat) :
    cmin p (iterate p k x) = cmin p x := by
  apply Fin.ext
  apply Nat.le_antisymm
  · obtain ⟨i, _, he⟩ := cmin_mem (p := p) x
    obtain ⟨r, hr⟩ := back hp k x
    have := cmin_le hp (iterate p k x) (r + i)
    rw [iterate_add, hr, he] at this
    exact this
  · obtain ⟨i, _, he⟩ := cmin_mem (p := p) (iterate p k x)
    have := cmin_le hp x (k + i)
    rw [iterate_add, he] at this
    exact this

theorem cmin_step (hp : ∀ a b, p a = p b → a = b) (x : Fin n) : cmin p (p x) = cmin p x :=
  cmin_iterate hp x 1

theorem cmin_le_self (hp : ∀ a b, p a = p b → a = b) (x : Fin n) : (cmin p x).val ≤ x.val :=
  cmin_le hp x 0

theorem cmin_eq_iff (hp : ∀ a b, p a = p b → a = b) (x : Fin n) :
    cmin p x = x ↔ CycleMin p x = true := by
  simp only [CycleMin, List.all_eq_true, List.mem_range, Nat.ble_eq]
  constructor
  · intro h i _
    have := cmin_le hp x i
    rw [h] at this; exact this
  · intro h
    apply Fin.ext
    apply Nat.le_antisymm (cmin_le_self hp x)
    obtain ⟨i, hi, he⟩ := cmin_mem (p := p) x
    rw [← he]; exact h i hi

/-- `x` is reached from the least dart of its cycle. -/
theorem from_cmin (hp : ∀ a b, p a = p b → a = b) (x : Fin n) :
    ∃ r, iterate p r (cmin p x) = x := by
  obtain ⟨i, _, he⟩ := cmin_mem (p := p) x
  rw [← he]
  exact back hp i x

/-- The position of `x` in its cycle, counted from the least dart. -/
noncomputable def crank (p : Fin n → Fin n) (hp : ∀ a b, p a = p b → a = b) (x : Fin n) : Nat :=
  Classical.choose (exists_least (from_cmin hp x))

theorem crank_spec (hp : ∀ a b, p a = p b → a = b) (x : Fin n) :
    iterate p (crank p hp x) (cmin p x) = x ∧
      ∀ r, r < crank p hp x → iterate p r (cmin p x) ≠ x :=
  Classical.choose_spec (exists_least (from_cmin hp x))

theorem crank_zero_iff (hp : ∀ a b, p a = p b → a = b) (x : Fin n) :
    crank p hp x = 0 ↔ cmin p x = x := by
  constructor
  · intro h
    have := (crank_spec hp x).1
    rw [h] at this; exact this
  · intro h
    apply Classical.byContradiction
    intro hne
    exact (crank_spec hp x).2 0 (by omega) h

theorem crank_lt (hp : ∀ a b, p a = p b → a = b) (x : Fin n) : crank p hp x < n := by
  apply Classical.byContradiction
  intro hge
  obtain ⟨T, hT0, hTn, hT⟩ := period hp (cmin p x)
  have h1 := (crank_spec hp x).1
  have h2 : iterate p (crank p hp x - T) (cmin p x) = x := by
    have : iterate p (crank p hp x) (cmin p x) =
        iterate p (crank p hp x - T) (iterate p T (cmin p x)) := by
      rw [← iterate_add, show T + (crank p hp x - T) = crank p hp x by omega]
    rw [hT] at this
    rw [← this]; exact h1
  exact (crank_spec hp x).2 _ (by omega) h2

/-- The rank grows by one along the cycle, except when returning to the least dart. -/
theorem crank_step (hp : ∀ a b, p a = p b → a = b) (x : Fin n) :
    crank p hp (p x) = crank p hp x + 1 ∨ crank p hp (p x) = 0 := by
  by_cases h0 : cmin p (p x) = p x
  · exact Or.inr ((crank_zero_iff hp (p x)).mpr h0)
  · left
    have hc := cmin_step hp x
    obtain ⟨hx1, hx2⟩ := crank_spec hp x
    obtain ⟨hy1, hy2⟩ := crank_spec hp (p x)
    rw [hc] at hy1 hy2
    have hfwd : iterate p (crank p hp x + 1) (cmin p x) = p x := by
      rw [iterate_succ', hx1]
    apply Nat.le_antisymm
    · apply Classical.byContradiction
      intro hgt
      exact hy2 _ (by omega) hfwd
    · apply Classical.byContradiction
      intro hlt
      have hpos : 0 < crank p hp (p x) := by
        apply Nat.pos_of_ne_zero
        intro hz
        rw [hz] at hy1
        rw [← hc] at hy1
        exact h0 hy1
      have : iterate p (crank p hp (p x) - 1) (cmin p x) = x := by
        apply hp
        have h3 := iterate_succ' p (crank p hp (p x) - 1) (cmin p x)
        rw [show crank p hp (p x) - 1 + 1 = crank p hp (p x) by omega, hy1] at h3
        exact h3.symm
      exact hx2 _ (by omega) this

/-- Going one step back lowers the rank by one. -/
theorem crank_pred (hp : ∀ a b, p a = p b → a = b) (q x : Fin n) (hq : p q = x)
    (hpos : 0 < crank p hp x) : crank p hp q + 1 = crank p hp x := by
  rcases crank_step hp q with h | h
  · rw [hq] at h; omega
  · rw [hq] at h; omega

end perm

/-! ## Hypermap permutations -/

section hypermap

variable {n : Nat} (G : Hypermap n)

theorem hm_edge_inj : ∀ a b, G.edge a = G.edge b → a = b := by
  intro a b h
  have ha := G.edgeK a
  have hb := G.edgeK b
  rw [h] at ha
  rw [ha] at hb; exact hb

theorem hm_edge_surj (y : Fin n) : ∃ x, G.edge x = y := surj (hm_edge_inj G) y

theorem hm_node_inj : ∀ a b, G.node a = G.node b → a = b := by
  -- `node` has the right inverse `face ∘ edge`, which is injective, hence surjective
  have hr : ∀ a b, G.face (G.edge a) = G.face (G.edge b) → a = b := by
    intro a b h
    have ha := G.edgeK a
    have hb := G.edgeK b
    rw [h] at ha; rw [ha] at hb; exact hb
  intro a b h
  obtain ⟨a', ha'⟩ := surj (p := fun x => G.face (G.edge x)) hr a
  obtain ⟨b', hb'⟩ := surj (p := fun x => G.face (G.edge x)) hr b
  rw [← ha', ← hb', G.edgeK, G.edgeK] at h
  rw [← ha', ← hb', h]

theorem hm_face_inj : ∀ a b, G.face a = G.face b → a = b := by
  intro a b h
  obtain ⟨a', rfl⟩ := hm_edge_surj G a
  obtain ⟨b', rfl⟩ := hm_edge_surj G b
  have ha := G.edgeK a'
  have hb := G.edgeK b'
  rw [h] at ha
  rw [ha] at hb
  rw [hb]

/-- Every step can be undone by steps. -/
theorem hm_step_back {x s : Fin n} (h : Linked.Step G x s) : ∃ k, G.linked k s x = true := by
  have viaPerm : ∀ (p : Fin n → Fin n), (∀ a b, p a = p b → a = b) →
      (∀ y, Linked.Step G y (p y)) → p x = s → ∃ k, G.linked k s x = true := by
    intro p hp hstep hs
    obtain ⟨r, hr⟩ := back hp 1 x
    refine ⟨r, ?_⟩
    have : ∀ r (y : Fin n), G.linked r y (iterate p r y) = true := by
      intro r
      induction r with
      | zero => intro y; exact Linked.linked_refl G 0 y
      | succ r ih =>
        intro y
        rw [iterate_succ']
        exact Linked.linked_step G (ih y) (hstep _)
    have h1 := this r (iterate p 1 x)
    rw [hr] at h1
    rw [← hs]; exact h1
  rcases h with h | h | h
  · exact viaPerm G.edge (hm_edge_inj G) (fun y => Or.inl rfl) h
  · exact viaPerm G.node (hm_node_inj G) (fun y => Or.inr (Or.inl rfl)) h
  · exact viaPerm G.face (hm_face_inj G) (fun y => Or.inr (Or.inr rfl)) h

/-- Reachability is symmetric. -/
theorem hm_linked_symm {k : Nat} {x y : Fin n} (h : G.linked k x y = true) :
    ∃ k', G.linked k' y x = true := by
  induction k generalizing y with
  | zero =>
    have := (Linked.linked_zero G x y).mp h
    subst this; exact ⟨0, Linked.linked_refl G 0 x⟩
  | succ k ih =>
    rcases (Linked.linked_succ G k x y).mp h with h' | ⟨z, hz, hs⟩
    · exact ih h'
    · obtain ⟨k1, h1⟩ := hm_step_back G hs
      obtain ⟨k2, h2⟩ := ih hz
      exact ⟨k1 + k2, Linked.linked_trans G h1 h2⟩

/-- First-step decomposition of reachability. -/
theorem hm_linked_first {k : Nat} {x y : Fin n} (h : G.linked (k + 1) x y = true) :
    G.linked k x y = true ∨ ∃ s, Linked.Step G x s ∧ G.linked k s y = true := by
  induction k generalizing y with
  | zero =>
    rcases (Linked.linked_succ G 0 x y).mp h with h' | ⟨z, hz, hs⟩
    · exact Or.inl h'
    · have := (Linked.linked_zero G x z).mp hz
      subst this
      exact Or.inr ⟨y, hs, Linked.linked_refl G 0 y⟩
  | succ k ih =>
    rcases (Linked.linked_succ G (k + 1) x y).mp h with h' | ⟨z, hz, hs⟩
    · rcases ih h' with h'' | ⟨s, hs', hl⟩
      · exact Or.inl (Linked.linked_mono_succ G h'')
      · exact Or.inr ⟨s, hs', Linked.linked_mono_succ G hl⟩
    · rcases ih hz with h'' | ⟨s, hs', hl⟩
      · exact Or.inl (Linked.linked_step G h'' hs)
      · exact Or.inr ⟨s, hs', Linked.linked_step G hl hs⟩

end hypermap

end Complexity.Planar
