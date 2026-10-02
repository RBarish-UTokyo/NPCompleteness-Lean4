module

public import Complexity.Planarity
import Lean.Elab.Tactic.Omega

/-!
# Bounds on the Euler counts of a hypermap

Planarity is `genus = 0`, that is `2 * components + darts ≤ edges + nodes + faces + 1` for the
cycle and component counts of `Complexity.Planarity`.  This file proves the inequalities used to
establish it without computing any count exactly:

* `cycleCount_ge`: a permutation has at least as many cycles as there are darts with pairwise
  different values of a function invariant under it;
* `componentCount_le`: there are at most as many components as "roots", when every other dart
  can reach a smaller dart;
* `linked_stable`: reachability within any number of steps is reachability within `n` steps.
-/

@[expose] public section

namespace Complexity

theorem iterate_succ' {α : Type} (f : α → α) (k : Nat) (x : α) :
    iterate f (k + 1) x = f (iterate f k x) := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih => exact ih (f x)

theorem iterate_add {α : Type} (f : α → α) (a b : Nat) (x : α) :
    iterate f (a + b) x = iterate f b (iterate f a x) := by
  induction a generalizing x with
  | zero => simp [iterate]
  | succ a ih =>
    rw [Nat.add_right_comm]
    exact ih (f x)

theorem iterate_invariant {α β : Type} (f : α → α) (φ : α → β) (h : ∀ x, φ (f x) = φ x)
    (k : Nat) (x : α) : φ (iterate f k x) = φ x := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih => simp only [iterate]; rw [ih (f x), h x]

namespace Planar

/-! ## Counting on `Fin n` -/

/-- A duplicate-free list of darts satisfying `P` is no longer than the number of such darts. -/
theorem length_le_countP {n : Nat} (P : Fin n → Bool) (xs : List (Fin n)) (hnd : xs.Nodup)
    (hP : ∀ x ∈ xs, P x = true) : xs.length ≤ (List.finRange n).countP P := by
  rw [List.countP_eq_length_filter]
  apply List.Nodup.length_le_of_subset hnd
  intro x hx
  simp [List.mem_filter, hP x hx]

/-- Every dart has a smallest dart with the same label. -/
theorem exists_least_label {n : Nat} {β : Type} (φ : Fin n → β) (x : Fin n) :
    ∃ m : Fin n, φ m = φ x ∧ ∀ z : Fin n, φ z = φ x → m.val ≤ z.val := by
  have key : ∀ k, ∀ x : Fin n, x.val < k →
      ∃ m : Fin n, φ m = φ x ∧ ∀ z : Fin n, φ z = φ x → m.val ≤ z.val := by
    intro k
    induction k with
    | zero => intro x hx; omega
    | succ k ih =>
      intro x hx
      by_cases hex : ∃ z : Fin n, φ z = φ x ∧ z.val < x.val
      · obtain ⟨z, hz, hlt⟩ := hex
        obtain ⟨m, hm, hmin⟩ := ih z (by omega)
        exact ⟨m, hm.trans hz, fun w hw => hmin w (hw.trans hz.symm)⟩
      · refine ⟨x, rfl, fun z hz => ?_⟩
        by_cases hlt : z.val < x.val
        · exact absurd ⟨z, hz, hlt⟩ hex
        · omega
  exact key (x.val + 1) x (by omega)

theorem nodup_of_map {α β : Type} (f : α → β) {l : List α} (h : (l.map f).Nodup) : l.Nodup := by
  induction l with
  | nil => exact List.nodup_nil
  | cons a l ih =>
    rw [List.map_cons, List.nodup_cons] at h
    rw [List.nodup_cons]
    refine ⟨fun ha => h.1 (List.mem_map.mpr ⟨a, ha, rfl⟩), ih h.2⟩

/-- The predicate counted by `cycleCount`. -/
def CycleMin {n : Nat} (p : Fin n → Fin n) (x : Fin n) : Bool :=
  (List.range n).all fun i => Nat.ble x.val (iterate p i x).val

theorem cycleCount_eq {n : Nat} (p : Fin n → Fin n) :
    cycleCount p = (List.finRange n).countP (CycleMin p) := rfl

/-- **Lower bound on cycles.** If `φ` is invariant under `p`, the darts of a list with pairwise
different labels lie in pairwise different cycles. -/
theorem cycleCount_ge {n : Nat} {β : Type} (p : Fin n → Fin n) (φ : Fin n → β)
    (hφ : ∀ x, φ (p x) = φ x) (xs : List (Fin n)) (hnd : (xs.map φ).Nodup) :
    xs.length ≤ cycleCount p := by
  have hm : ∀ x : Fin n, ∃ m : Fin n, φ m = φ x ∧ ∀ z : Fin n, φ z = φ x → m.val ≤ z.val :=
    fun x => exists_least_label φ x
  let m : Fin n → Fin n := fun x => Classical.choose (hm x)
  have hmφ : ∀ x, φ (m x) = φ x := fun x => (Classical.choose_spec (hm x)).1
  have hmmin : ∀ x z, φ z = φ x → (m x).val ≤ z.val := fun x => (Classical.choose_spec (hm x)).2
  have hcyc : ∀ x, CycleMin p (m x) = true := by
    intro x
    simp only [CycleMin, List.all_eq_true, List.mem_range, Nat.ble_eq]
    intro i _
    apply hmmin x
    rw [iterate_invariant p φ hφ i (m x), hmφ x]
  have hlen := length_le_countP (CycleMin p) (xs.map m) ?_ ?_
  · simpa [cycleCount_eq] using hlen
  · -- distinct labels give distinct least darts
    have : (xs.map m).map φ = xs.map φ := by
      rw [List.map_map]; exact List.map_inj_left.mpr (fun x _ => hmφ x)
    rw [← this] at hnd
    exact nodup_of_map φ hnd
  · intro y hy
    obtain ⟨x, _, rfl⟩ := List.mem_map.mp hy
    exact hcyc x

/-! ## Reachability -/

namespace Linked

variable {n : Nat} (G : Hypermap n)

/-- One step of `edge`, `node` or `face`. -/
def Step (z y : Fin n) : Prop := G.edge z = y ∨ G.node z = y ∨ G.face z = y

theorem linked_zero (x y : Fin n) : G.linked 0 x y = true ↔ x = y := by
  simp [Hypermap.linked, Fin.ext_iff]

theorem linked_succ (k : Nat) (x y : Fin n) :
    G.linked (k + 1) x y = true ↔
      G.linked k x y = true ∨ ∃ z, G.linked k x z = true ∧ Step G z y := by
  simp [Hypermap.linked, Step, Fin.ext_iff, Nat.beq_eq, or_assoc]

theorem linked_mono_succ {k : Nat} {x y : Fin n} (h : G.linked k x y = true) :
    G.linked (k + 1) x y = true := (linked_succ G k x y).mpr (Or.inl h)

theorem linked_mono {k k' : Nat} (hk : k ≤ k') {x y : Fin n} (h : G.linked k x y = true) :
    G.linked k' x y = true := by
  induction hk with
  | refl => exact h
  | step _ ih => exact linked_mono_succ G ih

theorem linked_refl (k : Nat) (x : Fin n) : G.linked k x x = true :=
  linked_mono G (Nat.zero_le k) ((linked_zero G x x).mpr rfl)

theorem linked_step {k : Nat} {x z y : Fin n} (h : G.linked k x z = true) (hs : Step G z y) :
    G.linked (k + 1) x y = true := (linked_succ G k x y).mpr (Or.inr ⟨z, h, hs⟩)

/-- Concatenation of paths. -/
theorem linked_trans {a b : Nat} {x y z : Fin n} (h1 : G.linked a x y = true)
    (h2 : G.linked b y z = true) : G.linked (a + b) x z = true := by
  induction b generalizing z with
  | zero =>
    have : y = z := (linked_zero G y z).mp h2
    subst this; simpa using h1
  | succ b ih =>
    rcases (linked_succ G b y z).mp h2 with h | ⟨w, hw, hs⟩
    · exact linked_mono_succ G (ih h)
    · exact linked_step G (ih hw) hs

/-- If the reachable set does not grow at step `k`, it never grows again. -/
theorem stable_succ {x : Fin n} {k : Nat} (h : ∀ y, G.linked (k + 1) x y = G.linked k x y) :
    ∀ y, G.linked (k + 2) x y = G.linked (k + 1) x y := by
  intro y
  have e1 : G.linked (k + 2) x y = (G.linked (k + 1) x y || (List.finRange n).any fun z =>
      G.linked (k + 1) x z && (Nat.beq (G.edge z).val y.val || Nat.beq (G.node z).val y.val ||
        Nat.beq (G.face z).val y.val)) := rfl
  have e2 : G.linked (k + 1) x y = (G.linked k x y || (List.finRange n).any fun z =>
      G.linked k x z && (Nat.beq (G.edge z).val y.val || Nat.beq (G.node z).val y.val ||
        Nat.beq (G.face z).val y.val)) := rfl
  rw [e1]
  conv => rhs; rw [e2]
  simp only [h]

theorem stable_from {x : Fin n} {k : Nat} (h : ∀ y, G.linked (k + 1) x y = G.linked k x y) :
    ∀ j y, G.linked (k + j + 1) x y = G.linked (k + j) x y := by
  intro j
  induction j with
  | zero => simpa using h
  | succ j ih =>
    intro y
    have := stable_succ G (k := k + j) ih y
    simpa [Nat.add_assoc] using this

theorem stable_forever {x : Fin n} {k : Nat} (h : ∀ y, G.linked (k + 1) x y = G.linked k x y) :
    ∀ j y, G.linked (k + j) x y = G.linked k x y := by
  intro j
  induction j with
  | zero => intro y; rfl
  | succ j ih =>
    intro y
    rw [show k + (j + 1) = k + j + 1 by omega, stable_from G h j y, ih y]

/-- A strictly larger subset has a strictly larger count. -/
theorem countP_lt_of_mono {α : Type} {l : List α} {p q : α → Bool}
    (hpq : ∀ a ∈ l, p a = true → q a = true) {y : α} (hy : y ∈ l) (hqy : q y = true)
    (hpy : p y = false) : l.countP p < l.countP q := by
  induction l with
  | nil => simp at hy
  | cons a l ih =>
    simp only [List.countP_cons]
    have hl : ∀ b ∈ l, p b = true → q b = true := fun b hb => hpq b (List.mem_cons_of_mem a hb)
    have hmono := List.countP_mono_left (l := l) hl
    rcases List.mem_cons.mp hy with rfl | hy'
    · simp [hpy, hqy]; omega
    · have := ih hl hy'
      by_cases hpa : p a = true
      · simp [hpa, hpq a (List.mem_cons_self) hpa]; omega
      · simp [hpa]; split <;> omega

/-- The number of darts reachable within `k` steps. -/
def reachCount (x : Fin n) (k : Nat) : Nat := (List.finRange n).countP (G.linked k x)

theorem reachCount_zero (x : Fin n) : 1 ≤ reachCount G x 0 := by
  unfold reachCount
  apply List.countP_pos_iff.mpr
  exact ⟨x, List.mem_finRange x, linked_refl G 0 x⟩

theorem reachCount_le (x : Fin n) (k : Nat) : reachCount G x k ≤ n := by
  unfold reachCount
  simpa using (List.countP_le_length (p := G.linked k x) (l := List.finRange n))

theorem reachCount_grows (x : Fin n) (k : Nat)
    (h : ¬ ∀ y, G.linked (k + 1) x y = G.linked k x y) :
    reachCount G x k < reachCount G x (k + 1) := by
  have : ∃ y, G.linked (k + 1) x y = true ∧ G.linked k x y = false := by
    apply Classical.byContradiction
    intro hne
    apply h
    intro y
    cases hk : G.linked k x y
    · cases hk1 : G.linked (k + 1) x y
      · rfl
      · exact absurd ⟨y, hk1, hk⟩ hne
    · exact linked_mono_succ G hk
  obtain ⟨y, h1, h0⟩ := this
  exact countP_lt_of_mono (fun a _ ha => linked_mono_succ G ha) (List.mem_finRange y) h1 h0

/-- Some step before `n` adds no new dart. -/
theorem exists_stable (x : Fin n) :
    ∃ j, j < n ∧ ∀ y, G.linked (j + 1) x y = G.linked j x y := by
  apply Classical.byContradiction
  intro hno
  have grow : ∀ j, j ≤ n → j + 1 ≤ reachCount G x j := by
    intro j
    induction j with
    | zero => intro _; exact reachCount_zero G x
    | succ j ih =>
      intro hj
      have hns : ¬ ∀ y, G.linked (j + 1) x y = G.linked j x y :=
        fun hs => hno ⟨j, by omega, hs⟩
      have := reachCount_grows G x j hns
      have := ih (by omega)
      omega
  have := grow n (Nat.le_refl n)
  have := reachCount_le G x n
  omega

/-- **Reachability stabilizes**: anything reachable is reachable within `n` steps. -/
theorem linked_stable {k : Nat} {x y : Fin n} (h : G.linked k x y = true) :
    G.linked n x y = true := by
  obtain ⟨j, hj, hs⟩ := exists_stable G x
  have hall := stable_forever G hs
  have hn : G.linked n x y = G.linked j x y := by
    have := hall (n - j) y
    rwa [show j + (n - j) = n by omega] at this
  rw [hn]
  by_cases hk : k ≤ j
  · exact linked_mono G hk h
  · have := hall (k - j) y
    rw [show j + (k - j) = k by omega] at this
    rw [← this]; exact h

end Linked

/-! ## Components -/

/-- **Upper bound on components**: if every non-root dart reaches a smaller dart, there are at
most as many components as roots. -/
theorem componentCount_le {n : Nat} (G : Hypermap n) (R : Fin n → Bool)
    (h : ∀ x, R x = false → ∃ y : Fin n, y.val < x.val ∧ ∃ k, G.linked k x y = true) :
    G.componentCount ≤ (List.finRange n).countP R := by
  unfold Hypermap.componentCount
  apply List.countP_mono_left
  intro x _ hx
  apply Classical.byContradiction
  intro hR
  have hR' : R x = false := by simpa using hR
  obtain ⟨y, hy, k, hk⟩ := h x hR'
  have hn := Linked.linked_stable G hk
  have := List.all_eq_true.mp hx y (List.mem_finRange y)
  simp [hn, Nat.ble_eq] at this
  omega

/-! ## The Euler criterion -/

theorem planar_iff {n : Nat} (G : Hypermap n) :
    G.Planar ↔ 2 * G.componentCount + n ≤ G.eulerRhs + 1 := by
  unfold Hypermap.Planar Hypermap.genus Hypermap.eulerLhs
  omega

/-- **Planarity from bounds** on the four counts. -/
theorem planar_of_bounds {n : Nat} (G : Hypermap n) (e v f c : Nat)
    (he : e ≤ cycleCount G.edge) (hv : v ≤ cycleCount G.node) (hf : f ≤ cycleCount G.face)
    (hc : G.componentCount ≤ c) (h : 2 * c + n ≤ e + v + f + 1) : G.Planar := by
  rw [planar_iff]
  unfold Hypermap.eulerRhs
  omega

/-! ## The edge permutation of a graph -/

theorem map_val_finRange (n : Nat) : (List.finRange n).map Fin.val = List.range n := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp [List.getElem_finRange]

theorem countP_finRange_val {n : Nat} (P : Nat → Bool) :
    (List.finRange n).countP (fun x => P x.val) = (List.range n).countP P := by
  rw [← map_val_finRange, List.countP_map]
  rfl

/-- The `edge` permutation of a graph embedding pairs `2i` with `2i+1`. -/
def IsGraphEdge {n : Nat} (edge : Fin n → Fin n) : Prop :=
  ∀ d, (edge d).val = cond (Nat.beq (d.val % 2) 0) (d.val + 1) (d.val - 1)

theorem graphEdge_val {n : Nat} {edge : Fin n → Fin n} (h : IsGraphEdge edge) (d : Fin n) :
    (d.val % 2 = 0 ∧ (edge d).val = d.val + 1) ∨ (d.val % 2 = 1 ∧ (edge d).val = d.val - 1) := by
  have := h d
  rcases Nat.mod_two_eq_zero_or_one d.val with h2 | h2
  · rw [h2] at this; exact Or.inl ⟨h2, this⟩
  · rw [h2] at this; exact Or.inr ⟨h2, this⟩

theorem graphEdge_div {n : Nat} {edge : Fin n → Fin n} (h : IsGraphEdge edge) (d : Fin n) :
    (edge d).val / 2 = d.val / 2 := by
  rcases graphEdge_val h d with ⟨h2, he⟩ | ⟨h2, he⟩ <;> omega

theorem cycleCount_graphEdge_ge {E : Nat} {edge : Fin (2 * E) → Fin (2 * E)}
    (h : IsGraphEdge edge) : E ≤ cycleCount edge := by
  let xs : List (Fin (2 * E)) := (List.range E).pmap (fun i hi => ⟨2 * i, by
    simp [List.mem_range] at hi; omega⟩) (fun _ h => h)
  have hlen : xs.length = E := by simp [xs]
  have hmap : xs.map (fun d => d.val / 2) = List.range E := by
    apply List.ext_getElem
    · simp [xs]
    · intro i h1 h2
      simp [xs]
  have := cycleCount_ge edge (fun d => d.val / 2) (graphEdge_div h) xs
    (by rw [hmap]; exact List.nodup_range)
  omega

theorem countP_range_even (E : Nat) :
    (List.range (2 * E)).countP (fun d => d % 2 == 0) = E := by
  induction E with
  | zero => rfl
  | succ E ih =>
    rw [show 2 * (E + 1) = 2 * E + 1 + 1 by omega, List.range_succ, List.range_succ]
    simp [List.countP_append, ih] <;> omega

theorem cycleCount_graphEdge_le {E : Nat} {edge : Fin (2 * E) → Fin (2 * E)}
    (h : IsGraphEdge edge) : cycleCount edge ≤ E := by
  rw [cycleCount_eq]
  calc (List.finRange (2 * E)).countP (CycleMin edge)
      ≤ (List.finRange (2 * E)).countP (fun d => d.val % 2 == 0) := by
        apply List.countP_mono_left
        intro d _ hd
        apply Classical.byContradiction
        intro hodd
        have hodd' : d.val % 2 ≠ 0 := by simpa using hodd
        have h1 := List.all_eq_true.mp hd 1 (by simp [List.mem_range]; omega)
        simp [iterate, Nat.ble_eq] at h1
        rcases graphEdge_val h d with ⟨h2, _⟩ | ⟨_, he⟩
        · omega
        · omega
    _ = E := by
        rw [countP_finRange_val (fun d => d % 2 == 0), countP_range_even]


end Planar

end Complexity
