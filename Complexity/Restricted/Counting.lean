module

public import Complexity.Restricted.Copies
import Lean.Elab.Tactic.Omega

/-!
# Occurrence counts in the copy formula

Every literal occurs at most once in the clauses replacing the entries (`gadgetVal`) and at
most once in the implication cycles (`cyclesVal`). Positive literals of copy variables occur
only in the cycles and literals of chain variables only in the chains. Hence in `output`
every variable occurs at most once positively and at most twice negatively.
-/

@[expose] public section

namespace Complexity.Restricted

open Complexity.SAT

/-! ### Generic counting lemmas -/

theorem count_le_one_of_nodup {α : Type} [BEq α] [LawfulBEq α] :
    ∀ {l : List α}, l.Nodup → ∀ x : α, l.count x ≤ 1
  | [], _, _ => by simp
  | a :: l, h, x => by
    rw [List.count_cons]
    have h' := List.nodup_cons.mp h
    by_cases hax : a = x
    · subst hax
      have : l.count a = 0 := List.count_eq_zero.mpr h'.1
      simp [this]
    · have := count_le_one_of_nodup h'.2 x
      simp [hax, this]

theorem sum_zero_of_forall' {α : Type} {l : List α} (f : α → Nat) (h : ∀ i ∈ l, f i = 0) :
    (l.map f).sum = 0 := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [h x (by simp), ih (fun i hi => h i (by simp [hi]))]

theorem nodup_of_map {α β : Type} (f : α → β) : ∀ {l : List α}, (l.map f).Nodup → l.Nodup
  | [], _ => List.nodup_nil
  | a :: l, h => by
    simp only [List.map_cons] at h
    have h' := List.nodup_cons.mp h
    refine List.nodup_cons.mpr ⟨fun ha => h'.1 (List.mem_map_of_mem ha), nodup_of_map f h'.2⟩

theorem sum_map_le_one' {α : Type} {l : List α} (hl : l.Nodup) (f : α → Nat)
    (h1 : ∀ i ∈ l, f i ≤ 1) (h2 : ∀ i ∈ l, ∀ j ∈ l, 0 < f i → 0 < f j → i = j) :
    (l.map f).sum ≤ 1 := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons]
    have hx := List.nodup_cons.mp hl
    by_cases hfx : f x = 0
    · rw [hfx, Nat.zero_add]
      exact ih hx.2 (fun i hi => h1 i (by simp [hi]))
        (fun i hi j hj => h2 i (by simp [hi]) j (by simp [hj]))
    · have hzero : (xs.map f).sum = 0 := by
        apply sum_zero_of_forall'
        intro i hi
        by_cases hfi : f i = 0
        · exact hfi
        · exfalso
          have := h2 x (by simp) i (by simp [hi]) (by omega) (by omega)
          subst this
          exact hx.1 hi
      rw [hzero]
      have := h1 x (by simp)
      omega

theorem count_flatMap_le_one {α β : Type} [BEq β] [LawfulBEq β] {l : List α} (hl : l.Nodup)
    (f : α → List β) (x : β) (h1 : ∀ a ∈ l, (f a).count x ≤ 1)
    (h2 : ∀ a ∈ l, ∀ a' ∈ l, x ∈ f a → x ∈ f a' → a = a') :
    (l.flatMap f).count x ≤ 1 := by
  rw [List.count_flatMap]
  apply sum_map_le_one' hl _ h1
  intro a ha a' ha' h h'
  exact h2 a ha a' ha' (List.count_pos_iff.mp h) (List.count_pos_iff.mp h')

theorem sum_le_countP {α : Type} (L : List α) (f : α → Nat) (q : α → Bool)
    (h : ∀ e ∈ L, f e ≤ if q e then 1 else 0) : (L.map f).sum ≤ L.countP q := by
  induction L with
  | nil => simp
  | cons e L ih =>
    simp only [List.map_cons, List.sum_cons, List.countP_cons]
    have h1 := h e (by simp)
    have h2 := ih (fun e' he' => h e' (by simp [he']))
    omega

theorem flatten_flatMap {α β : Type} (l : List α) (f : α → List (List β)) :
    (l.flatMap f).flatten = l.flatMap (fun a => (f a).flatten) := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [List.flatMap_cons, List.flatten_append, ih]

theorem flatten_map {α β : Type} (l : List α) (f : α → List β) :
    (l.map f).flatten = l.flatMap f := by
  rw [List.flatMap_def]

theorem nodup_reverse_range (n : Nat) : (List.range n).reverse.Nodup := by
  unfold List.Nodup
  rw [List.pairwise_reverse]
  exact List.nodup_range.imp (fun hab => Ne.symm hab)

/-! ### Slots of variables -/

/-- The position and slot of a copy or chain variable. -/
def slotOf (Pt R u : Nat) : Nat × Nat :=
  if u % 2 = 0 then (u / 2 / R % Pt, u / 2 % R) else (u / 2 / R, u / 2 % R)

theorem slotOf_wVal {Pt R v p r : Nat} (hp : p < Pt) (hr : r < R) :
    slotOf Pt R (wVal Pt R v p r) = (p, r) := by
  have h1 : (v * Pt + p) % Pt = p := by
    rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hp]
  simp only [slotOf, wVal_mod_two, wVal_div_two, divR hr, modR hr, h1, ↓reduceIte]

theorem slotOf_zVal {Pt R q r : Nat} (hr : r < R) : slotOf Pt R (zVal R q r) = (q, r) := by
  simp only [slotOf, zVal_mod_two, zVal_div_two, divR hr, modR hr]
  rfl

/-! ### Chains -/

def zlist {α : Type} (zp zn : Nat → α) : Nat → Nat → List α
  | _, 0 => []
  | j, n + 1 => zp j :: zn j :: zlist zp zn (j + 1) n

theorem count_chainFrom {α : Type} [BEq α] (zp zn : Nat → α) (x : α) (a : α) (rest : List α)
    (j : Nat) :
    (chainFrom zp zn a rest j).flatten.count x =
      (a :: rest).count x + (zlist zp zn j (rest.length - 2)).count x := by
  induction rest generalizing a j with
  | nil => simp [chainFrom, zlist]
  | cons b tail ih =>
    match tail, ih with
    | [], _ => simp [chainFrom, zlist]
    | [c], _ => simp [chainFrom, zlist]
    | c :: d :: rest, ih =>
      have h := ih (zn j) (j + 1)
      simp only [chainFrom, List.flatten_cons, List.count_append, h]
      simp only [List.length_cons, show rest.length + 1 + 1 + 1 - 2 = rest.length + 1 by omega,
        show rest.length + 1 + 1 - 2 = rest.length by omega, zlist, List.count_cons,
        List.count_nil]
      omega

theorem mem_zlist {α : Type} {zp zn : Nat → α} {x : α} :
    ∀ {j n : Nat}, x ∈ zlist zp zn j n → ∃ i, j ≤ i ∧ i < j + n ∧ (x = zp i ∨ x = zn i)
  | _, 0, h => by simp [zlist] at h
  | j, n + 1, h => by
    simp only [zlist, List.mem_cons] at h
    rcases h with h | h | h
    · exact ⟨j, Nat.le_refl j, by omega, Or.inl h⟩
    · exact ⟨j, Nat.le_refl j, by omega, Or.inr h⟩
    · obtain ⟨i, h1, h2, h3⟩ := mem_zlist h
      exact ⟨i, by omega, by omega, h3⟩

/-! ### The clauses replacing one entry -/

theorem zlist_nodup {R c r : Nat} (hr : r < R) :
    ∀ j n, (zlist (zpV R c r) (znV R c r) j n).Nodup
  | _, 0 => by simp [zlist]
  | j, n + 1 => by
    simp only [zlist]
    refine List.nodup_cons.mpr ⟨?_, List.nodup_cons.mpr ⟨?_, zlist_nodup hr (j + 1) n⟩⟩
    · intro h
      simp only [List.mem_cons] at h
      rcases h with h | h
      · simp [zpV, znV] at h
      · obtain ⟨i, h1, _, h3⟩ := mem_zlist h
        rcases h3 with h3 | h3 <;>
        · simp only [zpV, znV, Literal.mk.injEq] at h3
          have := (zVal_inj hr hr h3.1).1
          omega
    · intro h
      obtain ⟨i, h1, _, h3⟩ := mem_zlist h
      rcases h3 with h3 | h3 <;>
      · simp only [zpV, znV, Literal.mk.injEq] at h3
        have := (zVal_inj hr hr h3.1).1
        omega

theorem copiesV_nodup {Pt R r : Nat} (hr : r < R) (lits : Clause) (p : Nat)
    (hp : p + lits.length ≤ Pt) : (copiesV Pt R r p lits).Nodup := by
  have h := copiesV_vars_nodup hr lits p hp
  exact nodup_of_map _ h

theorem gadget_count {Pt R N : Nat} {σ : Nat → Bool} {L : List Entry}
    (hWF : WF Pt R N σ L) {e : Entry} (he : e ∈ L) (x : Literal) :
    (gadgetVal Pt R e).flatten.count x ≤
      if owns (slotOf Pt R x.var).1 (slotOf Pt R x.var).2 e then 1 else 0 := by
  obtain ⟨c0, r, lits⟩ := e
  have hlen := hWF.len _ he
  have hpos := hWF.pos _ he
  have hr := hWF.slot _ he
  simp only at hlen hpos hr
  obtain ⟨m0, ms', hms, hlen'⟩ := exists_copies_cons Pt R r c0 hlen
  have hgad : gadgetVal Pt R (c0, r, lits) = chainFrom (zpV R c0 r) (znV R c0 r) m0 ms' 1 := by
    simp only [gadgetVal, hms, gadget]
  rw [hgad, count_chainFrom, ← hms]
  have hcop := count_le_one_of_nodup (copiesV_nodup hr lits c0 hpos) x
  have hz := count_le_one_of_nodup (zlist_nodup (c := c0) hr 1 (ms'.length - 2)) x
  -- membership gives ownership
  have own_c : x ∈ copiesV Pt R r c0 lits → owns (slotOf Pt R x.var).1 (slotOf Pt R x.var).2
      (c0, r, lits) = true := by
    intro hx
    obtain ⟨v, q, h1, h2, h3⟩ := mem_copiesV_var lits c0 x.var (List.mem_map_of_mem hx)
    rw [h3, slotOf_wVal (by omega) hr]
    simp [owns]; omega
  have own_z : x ∈ zlist (zpV R c0 r) (znV R c0 r) 1 (ms'.length - 2) →
      owns (slotOf Pt R x.var).1 (slotOf Pt R x.var).2 (c0, r, lits) = true := by
    intro hx
    obtain ⟨i, h1, h2, h3⟩ := mem_zlist hx
    have hv : x.var = zVal R (c0 + i) r := by
      rcases h3 with h3 | h3 <;> rw [h3] <;> rfl
    rw [hv, slotOf_zVal hr]
    simp [owns]; omega
  have not_both : x ∈ copiesV Pt R r c0 lits → x ∉ zlist (zpV R c0 r) (znV R c0 r) 1
      (ms'.length - 2) := by
    intro hx hz'
    obtain ⟨v, q, _, _, h3⟩ := mem_copiesV_var lits c0 x.var (List.mem_map_of_mem hx)
    obtain ⟨i, _, _, h4⟩ := mem_zlist hz'
    have hv : x.var = zVal R (c0 + i) r := by
      rcases h4 with h4 | h4 <;> rw [h4] <;> rfl
    exact wVal_ne_zVal Pt R v q r (c0 + i) r (h3.symm.trans hv)
  by_cases hc : x ∈ copiesV Pt R r c0 lits
  · have h0 : (zlist (zpV R c0 r) (znV R c0 r) 1 (ms'.length - 2)).count x = 0 :=
      List.count_eq_zero.mpr (not_both hc)
    rw [own_c hc, h0]
    simpa using hcop
  · have h0 : (copiesV Pt R r c0 lits).count x = 0 := List.count_eq_zero.mpr hc
    rw [h0, Nat.zero_add]
    by_cases hzx : x ∈ zlist (zpV R c0 r) (znV R c0 r) 1 (ms'.length - 2)
    · rw [own_z hzx]; simpa using hz
    · rw [List.count_eq_zero.mpr hzx]; exact Nat.zero_le _

theorem gadgets_count {Pt R N : Nat} {σ : Nat → Bool} {L : List Entry}
    (hWF : WF Pt R N σ L) (x : Literal) : (L.flatMap (gadgetVal Pt R)).flatten.count x ≤ 1 := by
  rw [flatten_flatMap, List.count_flatMap]
  exact Nat.le_trans (sum_le_countP L _ _ (fun e he => gadget_count hWF he x))
    (hWF.unique _ _)

theorem mem_copiesV_neg {Pt R r : Nat} {x : Literal} :
    ∀ (lits : Clause) (p : Nat), x ∈ copiesV Pt R r p lits → x.positive = false
  | [], _, h => by simp [copiesV] at h
  | l :: ls, p, h => by
    simp only [copiesV, List.mem_cons] at h
    rcases h with h | h
    · rw [h]
    · exact mem_copiesV_neg ls (p + 1) h

theorem gadgets_mem {Pt R N : Nat} {σ : Nat → Bool} {L : List Entry} (hWF : WF Pt R N σ L)
    {x : Literal} (hx : x ∈ (L.flatMap (gadgetVal Pt R)).flatten) :
    x.positive = false ∨ x.var % 2 = 1 := by
  rw [flatten_flatMap, List.mem_flatMap] at hx
  obtain ⟨⟨c0, r, lits⟩, he, hx⟩ := hx
  have hlen := hWF.len _ he
  simp only at hlen
  obtain ⟨m0, ms', hms, _⟩ := exists_copies_cons Pt R r c0 hlen
  have hgad : gadgetVal Pt R (c0, r, lits) = chainFrom (zpV R c0 r) (znV R c0 r) m0 ms' 1 := by
    simp only [gadgetVal, hms, gadget]
  rw [hgad] at hx
  have hpos := List.count_pos_iff.mpr hx
  rw [count_chainFrom, ← hms] at hpos
  by_cases hc : x ∈ copiesV Pt R r c0 lits
  · left
    exact mem_copiesV_neg lits c0 hc
  · right
    have hz : x ∈ zlist (zpV R c0 r) (znV R c0 r) 1 (ms'.length - 2) := by
      rw [List.count_eq_zero.mpr hc, Nat.zero_add] at hpos
      exact List.count_pos_iff.mp hpos
    obtain ⟨i, _, _, h3⟩ := mem_zlist hz
    rcases h3 with h3 | h3 <;> rw [h3] <;> exact zVal_mod_two _ _ _

/-! ### The cycles -/

theorem succ_mod_inj {Pt p p' : Nat} (hp : p < Pt) (hp' : p' < Pt)
    (h : (p + 1) % Pt = (p' + 1) % Pt) : p = p' := by
  by_cases h1 : p + 1 < Pt <;> by_cases h2 : p' + 1 < Pt
  · rw [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2] at h; omega
  · rw [Nat.mod_eq_of_lt h1, show p' + 1 = Pt by omega, Nat.mod_self] at h; omega
  · rw [Nat.mod_eq_of_lt h2, show p + 1 = Pt by omega, Nat.mod_self] at h; omega
  · omega

theorem nextSlot_inj {Pt R p r p' r' : Nat} (hp : p < Pt) (hp' : p' < Pt) (hr : r < R)
    (hr' : r' < R) (h : nextSlot Pt R p r = nextSlot Pt R p' r') : p = p' ∧ r = r' := by
  unfold nextSlot at h
  split at h <;> split at h
  · simp only [Prod.mk.injEq] at h; omega
  · simp only [Prod.mk.injEq] at h; omega
  · simp only [Prod.mk.injEq] at h; omega
  · simp only [Prod.mk.injEq] at h
    exact ⟨succ_mod_inj hp hp' h.1, by omega⟩

theorem cycle_mem_unique {Pt R : Nat} (σ : Nat → Bool) (hR : 2 ≤ R) {x : Literal}
    {v p r v' p' r' : Nat} (hp : p < Pt) (hr : r < R) (hp' : p' < Pt) (hr' : r' < R)
    (h : x ∈ cycleClause Pt R σ v p r) (h' : x ∈ cycleClause Pt R σ v' p' r') :
    v = v' ∧ p = p' ∧ r = r' := by
  obtain ⟨n1, n2⟩ := nextSlot_lt (Pt := Pt) (R := R) (p := p) (r := r) hp (by omega)
  obtain ⟨n1', n2'⟩ := nextSlot_lt (Pt := Pt) (R := R) (p := p') (r := r') hp' (by omega)
  simp only [cycleClause, List.mem_cons, List.not_mem_nil, or_false] at h h'
  rcases h with h | h <;> rcases h' with h' | h' <;> rw [h] at h' <;>
    simp only [Literal.mk.injEq] at h'
  · exact wVal_inj hp hp' hr hr' h'.1
  · exfalso
    obtain ⟨_, e1, _⟩ := wVal_inj hp n1' hr n2' h'.1
    rw [e1] at h'
    cases hs : σ (nextSlot Pt R p' r').1 <;> simp [hs] at h'
  · exfalso
    obtain ⟨_, e1, _⟩ := wVal_inj n1 hp' n2 hr' h'.1
    rw [← e1] at h'
    cases hs : σ (nextSlot Pt R p r).1 <;> simp [hs] at h'
  · obtain ⟨e0, e1, e2⟩ := wVal_inj n1 n1' n2 n2' h'.1
    have := nextSlot_inj hp hp' hr hr' (Prod.ext e1 e2)
    exact ⟨e0, this⟩

theorem cycleClause_count {Pt R : Nat} (σ : Nat → Bool) (hR : 2 ≤ R) {v p r : Nat}
    (hp : p < Pt) (hr : r < R) (x : Literal) : (cycleClause Pt R σ v p r).count x ≤ 1 := by
  apply count_le_one_of_nodup _ x
  exact nodup_of_map _ (cycle_shape σ hR hp hr).2

theorem cycles_flatten (N Pt R : Nat) (σ : Nat → Bool) :
    (cyclesVal N Pt R σ).flatten = (List.range N).reverse.flatMap (fun v =>
      (List.range Pt).flatMap (fun p => (List.range R).reverse.flatMap (fun r =>
        cycleClause Pt R σ v p r))) := by
  simp only [cyclesVal, flatten_flatMap, flatten_map]

theorem cycles_count {N Pt R : Nat} (σ : Nat → Bool) (hR : 2 ≤ R) (x : Literal) :
    (cyclesVal N Pt R σ).flatten.count x ≤ 1 := by
  rw [cycles_flatten]
  apply count_flatMap_le_one (nodup_reverse_range N)
  · intro v _
    apply count_flatMap_le_one List.nodup_range
    · intro p hp
      simp only [List.mem_range] at hp
      apply count_flatMap_le_one (nodup_reverse_range R)
      · intro r hr
        simp only [List.mem_reverse, List.mem_range] at hr
        exact cycleClause_count σ hR hp hr x
      · intro r hr r' hr' h h'
        simp only [List.mem_reverse, List.mem_range] at hr hr'
        exact (cycle_mem_unique σ hR hp hr hp hr' h h').2.2
    · intro p hp p' hp' h h'
      simp only [List.mem_range, List.mem_flatMap, List.mem_reverse] at hp hp' h h'
      obtain ⟨r, hr, h⟩ := h
      obtain ⟨r', hr', h'⟩ := h'
      exact (cycle_mem_unique σ hR hp hr hp' hr' h h').2.1
  · intro v _ v' _ h h'
    simp only [List.mem_range, List.mem_flatMap, List.mem_reverse] at h h'
    obtain ⟨p, hp, r, hr, h⟩ := h
    obtain ⟨p', hp', r', hr', h'⟩ := h'
    exact (cycle_mem_unique σ hR hp hr hp' hr' h h').1

theorem cycles_mem {N Pt R : Nat} {σ : Nat → Bool} (x : Literal)
    (hx : x ∈ (cyclesVal N Pt R σ).flatten) : x.var % 2 = 0 := by
  rw [cycles_flatten] at hx
  simp only [List.mem_flatMap, List.mem_reverse, List.mem_range] at hx
  obtain ⟨v, _, p, _, r, _, hx⟩ := hx
  simp only [cycleClause, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with hx | hx <;> rw [hx] <;> exact wVal_mod_two _ _ _ _ _

/-! ### Occurrence filters as counts -/

theorem beq_lit (w v : Nat) (s : Bool) : w.beq v = ((⟨w, s⟩ : Literal) == ⟨v, s⟩) := by
  cases h : w.beq v
  · have := Nat.ne_of_beq_eq_false h
    simp [this]
  · have := Nat.eq_of_beq_eq_true h
    subst this
    simp

theorem filter_pos_count (l : List Literal) (v : Nat) :
    (l.filter fun x => x.positive && Nat.beq x.var v).length = l.count ⟨v, true⟩ := by
  rw [List.count_eq_countP, List.countP_eq_length_filter]
  congr 2
  funext x
  rcases x with ⟨w, s⟩
  cases s
  · simp
  · simpa using beq_lit w v true

theorem filter_neg_count (l : List Literal) (v : Nat) :
    (l.filter fun x => !x.positive && Nat.beq x.var v).length = l.count ⟨v, false⟩ := by
  rw [List.count_eq_countP, List.countP_eq_length_filter]
  congr 2
  funext x
  rcases x with ⟨w, s⟩
  cases s
  · simpa using beq_lit w v false
  · simp

/-! ### Occurrences in the output -/

theorem output_counts {Pt R N : Nat} {σ : Nat → Bool} {L : List Entry}
    (hWF : WF Pt R N σ L) (hR : 2 ≤ R) (v : Nat) :
    (output Pt R N σ L).flatten.count ⟨v, true⟩ ≤ 1 ∧
      (output Pt R N σ L).flatten.count ⟨v, false⟩ ≤ 2 := by
  have hsplit : ∀ x, (output Pt R N σ L).flatten.count x =
      (L.flatMap (gadgetVal Pt R)).flatten.count x + (cyclesVal N Pt R σ).flatten.count x := by
    intro x
    simp only [output, List.flatten_append, List.count_append]
  constructor
  · rw [hsplit]
    by_cases hv : v % 2 = 0
    · have : (L.flatMap (gadgetVal Pt R)).flatten.count ⟨v, true⟩ = 0 := by
        apply List.count_eq_zero.mpr
        intro hx
        rcases gadgets_mem hWF hx with h | h
        · simp at h
        · simp at h; omega
      rw [this]
      exact Nat.le_trans (Nat.le_of_eq (Nat.zero_add _)) (cycles_count σ hR _)
    · have : (cyclesVal N Pt R σ).flatten.count ⟨v, true⟩ = 0 := by
        apply List.count_eq_zero.mpr
        intro hx
        have := cycles_mem _ hx
        simp at this; omega
      rw [this, Nat.add_zero]
      exact gadgets_count hWF _
  · rw [hsplit]
    have := gadgets_count hWF ⟨v, false⟩
    have := cycles_count (N := N) (Pt := Pt) σ hR ⟨v, false⟩
    omega

end Complexity.Restricted
