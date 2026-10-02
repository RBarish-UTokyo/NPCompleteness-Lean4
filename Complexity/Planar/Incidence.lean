module

public import Complexity.PlanarSAT
import Lean.Elab.Tactic.Omega

/-!
# The edges of incidence graphs

Index computations for `incidenceGraph`, `variableCycle`, `variableCount` and `halfEdgeEnd`:
the `e`-th edge of the incidence graph joins the variable of the `e`-th literal occurrence to
its clause, occurrences being numbered clause after clause.
-/

@[expose] public section

namespace Complexity.Planar

open SAT

/-- Indexing a concatenation of lists by block offsets. -/
theorem getElem?_flatten_offset {α : Type} (ls : List (List α)) (j t : Nat)
    (hj : j < ls.length) (ht : t < ls[j].length) :
    ls.flatten[((ls.map List.length).take j).sum + t]? = ls[j][t]? := by
  induction ls generalizing j with
  | nil => simp at hj
  | cons l ls ih =>
    cases j with
    | zero =>
      simp only [List.flatten_cons, List.take_zero, List.sum_nil, Nat.zero_add,
        List.getElem_cons_zero] at ht ⊢
      rw [List.getElem?_append_left ht]
    | succ j =>
      simp only [List.flatten_cons, List.map_cons, List.take_succ_cons, List.sum_cons,
        List.getElem_cons_succ] at ht ⊢
      rw [show l.length + ((ls.map List.length).take j).sum + t =
        l.length + (((ls.map List.length).take j).sum + t) by omega,
        List.getElem?_append_right (by omega), Nat.add_sub_cancel_left]
      exact ih j (by simpa using hj) ht

theorem length_flatten' {α : Type} (ls : List (List α)) :
    ls.flatten.length = (ls.map List.length).sum := by
  induction ls with
  | nil => rfl
  | cons l ls ih => simp [ih]

/-- The incidence graph as a concatenation of blocks, one per clause. -/
theorem incidenceGraph_eq (f : CNF) :
    incidenceGraph f = (f.zipIdx.map fun p => p.1.map fun l => (Sum.inl l.var, Sum.inr p.2)).flatten := by
  rfl

theorem incidenceGraph_length (f : CNF) :
    (incidenceGraph f).length = (f.map List.length).sum := by
  rw [incidenceGraph_eq, length_flatten']
  congr 1
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp [List.getElem_zipIdx]

theorem incidenceGraph_getElem? (f : CNF) (j t : Nat) (hj : j < f.length)
    (ht : t < f[j].length) :
    (incidenceGraph f)[((f.map List.length).take j).sum + t]? =
      some (Sum.inl f[j][t].var, Sum.inr j) := by
  rw [incidenceGraph_eq]
  have hmap : ((f.zipIdx.map fun p => p.1.map fun l =>
      ((Sum.inl l.var, Sum.inr p.2) : Sum Nat Nat × Sum Nat Nat)).map List.length) =
      f.map List.length := by
    apply List.ext_getElem
    · simp
    · intro i h1 h2
      simp [List.getElem_zipIdx]
  have := getElem?_flatten_offset (f.zipIdx.map fun p => p.1.map fun l =>
      ((Sum.inl l.var, Sum.inr p.2) : Sum Nat Nat × Sum Nat Nat)) j t (by simpa using hj)
    (by simpa [List.getElem_zipIdx] using ht)
  rw [hmap] at this
  rw [this]
  simp [List.getElem_zipIdx, List.getElem?_eq_getElem ht]

/-! ## The variable cycle -/

theorem variableCycle_length (f : CNF) : (variableCycle f).length = variableCount f := by
  simp [variableCycle]

theorem variableCycle_getElem? (f : CNF) (i : Nat) (hi : i < variableCount f) :
    (variableCycle f)[i]? =
      some (Sum.inl i, Sum.inl (if i + 1 = variableCount f then 0 else i + 1)) := by
  simp only [variableCycle, List.getElem?_map, List.getElem?_range hi, Option.map_some]
  congr 3
  split
  · next h => rw [h]; simp
  · next h => exact Nat.mod_eq_of_lt (by omega)

/-- The largest variable plus one. -/
def vmax : List Literal → Nat
  | [] => 0
  | l :: ls => max (l.var + 1) (vmax ls)

theorem foldr_eq_vmax (ls : List Literal) :
    ls.foldr (fun l n => Nat.max (l.var + 1) n) 0 = vmax ls := by
  induction ls with
  | nil => rfl
  | cons l ls ih => simp [vmax, ih]

theorem le_vmax (ls : List Literal) : ∀ l ∈ ls, l.var + 1 ≤ vmax ls := by
  induction ls with
  | nil => simp
  | cons l ls ih =>
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih x hx) (Nat.le_max_right _ _)

theorem vmax_le (ls : List Literal) (K : Nat) (h : ∀ l ∈ ls, l.var < K) : vmax ls ≤ K := by
  induction ls with
  | nil => simp [vmax]
  | cons l ls ih =>
    exact Nat.max_le.mpr ⟨h l List.mem_cons_self,
      ih (fun x hx => h x (List.mem_cons_of_mem l hx))⟩

theorem vmax_attained (ls : List Literal) : vmax ls = 0 ∨ ∃ l ∈ ls, l.var + 1 = vmax ls := by
  induction ls with
  | nil => simp [vmax]
  | cons l ls ih =>
    right
    rcases Nat.le_total (l.var + 1) (vmax ls) with h | h
    · rw [vmax, Nat.max_eq_right h]
      rcases ih with h0 | ⟨x, hx, hxe⟩
      · omega
      · exact ⟨x, List.mem_cons_of_mem l hx, hxe⟩
    · rw [vmax, Nat.max_eq_left h]
      exact ⟨l, List.mem_cons_self, rfl⟩

theorem variableCount_eq_vmax (f : CNF) : variableCount f = vmax f.flatten := by
  unfold variableCount; exact foldr_eq_vmax _

/-- The variable count is determined by an upper bound that is attained. -/
theorem variableCount_eq (f : CNF) (K : Nat)
    (hlt : ∀ c ∈ f, ∀ l ∈ c, l.var < K)
    (hmax : K = 0 ∨ ∃ c ∈ f, ∃ l ∈ c, l.var + 1 = K) : variableCount f = K := by
  rw [variableCount_eq_vmax]
  have hle := vmax_le f.flatten K (fun l hl => by
    obtain ⟨c, hc, hlc⟩ := List.mem_flatten.mp hl; exact hlt c hc l hlc)
  rcases hmax with h0 | ⟨c, hc, l, hl, hlK⟩
  · omega
  · have := le_vmax f.flatten l (List.mem_flatten.mpr ⟨c, hc, hl⟩)
    omega

theorem variableCount_spec (f : CNF) :
    (∀ c ∈ f, ∀ l ∈ c, l.var < variableCount f) ∧
      (variableCount f = 0 ∨ ∃ c ∈ f, ∃ l ∈ c, l.var + 1 = variableCount f) := by
  rw [variableCount_eq_vmax]
  refine ⟨fun c hc l hl => le_vmax f.flatten l (List.mem_flatten.mpr ⟨c, hc, hl⟩), ?_⟩
  rcases vmax_attained f.flatten with h | ⟨l, hl, hle⟩
  · exact Or.inl h
  · obtain ⟨c, hc, hlc⟩ := List.mem_flatten.mp hl
    exact Or.inr ⟨c, hc, l, hlc, hle⟩

/-! ## Ends of half-edges -/

theorem halfEdgeEnd_append_left {V : Type} (es es' : List (V × V)) (d : Nat)
    (hd : d < 2 * es.length) : halfEdgeEnd (es ++ es') d = halfEdgeEnd es d := by
  unfold halfEdgeEnd
  rw [List.getElem?_append_left (by omega)]

theorem halfEdgeEnd_append_right {V : Type} (es es' : List (V × V)) (d : Nat)
    (hd : 2 * es.length ≤ d) :
    halfEdgeEnd (es ++ es') d = halfEdgeEnd es' (d - 2 * es.length) := by
  unfold halfEdgeEnd
  rw [List.getElem?_append_right (by omega)]
  have h1 : d / 2 - es.length = (d - 2 * es.length) / 2 := by omega
  have h2 : (d - 2 * es.length) % 2 = d % 2 := by omega
  rw [h1, h2]

theorem halfEdgeEnd_of_getElem? {V : Type} (es : List (V × V)) (e : Nat) (a b : V)
    (h : es[e]? = some (a, b)) :
    halfEdgeEnd es (2 * e) = some a ∧ halfEdgeEnd es (2 * e + 1) = some b := by
  unfold halfEdgeEnd
  have h1 : 2 * e / 2 = e := by omega
  have h2 : (2 * e + 1) / 2 = e := by omega
  have h3 : (2 * e + 1) % 2 = 1 := by omega
  simp [h1, h2, h3, h, Nat.mul_mod_right]

end Complexity.Planar
