module

public import Complexity.LocalConstraint
import Lean.Elab.Tactic.Omega

/-!
Unroll a finite-row transition system into a finite-domain constraint instance,
then use the proved one-hot translation to obtain CNF. Each transition is an
explicit finite decision tree. This module establishes semantic correctness and
structural bounds, not a Turing-machine implementation or a runtime bound.
-/

@[expose] public section

namespace Complexity.LocalConstraint

def Tree.mapVars {m n d : Nat} (f : Fin m → Fin n) : Tree m d → Tree n d
  | .value val => .value val
  | .query slot branches => .query (f slot) (fun val => (branches val).mapVars f)

theorem Tree.eval_mapVars {m n d : Nat} (tree : Tree m d) (f : Fin m → Fin n)
    (v : CSPSAT.Valuation n d) :
    (tree.mapVars f).eval v = tree.eval (fun i => v (f i)) := by
  induction tree with
  | value value => rfl
  | query slot branches ih => simp [Tree.mapVars, Tree.eval, ih]

@[simp] theorem Tree.mapVars_leaves {m n d : Nat} (tree : Tree m d) (f : Fin m → Fin n) :
    (tree.mapVars f).leaves = tree.leaves := by
  induction tree with
  | value value => rfl
  | query slot branches ih => simp [Tree.mapVars, Tree.leaves, ih]

end Complexity.LocalConstraint

namespace Complexity.Tableau

open Complexity.CSPSAT Complexity.LocalConstraint

abbrev Row (w d : Nat) := Valuation (w + 1) d
abbrev System (w d : Nat) := Fin (w + 1) → Tree (w + 1) d

def next {w d : Nat} (system : System w d) (row : Row w d) : Row w d :=
  fun i => (system i).eval row

def iterate {w d : Nat} (system : System w d) : Nat → Row w d → Row w d
  | 0, row => row
  | time + 1, row => next system (iterate system time row)

/-- Flatten time and cell coordinates into the finite tableau domain. -/
def cell {T w : Nat} (time : Fin (T + 1)) (position : Fin (w + 1)) :
    Fin ((T + 1) * (w + 1)) :=
  ⟨time.val * (w + 1) + position.val, atomIndex_lt (time, position)⟩

theorem cell_injective {T w : Nat} {t t' : Fin (T + 1)} {i i' : Fin (w + 1)}
    (h : cell t i = cell t' i') : t = t' ∧ i = i' := by
  have heq := atomIndex_injective (x := (t, i)) (y := (t', i')) (congrArg Fin.val h)
  exact ⟨congrArg Prod.fst heq, congrArg Prod.snd heq⟩

def rowAt {T w d : Nat} (history : Valuation ((T + 1) * (w + 1)) d)
    (time : Fin (T + 1)) : Row w d :=
  fun position => history (cell time position)

def mapTuple {m n d : Nat} (f : Fin m → Fin n) (tuple : ForbiddenTuple m d) :
    ForbiddenTuple n d := tuple.map (fun atom => (f atom.1, atom.2))

def mapInstance {m n d : Nat} (f : Fin m → Fin n) (problem : Instance m d) :
    Instance n d := problem.map (mapTuple f)

theorem mapTuple_correct {m n d : Nat} (f : Fin m → Fin n) (v : Valuation n d)
    (tuple : ForbiddenTuple m d) :
    TupleSatisfied v (mapTuple f tuple) ↔ TupleSatisfied (fun i => v (f i)) tuple := by
  constructor
  · rintro ⟨atom, ha, hne⟩
    obtain ⟨original, horiginal, rfl⟩ := List.mem_map.mp ha
    exact ⟨original, horiginal, hne⟩
  · rintro ⟨atom, ha, hne⟩
    exact ⟨(f atom.1, atom.2), List.mem_map.mpr ⟨atom, ha, rfl⟩, hne⟩

theorem mapInstance_correct {m n d : Nat} (f : Fin m → Fin n) (v : Valuation n d)
    (problem : Instance m d) :
    Satisfied v (mapInstance f problem) ↔ Satisfied (fun i => v (f i)) problem := by
  constructor
  · intro h tuple ht
    apply (mapTuple_correct f v tuple).mp
    exact h _ (List.mem_map.mpr ⟨tuple, ht, rfl⟩)
  · intro h tuple ht
    obtain ⟨original, horiginal, rfl⟩ := List.mem_map.mp ht
    exact (mapTuple_correct f v original).mpr (h original horiginal)

theorem satisfied_append_iff {m d : Nat} (v : Valuation m d) (first second : Instance m d) :
    Satisfied v (first ++ second) ↔ Satisfied v first ∧ Satisfied v second := by
  simp [Satisfied, List.mem_append, or_imp, forall_and]

/-- One time step supplies an output constraint for each cell of the next row. -/
def transitionRow {w d : Nat} (system : System w d) (T : Nat) (time : Fin T) :
    Instance ((T + 1) * (w + 1)) d :=
  (List.finRange (w + 1)).flatMap (fun position =>
    ((system position).mapVars (cell time.castSucc)).encode (cell time.succ position))

def transitions {w d : Nat} (system : System w d) (T : Nat) :
    Instance ((T + 1) * (w + 1)) d :=
  (List.finRange T).flatMap (transitionRow system T)

def problem {w d : Nat} (system : System w d) (T : Nat)
    (initial final : Instance (w + 1) d) : Instance ((T + 1) * (w + 1)) d :=
  mapInstance (cell (0 : Fin (T + 1))) initial ++
    (transitions system T ++ mapInstance (cell (Fin.last T)) final)

theorem transitionRow_correct {w d : Nat} (system : System w d) (T : Nat)
    (history : Valuation ((T + 1) * (w + 1)) d) (time : Fin T) :
    Satisfied history (transitionRow system T time) ↔
      rowAt history time.succ = next system (rowAt history time.castSucc) := by
  simp only [transitionRow, satisfied_flatMap_iff, List.mem_finRange, true_implies,
    LocalConstraint.encode_correct, Tree.eval_mapVars]
  constructor
  · intro h
    funext i
    exact h i
  · intro h i
    exact congrFun h i

theorem transitions_correct {w d : Nat} (system : System w d) (T : Nat)
    (history : Valuation ((T + 1) * (w + 1)) d) :
    Satisfied history (transitions system T) ↔
      ∀ time : Fin T, rowAt history time.succ = next system (rowAt history time.castSucc) := by
  simp [transitions, satisfied_flatMap_iff, List.mem_finRange, transitionRow_correct]

theorem problem_correct {w d : Nat} (system : System w d) (T : Nat)
    (initial final : Instance (w + 1) d) (history : Valuation ((T + 1) * (w + 1)) d) :
    Satisfied history (problem system T initial final) ↔
      Satisfied (rowAt history 0) initial ∧
      (∀ time : Fin T, rowAt history time.succ = next system (rowAt history time.castSucc)) ∧
      Satisfied (rowAt history (Fin.last T)) final := by
  simp only [problem, satisfied_append_iff, mapInstance_correct, transitions_correct]
  rfl

/-- Serialize the genuine iterated computation into a valuation of all cells. -/
def historyOf {w d : Nat} (system : System w d) (T : Nat) (initial : Row w d) :
    Valuation ((T + 1) * (w + 1)) d :=
  fun index => iterate system (index.val / (w + 1)) initial
    ⟨index.val % (w + 1), Nat.mod_lt _ (by omega)⟩

theorem historyOf_row {w d : Nat} (system : System w d) (T : Nat) (initial : Row w d)
    (time : Fin (T + 1)) :
    rowAt (historyOf system T initial) time = iterate system time.val initial := by
  funext i
  have hdiv : (time.val * (w + 1) + i.val) / (w + 1) = time.val := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt i.isLt]
    simp
  have hmod : (time.val * (w + 1) + i.val) % (w + 1) = i.val := by
    rw [Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt i.isLt]
  simp [rowAt, historyOf, cell, hdiv, hmod]

theorem rowAt_iterate_of_transitions {w d : Nat} (system : System w d) (T : Nat)
    (history : Valuation ((T + 1) * (w + 1)) d)
    (h : ∀ time : Fin T, rowAt history time.succ = next system (rowAt history time.castSucc))
    (time : Fin (T + 1)) :
    rowAt history time = iterate system time.val (rowAt history 0) := by
  induction time using Fin.induction with
  | zero => rfl
  | succ time ih =>
      exact (h time).trans (congrArg (next system) ih)

/-- The generated CNF is satisfiable exactly when an allowed initial row evolves
in precisely `T` steps to a row satisfying the final constraints. -/
theorem satisfiable_encode_iff {w d : Nat} (system : System w d) (T : Nat)
    (initial final : Instance (w + 1) d) :
    SAT.Satisfiable (CSPSAT.encode (problem system T initial final)) ↔
      ∃ row : Row w d, Satisfied row initial ∧ Satisfied (iterate system T row) final := by
  rw [CSPSAT.satisfiable_encode_iff]
  constructor
  · rintro ⟨history, hhistory⟩
    obtain ⟨hi, ht, hf⟩ := (problem_correct system T initial final history).mp hhistory
    refine ⟨rowAt history 0, hi, ?_⟩
    have hlast := rowAt_iterate_of_transitions system T history ht (Fin.last T)
    rw [hlast] at hf
    exact hf
  · rintro ⟨row, hi, hf⟩
    refine ⟨historyOf system T row, ?_⟩
    apply (problem_correct system T initial final _).mpr
    refine ⟨?_, ?_, ?_⟩
    · simpa only [historyOf_row, Fin.val_zero, iterate] using hi
    · intro time
      simp only [historyOf_row, Fin.val_succ, Fin.val_castSucc, iterate]
    · simpa only [historyOf_row, Fin.val_last] using hf

/-- Sum of the finite decision-tree leaf counts for all cells in one row. -/
def systemLeaves {w d : Nat} (system : System w d) : Nat :=
  ((List.finRange (w + 1)).map (fun position => (system position).leaves)).sum

theorem transitionRow_length_le {w d : Nat} (system : System w d) (T : Nat) (time : Fin T) :
    (transitionRow system T time).length ≤ (d + 1) * systemLeaves system := by
  have h : ∀ positions : List (Fin (w + 1)),
      (positions.flatMap (fun position =>
        ((system position).mapVars (cell time.castSucc)).encode (cell time.succ position))).length ≤
      (d + 1) * (positions.map (fun position => (system position).leaves)).sum := by
    intro positions
    induction positions with
    | nil => simp
    | cons position rest ih =>
      have hp := LocalConstraint.encode_length_le
        ((system position).mapVars (cell time.castSucc)) (cell time.succ position)
      simp only [Tree.mapVars_leaves] at hp
      simp only [List.flatMap_cons, List.length_append, List.map_cons, List.sum_cons,
        Nat.mul_add]
      exact Nat.add_le_add hp ih
  exact h _

theorem transitions_length_le {w d : Nat} (system : System w d) (T : Nat) :
    (transitions system T).length ≤ T * ((d + 1) * systemLeaves system) := by
  have h := flatMap_length_le (List.finRange T) (transitionRow system T)
    ((d + 1) * systemLeaves system) (by
      intro time _
      exact transitionRow_length_le system T time)
  simpa [transitions] using h

theorem problem_length_le {w d : Nat} (system : System w d) (T : Nat)
    (initial final : Instance (w + 1) d) :
    (problem system T initial final).length ≤
      initial.length + T * ((d + 1) * systemLeaves system) + final.length := by
  have h := transitions_length_le system T
  simp only [problem, List.length_append, mapInstance, List.length_map]
  omega

theorem cnf_length_le {w d : Nat} (system : System w d) (T : Nat)
    (initial final : Instance (w + 1) d) :
    (CSPSAT.encode (problem system T initial final)).length ≤
      ((T + 1) * (w + 1)) * ((d + 1) * (d + 1) + 1) +
      initial.length + T * ((d + 1) * systemLeaves system) + final.length := by
  have hc := CSPSAT.encode_length_le (problem system T initial final)
  have hp := problem_length_le system T initial final
  omega

end Complexity.Tableau
