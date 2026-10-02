module

public import Complexity.EmitterTools
public import Complexity.InitialWord
public import Complexity.Tableau

/-!
Clause-order and reindexing lemmas for streaming computation-tableau generators.
-/

@[expose] public section

namespace Complexity.StackTableauEmitter

open FiniteRows

theorem equivalent_flatMap {α : Type} (xs : List α) (f g : α → SAT.CNF)
    (h : ∀ x ∈ xs, Equivalent (f x) (g x)) :
    Equivalent (xs.flatMap f) (xs.flatMap g) := by
  intro a
  simp only [CSPSAT.evalCNF_flatMap_iff]
  constructor
  · intro hf x hx
    exact (h x hx a).mp (hf x hx)
  · intro hg x hx
    exact (h x hx a).mpr (hg x hx)

theorem equivalent_cell_partition (width : Nat) (f : Slot width → SAT.CNF) :
    Equivalent (f (stateSlot width) ++
      (List.finRange width).flatMap (fun i => f (leftSlot width i)) ++
      (List.finRange width).flatMap (fun i => f (rightSlot width i)))
      ((List.finRange (2 * width + 1)).flatMap f) := by
  apply equivalent_of_membership
  intro clause
  simp only [List.mem_append, List.mem_flatMap, List.mem_finRange, true_and]
  constructor
  · rintro ((h | ⟨i, hi⟩) | ⟨i, hi⟩)
    · exact ⟨stateSlot width, h⟩
    · exact ⟨leftSlot width i, hi⟩
    · exact ⟨rightSlot width i, hi⟩
  · rintro ⟨slot, h⟩
    rcases slot_cases slot with rfl | ⟨i, rfl⟩ | ⟨i, rfl⟩
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr ⟨i, h⟩)
    · exact Or.inr ⟨i, h⟩

theorem forbiddenClause_mapTuple {m n d : Nat} (f : Fin m → Fin n)
    (tuple : CSPSAT.ForbiddenTuple m d) :
    CSPSAT.forbiddenClause (Tableau.mapTuple f tuple) =
      RawConstraint.clause (fun i => (f i).val) tuple := by
  simp [CSPSAT.forbiddenClause, Tableau.mapTuple, RawConstraint.clause,
    RawConstraint.literal, CSPSAT.atomIndex, List.map_map]

theorem forbiddenClauses_mapInstance {m n d : Nat} (f : Fin m → Fin n)
    (I : CSPSAT.Instance m d) :
    (Tableau.mapInstance f I).map CSPSAT.forbiddenClause =
      I.map (RawConstraint.clause (fun i => (f i).val)) := by
  simp [Tableau.mapInstance, List.map_map, forbiddenClause_mapTuple]

theorem forbiddenClauses_mapInstance_zero {w d : Nat} (T : Nat)
    (I : CSPSAT.Instance (w + 1) d) :
    (Tableau.mapInstance (Tableau.cell (T := T) (0 : Fin (T + 1))) I).map
      CSPSAT.forbiddenClause = I.map CSPSAT.forbiddenClause := by
  rw [forbiddenClauses_mapInstance]
  simp only [Tableau.cell, Fin.val_zero, Nat.zero_mul, Nat.zero_add]
  rfl

theorem mapInstance_pin {m n d : Nat} (f : Fin m → Fin n)
    (slot : Fin m) (value : Fin (d + 1)) :
    Tableau.mapInstance f (InitialWord.pin slot value) = InitialWord.pin (f slot) value := by
  simp [Tableau.mapInstance, Tableau.mapTuple, InitialWord.pin,
    LocalConstraint.Tree.encode, List.map_map]

end Complexity.StackTableauEmitter
