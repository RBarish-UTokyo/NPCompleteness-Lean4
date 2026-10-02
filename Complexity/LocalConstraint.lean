module

public import Complexity.CSPSAT
import Lean.Elab.Tactic.Omega

/-!
Finite decision trees give explicit local constraints for a computation row.
They inspect named finite-domain slots and return one finite-domain value.
Encoding a tree produces a finite list of forbidden tuples, never an oracle
predicate or an unexplained unit-cost function.
-/

@[expose] public section

namespace Complexity.LocalConstraint

open CSPSAT

inductive Tree (m d : Nat) where
  | value (v : Fin (d + 1))
  | query (slot : Fin m) (branches : Fin (d + 1) → Tree m d)

def Tree.eval {m d : Nat} (v : Valuation m d) : Tree m d → Fin (d + 1)
  | .value val => val
  | .query slot branches => (branches (v slot)).eval v

def guard {m d : Nat} (atom : Atom m d) (I : Instance m d) : Instance m d :=
  I.map (fun tuple => atom :: tuple)

def Tree.encode {m d : Nat} (target : Fin m) : Tree m d → Instance m d
  | .value val =>
    ((List.finRange (d + 1)).filter (fun other => other != val)).map
      (fun other => [(target, other)])
  | .query slot branches =>
    (List.finRange (d + 1)).flatMap
      (fun value => guard (slot, value) ((branches value).encode target))

theorem satisfied_guard_iff {m d : Nat} (v : Valuation m d)
    (atom : Atom m d) (I : Instance m d) :
    Satisfied v (guard atom I) ↔ (v atom.1 = atom.2 → Satisfied v I) := by
  constructor
  · intro h heq tuple ht
    have hh := h (atom :: tuple) (List.mem_map.mpr ⟨tuple, ht, rfl⟩)
    obtain ⟨a, ha, hd⟩ := hh
    rcases List.mem_cons.mp ha with ha | ha
    · subst a
      exact False.elim (hd heq)
    · exact ⟨a, ha, hd⟩
  · intro h tuple ht
    obtain ⟨rest, hr, rfl⟩ := List.mem_map.mp ht
    by_cases heq : v atom.1 = atom.2
    · obtain ⟨a, ha, hd⟩ := h heq rest hr
      exact ⟨a, List.mem_cons_of_mem atom ha, hd⟩
    · exact ⟨atom, List.mem_cons_self, heq⟩

theorem satisfied_flatMap_iff {m d : Nat} {α : Type}
    (v : Valuation m d) (xs : List α) (f : α → Instance m d) :
    Satisfied v (xs.flatMap f) ↔ ∀ a ∈ xs, Satisfied v (f a) := by
  constructor
  · intro h a ha tuple ht
    exact h tuple (List.mem_flatMap.mpr ⟨a, ha, ht⟩)
  · intro h tuple ht
    obtain ⟨a, ha, ht⟩ := List.mem_flatMap.mp ht
    exact h a ha tuple ht

theorem value_encode_correct {m d : Nat} (v : Valuation m d)
    (target : Fin m) (value : Fin (d + 1)) :
    Satisfied v ((Tree.value value).encode target) ↔ v target = value := by
  constructor
  · intro h
    by_cases heq : v target = value
    · exact heq
    have hne := heq
    apply False.elim
    have hm : v target ∈ (List.finRange (d + 1)).filter (fun other => other != value) := by
      simp [hne]
    have hh := h [(target, v target)] (List.mem_map.mpr ⟨v target, hm, rfl⟩)
    obtain ⟨atom, ha, hn⟩ := hh
    simp only [List.mem_singleton] at ha
    subst atom
    exact hn rfl
  · intro h tuple ht
    obtain ⟨other, ho, rfl⟩ := List.mem_map.mp ht
    have hn : other ≠ value := by simpa using (List.mem_filter.mp ho).2
    exact ⟨(target, other), List.mem_cons_self, by simpa [h] using Ne.symm hn⟩

/-- Local constraints exactly express the tree's output equality. -/
theorem encode_correct {m d : Nat} (tree : Tree m d)
    (v : Valuation m d) (target : Fin m) :
    Satisfied v (tree.encode target) ↔ v target = tree.eval v := by
  induction tree with
  | value value => exact value_encode_correct v target value
  | query slot branches ih =>
    simp only [Tree.encode, satisfied_flatMap_iff, List.mem_finRange, true_implies,
      satisfied_guard_iff, ih, Tree.eval]
    constructor
    · intro h
      exact h (v slot) rfl
    · intro h value hv
      simpa [← hv] using h

/-- Each generated tuple consists of a branch path followed by one output atom.
The number and lengths depend only on the finite syntax of the tree. -/
def Tree.leaves {m d : Nat} : Tree m d → Nat
  | .value _ => 1
  | .query _ branches => ((List.finRange (d + 1)).map (fun v => (branches v).leaves)).sum

theorem guard_length {m d : Nat} (a : Atom m d) (I : Instance m d) :
    (guard a I).length = I.length := by simp [guard]

theorem encode_length_le {m d : Nat} (tree : Tree m d) (target : Fin m) :
    (tree.encode target).length ≤ (d + 1) * tree.leaves := by
  induction tree with
  | value value =>
    simpa [Tree.encode, Tree.leaves] using
      List.length_filter_le (fun other : Fin (d + 1) => other != value) (List.finRange (d + 1))
  | query slot branches ih =>
    simp only [Tree.encode, List.length_flatMap, Tree.leaves]
    have h : ∀ xs : List (Fin (d + 1)),
        (xs.map (fun value => (guard (slot, value) ((branches value).encode target)).length)).sum ≤
        (d + 1) * (xs.map (fun value => (branches value).leaves)).sum := by
      intro xs
      induction xs with
      | nil => simp
      | cons value rest hr =>
        simp only [List.map_cons, List.sum_cons, guard_length, Nat.mul_add]
        exact Nat.add_le_add (ih value) (by simpa only [guard_length] using hr)
    exact h _

end Complexity.LocalConstraint
