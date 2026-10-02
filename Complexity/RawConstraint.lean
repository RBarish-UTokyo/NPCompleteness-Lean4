module

public import Complexity.LocalConstraint
public import Complexity.Tableau

/-!
Natural-number views of finite constraint trees. They expose index arithmetic
for a uniform generator, while retaining the exact forbidden-clause encoding.
-/

@[expose] public section

namespace Complexity.RawConstraint

open LocalConstraint

inductive Tree (d : Nat) where
  | value (v : Fin (d + 1))
  | query (slot : Nat) (branches : Fin (d + 1) → Tree d)

def literal (d slot value : Nat) : SAT.Literal := ⟨slot * (d + 1) + value, false⟩

def Tree.encode {d : Nat} (target : Nat) : Tree d → SAT.CNF
  | .value val =>
    ((List.finRange (d + 1)).filter (fun other => other != val)).map
      (fun other => [literal d target other.val])
  | .query slot branches =>
    (List.finRange (d + 1)).flatMap (fun value =>
      ((branches value).encode target).map (List.cons (literal d slot value.val)))

def ofTree {m d : Nat} (index : Fin m → Nat) : LocalConstraint.Tree m d → Tree d
  | .value val => .value val
  | .query slot branches => .query (index slot) (fun value => ofTree index (branches value))

def clause {m d : Nat} (index : Fin m → Nat) (tuple : CSPSAT.ForbiddenTuple m d) :
    SAT.Clause := tuple.map (fun atom => literal d (index atom.1) atom.2.val)

theorem map_guard {m d : Nat} (index : Fin m → Nat) (atom : CSPSAT.Atom m d)
    (I : CSPSAT.Instance m d) :
    (guard atom I).map (clause index) =
      (I.map (clause index)).map (List.cons (literal d (index atom.1) atom.2.val)) := by
  simp [LocalConstraint.guard, clause, List.map_map]

theorem encode_ofTree {m d : Nat} (tree : LocalConstraint.Tree m d)
    (index : Fin m → Nat) (target : Fin m) :
    (ofTree index tree).encode (index target) = (tree.encode target).map (clause index) := by
  induction tree with
  | value value => simp [ofTree, Tree.encode, LocalConstraint.Tree.encode, clause, List.map_map]
  | query slot branches ih =>
    simp only [ofTree, Tree.encode, LocalConstraint.Tree.encode, List.map_flatMap,
      map_guard, ih]

@[simp] theorem clause_val {m d : Nat} (tuple : CSPSAT.ForbiddenTuple m d) :
    clause Fin.val tuple = CSPSAT.forbiddenClause tuple := rfl

theorem encode_ofTree_val {m d : Nat} (tree : LocalConstraint.Tree m d) (target : Fin m) :
    (ofTree Fin.val tree).encode target.val =
      (tree.encode target).map CSPSAT.forbiddenClause := by
  exact encode_ofTree tree Fin.val target

theorem ofTree_mapVars {m n d : Nat} (tree : LocalConstraint.Tree m d)
    (f : Fin m → Fin n) (index : Fin n → Nat) :
    ofTree index (tree.mapVars f) = ofTree (fun i => index (f i)) tree := by
  induction tree with
  | value value => rfl
  | query slot branches ih =>
    simp only [LocalConstraint.Tree.mapVars, ofTree]
    congr 1
    funext value
    exact ih value

end Complexity.RawConstraint
