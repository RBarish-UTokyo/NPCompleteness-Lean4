module

public import Complexity.SAT
public import Complexity.Planarity

/-!
# Planar 3-SAT

Two planar restrictions of 3-SAT, through the variable–clause incidence graph of a formula
(a vertex per variable and per clause, an edge per occurrence of a variable in a clause):

* `PlanarThreeSAT`: the incidence graph is planar;
* `CyclePlanarThreeSAT` (Lichtenstein's planar 3-SAT): the incidence graph stays planar after
  adding the cycle through the variables `0, 1, …, n - 1` in order.
-/

@[expose] public section

namespace Complexity.SAT

/-- The variable–clause incidence graph of `f`, as a list of edges: one edge between the
variable `.inl v` and the clause `.inr j` for each occurrence of `v` in the `j`-th clause. -/
def incidenceGraph (f : CNF) : List (Sum Nat Nat × Sum Nat Nat) :=
  f.zipIdx.flatMap fun p => p.1.map fun l => (Sum.inl l.var, Sum.inr p.2)

/-- One more than the largest variable occurring in `f`, or `0` if `f` has no literal. -/
def variableCount (f : CNF) : Nat :=
  f.flatten.foldr (fun l n => Nat.max (l.var + 1) n) 0

/-- The cycle through the variables `0, 1, …, variableCount f - 1`, in this order. -/
def variableCycle (f : CNF) : List (Sum Nat Nat × Sum Nat Nat) :=
  (List.range (variableCount f)).map fun v =>
    (Sum.inl v, Sum.inl ((v + 1) % variableCount f))

/-- Planar 3-CNF: every clause has at most three literals, and the incidence graph is
planar. -/
def IsPlanarThreeCNF (f : CNF) : Prop :=
  IsThreeCNF f ∧ PlanarGraph (incidenceGraph f)

/-- Planar 3-SAT: the words `encode f` with `f` satisfiable and planar 3-CNF. -/
def PlanarThreeSAT (input : Word) : Prop :=
  ∃ f, encode f = input ∧ IsPlanarThreeCNF f ∧ Satisfiable f

/-- Lichtenstein's planar 3-CNF: every clause has at most three literals, and the incidence
graph together with the cycle through the variables is planar. -/
def IsCyclePlanarThreeCNF (f : CNF) : Prop :=
  IsThreeCNF f ∧ PlanarGraph (incidenceGraph f ++ variableCycle f)

/-- Lichtenstein's planar 3-SAT: the words `encode f` with `f` satisfiable and satisfying
`IsCyclePlanarThreeCNF`. -/
def CyclePlanarThreeSAT (input : Word) : Prop :=
  ∃ f, encode f = input ∧ IsCyclePlanarThreeCNF f ∧ Satisfiable f

end Complexity.SAT
