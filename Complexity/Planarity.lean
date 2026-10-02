module

public import Init

/-!
# Hypermaps and planarity

A combinatorial definition of planarity, following Gonthier's formal proof of the Four Color
Theorem (Coq, `hypermap.v`): a hypermap is a triple of functions
`edge`, `node`, `face` on a finite set of darts with `node (face (edge x)) = x`, and it is
planar when its genus, computed from the Euler formula, is zero. Here the darts are `Fin n`
and every count is written with Lean core's lists.

A graph, given by its list of edges, is planar when it has a planar embedding: a planar
hypermap on its half-edges whose `edge` permutation pairs the two ends of each edge and whose
`node` cycles are the sets of half-edges at each vertex. This is the rotation-system
(combinatorial map) definition of planarity.
-/

@[expose] public section

namespace Complexity

/-- `iterate f k x` applies `f` to `x` `k` times. -/
def iterate {α : Type} (f : α → α) : Nat → α → α
  | 0, x => x
  | k + 1, x => iterate f k (f x)

/-- A hypermap on the darts `Fin n`: three functions whose composite is the identity,
`node (face (edge x)) = x`. They are then permutations of the darts. -/
structure Hypermap (n : Nat) where
  edge : Fin n → Fin n
  node : Fin n → Fin n
  face : Fin n → Fin n
  edgeK : ∀ x, node (face (edge x)) = x

/-- The number of cycles of a permutation `p` of `Fin n`: the darts `x` that are smallest
among `x, p x, p (p x), …` (a cycle has at most `n` darts). -/
def cycleCount {n : Nat} (p : Fin n → Fin n) : Nat :=
  (List.finRange n).countP fun x =>
    (List.range n).all fun i => Nat.ble x.val (iterate p i x).val

namespace Hypermap

/-- `G.linked k x y`: `y` can be reached from `x` by at most `k` steps of `edge`, `node` or
`face`. -/
def linked {n : Nat} (G : Hypermap n) : Nat → Fin n → Fin n → Bool
  | 0, x, y => Nat.beq x.val y.val
  | k + 1, x, y => G.linked k x y || (List.finRange n).any fun z =>
      G.linked k x z && (Nat.beq (G.edge z).val y.val || Nat.beq (G.node z).val y.val ||
        Nat.beq (G.face z).val y.val)

/-- The number of connected components of `G`: the darts that are smallest in their
component (a component has at most `n` darts). -/
def componentCount {n : Nat} (G : Hypermap n) : Nat :=
  (List.finRange n).countP fun x =>
    (List.finRange n).all fun y => !G.linked n x y || Nat.ble x.val y.val

/-- `2 * (number of components) + (number of darts)`. -/
def eulerLhs {n : Nat} (G : Hypermap n) : Nat :=
  2 * G.componentCount + n

/-- `(number of edges) + (number of nodes) + (number of faces)`: the cycles of the three
permutations. -/
def eulerRhs {n : Nat} (G : Hypermap n) : Nat :=
  cycleCount G.edge + cycleCount G.node + cycleCount G.face

/-- The genus of `G`, from the Euler formula. -/
def genus {n : Nat} (G : Hypermap n) : Nat :=
  (G.eulerLhs - G.eulerRhs) / 2

/-- `G` is planar: its genus is zero. -/
def Planar {n : Nat} (G : Hypermap n) : Prop :=
  G.genus = 0

end Hypermap

/-- The vertex at the end of half-edge `d` of the graph with edge list `edges`: half-edges
`2 * i` and `2 * i + 1` are the two ends of edge `i`. -/
def halfEdgeEnd {V : Type} (edges : List (V × V)) (d : Nat) : Option V :=
  (edges[d / 2]?).map fun e => cond (Nat.beq (d % 2) 0) e.1 e.2

/-- A graph, given by its list of edges (loops and repeated edges allowed), is planar: it has
a planar embedding, a planar hypermap on its half-edges whose `edge` permutation swaps the two
ends of each edge and whose `node` cycles are exactly the sets of half-edges at a common
vertex. -/
def PlanarGraph {V : Type} (edges : List (V × V)) : Prop :=
  ∃ G : Hypermap (2 * edges.length),
    (∀ d, (G.edge d).val = cond (Nat.beq (d.val % 2) 0) (d.val + 1) (d.val - 1)) ∧
    (∀ d d', (∃ k, iterate G.node k d = d') ↔
      halfEdgeEnd edges d.val = halfEdgeEnd edges d'.val) ∧
    G.Planar

end Complexity
