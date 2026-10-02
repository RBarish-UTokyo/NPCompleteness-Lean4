module

public import Init

/-!
# NP-completeness of SAT and of variants of SAT

For one machine model and concrete binary codes of CNF formulas, the theorems at the end
state that SAT, 3-SAT (at most three literals per clause), exactly-3-SAT (exactly three, on
distinct variables), (≤1,≤2)-SAT, SAT with binary variable indices, planar 3-SAT and
Lichtenstein's planar 3-SAT are NP-complete: in NP, and every language in NP reduces to them
by a polynomial-time many-one reduction. A last theorem states that NP, defined by verifiers,
is nondeterministic polynomial time.

* Machines: deterministic single-tape Turing machines over {blank, 0, 1, separator}; time is
  the number of steps, the halting step included. `NMachine` has two transition tables.
* Polynomial bounds are `c * (n + 1) ^ k`. A computed function leaves its output from the
  head onward; an NP verifier gets instance and certificate as `pairWords x w`.
* Formulas: variables are natural numbers, a clause is a list of literals, a formula a list
  of clauses. `encode` writes indices and lengths in unary, `encodeBinary` indices in binary.
  Words coding no formula belong to none of the languages.
* Planarity follows Gonthier's Four Color proof: a hypermap is planar when its genus, from the
  Euler formula, is zero; a graph is planar when some planar hypermap on its half-edges
  embeds it. Planar 3-SAT asks this of the variable–clause incidence graph.

Only Lean core is imported. `scripts/generate_challenge.py` generates this file from the
library; `Solution.lean` proves the theorems without importing it.
-/

@[expose] public section

namespace Complexity

/-- Tape symbols: the blank, the two bits, and a separator `sep` (a work symbol). -/
inductive Symbol where
  | blank | bit (value : Bool) | sep

/-- A head movement: one cell left, none, or one cell right. -/
inductive Move where
  | left | stay | right

/-- A two-way infinite tape: `right` is the scanned cell and the cells to its right,
`left` the cells to its left, nearest first; all other cells are blank. -/
structure Tape where
  left : List Symbol
  right : List Symbol

namespace Tape

/-- The scanned symbol (blank beyond the stored cells). -/
def read (t : Tape) : Symbol := t.right.headD .blank

/-- Overwrite the scanned cell with `a`. -/
def write (a : Symbol) (t : Tape) : Tape :=
  { t with right := a :: t.right.drop 1 }

/-- Move the head by `d`, storing a blank cell when it moves past the stored cells. -/
def move (d : Move) (t : Tape) : Tape :=
  match d with
  | .stay => t
  | .left =>
    match t.left with
    | [] => ⟨[], .blank :: t.right⟩
    | a :: rest => ⟨rest, a :: t.right⟩
  | .right =>
    match t.right with
    | [] => ⟨.blank :: t.left, []⟩
    | a :: rest => ⟨a :: t.left, rest⟩

/-- The tape holding `input` as bits, head on its first cell, blank elsewhere. -/
def ofInput (input : List Bool) : Tape := ⟨[], input.map Symbol.bit⟩

/-- The longest prefix of a symbol list made of bits, as a binary word. -/
def bits : List Symbol → List Bool
  | .bit b :: rest => b :: bits rest
  | _ => []

/-- The output: the bits from the head rightwards, up to the first non-bit cell. -/
def output (t : Tape) : List Bool := bits t.right

end Tape

/-- An instruction: `halt b` (`true` accepts), or write, move, and enter state `next`. -/
inductive Instruction (states : Nat) where
  | halt (decision : Bool)
  | step (write : Symbol) (move : Move) (next : Fin states)

/-- A deterministic single-tape Turing machine: control states `Fin (states + 1)`,
a start state, and an instruction for every control state and scanned symbol. -/
structure Machine where
  states : Nat
  start : Fin (states + 1)
  code : Fin (states + 1) → Symbol → Instruction (states + 1)

/-- A configuration of `M`: control state and tape (with head). -/
structure Config (M : Machine) where
  state : Fin (M.states + 1)
  tape : Tape

/-- The initial configuration on `input`: start state, input tape (`Tape.ofInput`). -/
def initial (M : Machine) (input : List Bool) : Config M :=
  ⟨M.start, Tape.ofInput input⟩

/-- One step from `c`: `.inl (b, tape)` on `halt b`, else the next configuration. -/
def step (M : Machine) (c : Config M) : (Bool × Tape) ⊕ Config M :=
  match M.code c.state c.tape.read with
  | .halt b => .inl (b, c.tape)
  | .step a d q => .inr ⟨q, (c.tape.write a).move d⟩

/-- `run M fuel c` executes at most `fuel` steps from `c`. It is `some (b, t)` if
the machine executes `halt b` within these steps (halting counts as a step),
`t` being the final tape, and `none` if it has not halted after `fuel` steps. -/
def run (M : Machine) : Nat → Config M → Option (Bool × Tape)
  | 0, _ => none
  | fuel + 1, c =>
    match M.code c.state c.tape.read with
    | .halt b => some (b, c.tape)
    | .step a d q => run M fuel ⟨q, (c.tape.write a).move d⟩

/-- `run` from the initial configuration on `input`. -/
def runInput (M : Machine) (fuel : Nat) (input : List Bool) :
    Option (Bool × Tape) := run M fuel (initial M input)

/-- Binary words. -/
abbrev Word := List Bool
/-- A language (decision problem): a set of binary words. -/
abbrev Language := Word → Prop

/-- The bound `c * (n + 1) ^ k`. Every polynomial in `n` with natural coefficients
is at most such a bound, so these bounds express polynomial time and length.
`Nat.pow` is written out so that this term is the same when Mathlib is imported. -/
def powerBound (coefficient exponent inputSize : Nat) : Nat :=
  coefficient * Nat.pow (inputSize + 1) exponent

/-- The pair `(x, y)` as one word, `|x|` ones, a zero, `x`, `y`: how NP verifiers get input. -/
def pairWords (x y : Word) : Word :=
  List.replicate x.length true ++ false :: (x ++ y)

/-- `M` accepts `input`: its run on `input` halts with decision `true`. -/
def Accepts (M : Machine) (input : Word) : Prop :=
  ∃ time tape, runInput M time input = some (true, tape)

/-- `M` halts, accepting or rejecting, within `c * (n + 1) ^ k` steps on every input. -/
def PolynomialTimeMachine (M : Machine) : Prop :=
  ∃ coefficient exponent, ∀ input : Word,
    ∃ time decision tape,
      time ≤ powerBound coefficient exponent input.length ∧
      runInput M time input = some (decision, tape)

/-- `f` is computable in polynomial time: one machine, on every input `x` of
length `n`, halts with decision `true` within `c * (n + 1) ^ k` steps, with
`f x` as the output (`Tape.output`) of its final tape. -/
def PolyTime (f : Word → Word) : Prop :=
  ∃ M : Machine, ∃ coefficient exponent, ∀ input : Word,
    ∃ time tape,
      time ≤ powerBound coefficient exponent input.length ∧
      runInput M time input = some (true, tape) ∧
      tape.output = f input

/-- NP, in its certificate (verifier) form: some polynomial-time machine `M` and
bound `p n = c * (n + 1) ^ k` satisfy, for every word `x`: `x ∈ L` iff `M`
accepts `pairWords x w` for some certificate `w` with `|w| ≤ p |x|`. -/
def InNP (L : Language) : Prop :=
  ∃ M : Machine, ∃ coefficient exponent,
    PolynomialTimeMachine M ∧
    ∀ input, L input ↔
      ∃ witness : Word,
        witness.length ≤ powerBound coefficient exponent input.length ∧
        Accepts M (pairWords input witness)

/-- Karp reducibility: a polynomial-time `f` with `x ∈ A ↔ f x ∈ B` for every word `x`. -/
def PolyRed (A B : Language) : Prop :=
  ∃ f : Word → Word, PolyTime f ∧ ∀ input, A input ↔ B (f input)

/-- `L` is NP-hard: every language in NP reduces to `L`. -/
def NPHard (L : Language) : Prop :=
  ∀ A : Language, InNP A → PolyRed A L

/-- `L` is NP-complete: `L` is in NP and is NP-hard. -/
def NPComplete (L : Language) : Prop :=
  InNP L ∧ NPHard L

end Complexity

namespace Complexity.SAT

/-- Binary words (the same type as `Complexity.Word`). -/
abbrev Word := List Bool
/-- A truth assignment to the variables `x 0, x 1, x 2, …`. -/
abbrev Assignment := Nat → Bool

/-- The literal `x var` if `positive`, and its negation `¬ x var` otherwise. -/
structure Literal where
  var : Nat
  positive : Bool

/-- A clause: the disjunction of its literals. -/
abbrev Clause := List Literal
/-- A CNF formula: the conjunction of its clauses. -/
abbrev CNF := List Clause

/-- The truth value of a literal under `a`. -/
def evalLiteral (a : Assignment) (l : Literal) : Bool :=
  if l.positive then a l.var else !(a l.var)

/-- The truth value of a clause (the empty clause is false). -/
def evalClause (a : Assignment) (c : Clause) : Bool :=
  c.any (evalLiteral a)

/-- The truth value of a formula (the empty formula is true). -/
def evalCNF (a : Assignment) (f : CNF) : Bool :=
  f.all (evalClause a)

/-- Some assignment makes `f` true. -/
def Satisfiable (f : CNF) : Prop :=
  ∃ a, evalCNF a f = true

/-- Every clause of `f` has at most three literals. -/
def IsThreeCNF (f : CNF) : Prop :=
  ∀ c ∈ f, c.length ≤ 3

/-- The unary code of `n`: `n` ones followed by a zero. -/
def writeNat : Nat → Word
  | 0 => [false]
  | n + 1 => true :: writeNat n

/-- Concatenate the codes of the elements of a list. -/
def writeValues {α : Type} (enc : α → Word) : List α → Word
  | [] => []
  | x :: xs => enc x ++ writeValues enc xs

/-- The code of a list: its length in unary, then the codes of its elements. -/
def writeList {α : Type} (enc : α → Word) (xs : List α) : Word :=
  writeNat xs.length ++ writeValues enc xs

/-- The code of a literal: its sign bit (`true` if positive), then its index in unary. -/
def encodeLiteral (l : Literal) : Word :=
  l.positive :: writeNat l.var

/-- The code of a clause: the list of its literals. -/
def encodeClause : Clause → Word := writeList encodeLiteral
/-- The code of a CNF formula: the list of its clauses. -/
def encode : CNF → Word := writeList encodeClause

/-- SAT: the words `encode f` with `f` satisfiable (no other word is in SAT). -/
def SAT (input : Word) : Prop :=
  ∃ f, encode f = input ∧ Satisfiable f

/-- 3-SAT: the words `encode f` with `f` satisfiable and `IsThreeCNF f`. -/
def ThreeSAT (input : Word) : Prop :=
  ∃ f, encode f = input ∧ IsThreeCNF f ∧ Satisfiable f

/-- Every clause of `f` has exactly three literals, on three distinct variables. -/
def IsExactThreeCNF (f : CNF) : Prop :=
  ∀ c ∈ f, c.length = 3 ∧ (c.map Literal.var).Nodup

/-- Exactly-3-SAT: the words `encode f` with `f` satisfiable and `IsExactThreeCNF f`. -/
def ExactThreeSAT (input : Word) : Prop :=
  ∃ f, encode f = input ∧ IsExactThreeCNF f ∧ Satisfiable f

/-- The (≤1,≤2) restriction: every clause of `f` has two or three literals, and every variable
occurs in `f` at most once positively and at most twice negatively. -/
def IsLeOneLeTwoCNF (f : CNF) : Prop :=
  (∀ c ∈ f, 2 ≤ c.length ∧ c.length ≤ 3) ∧
  ∀ v : Nat, (f.flatten.filter fun l => l.positive && Nat.beq l.var v).length ≤ 1 ∧
    (f.flatten.filter fun l => !l.positive && Nat.beq l.var v).length ≤ 2

/-- (≤1,≤2)-SAT: the words `encode f` with `f` satisfiable and satisfying `IsLeOneLeTwoCNF`. -/
def LeOneLeTwoSAT (input : Word) : Prop :=
  ∃ f, encode f = input ∧ IsLeOneLeTwoCNF f ∧ Satisfiable f

/-- The number with binary digits `bits`, least significant digit first. -/
def binaryValue : List Bool → Nat
  | [] => 0
  | b :: bits => b.toNat + 2 * binaryValue bits

/-- A literal naming its variable by binary digits, least significant first (zeros may trail). -/
structure BinaryLiteral where
  bits : List Bool
  positive : Bool

/-- The literal named by a `BinaryLiteral`. -/
def BinaryLiteral.toLiteral (l : BinaryLiteral) : Literal :=
  ⟨binaryValue l.bits, l.positive⟩

/-- The code of a binary literal: its sign bit, then its digits (their count in unary first). -/
def encodeBinaryLiteral (l : BinaryLiteral) : Word :=
  l.positive :: writeList (fun b => [b]) l.bits

/-- The code of a formula with binary indices; clause and literal counts stay in unary. -/
def encodeBinary (f : List (List BinaryLiteral)) : Word :=
  writeList (writeList encodeBinaryLiteral) f

/-- Binary SAT: the words `encodeBinary f` such that the formula `f` names is satisfiable. -/
def BinarySAT (input : Word) : Prop :=
  ∃ f, encodeBinary f = input ∧ Satisfiable (f.map (List.map BinaryLiteral.toLiteral))

end Complexity.SAT

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

namespace Complexity

/-- A nondeterministic machine: like `Machine`, with two tables; each step may follow either. -/
structure NMachine where
  states : Nat
  start : Fin (states + 1)
  code : Bool → Fin (states + 1) → Symbol → Instruction (states + 1)

/-- `M.run choices q t` runs `M` from state `q` and tape `t`, using the table `code c` for the
step consuming choice `c`: `some (b, t')` if it executes `halt b` (halting counts as a step)
before the choices run out, with final tape `t'`, and `none` otherwise. -/
def NMachine.run (M : NMachine) :
    List Bool → Fin (M.states + 1) → Tape → Option (Bool × Tape)
  | [], _, _ => none
  | c :: choices, q, t =>
    match M.code c q t.read with
    | .halt b => some (b, t)
    | .step a d q' => M.run choices q' ((t.write a).move d)

/-- Nondeterministic polynomial time: some nondeterministic machine `M` and bound
`p n = c * (n + 1) ^ k` such that, on every input `x`, every computation path halts within
`p |x|` steps, and `x ∈ L` iff some computation path accepts. -/
def NondeterministicPolyTime (L : Language) : Prop :=
  ∃ M : NMachine, ∃ coefficient exponent, ∀ input : Word,
    (∀ choices : List Bool, choices.length = powerBound coefficient exponent input.length →
      M.run choices M.start (Tape.ofInput input) ≠ none) ∧
    (L input ↔ ∃ choices tape, M.run choices M.start (Tape.ofInput input) = some (true, tape))

/-- **Cook–Levin theorem.** SAT is NP-complete. -/
theorem sat_np_complete : NPComplete SAT.SAT := by sorry

/-- 3-SAT is NP-complete. -/
theorem threeSAT_np_complete : NPComplete SAT.ThreeSAT := by sorry

/-- Exactly-3-SAT is NP-complete. -/
theorem exactThreeSAT_np_complete : NPComplete SAT.ExactThreeSAT := by sorry

/-- (≤1,≤2)-SAT is NP-complete. -/
theorem leOneLeTwoSAT_np_complete : NPComplete SAT.LeOneLeTwoSAT := by sorry

/-- SAT with binary variable indices is NP-complete. -/
theorem binarySAT_np_complete : NPComplete SAT.BinarySAT := by sorry

/-- Planar 3-SAT is NP-complete. -/
theorem planarThreeSAT_np_complete : NPComplete SAT.PlanarThreeSAT := by sorry

/-- Lichtenstein's planar 3-SAT, with the cycle through the variables, is NP-complete. -/
theorem cyclePlanarThreeSAT_np_complete : NPComplete SAT.CyclePlanarThreeSAT := by sorry

/-- NP, defined by verifiers, is nondeterministic polynomial time. -/
theorem inNP_iff_nondeterministicPolyTime (L : Language) :
    InNP L ↔ NondeterministicPolyTime L := by sorry

end Complexity
