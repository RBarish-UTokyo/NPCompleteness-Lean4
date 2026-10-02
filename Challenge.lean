module

public import Init

/-!
# SAT and 3-SAT are NP-complete

This file states the Cook–Levin theorem and its 3-SAT form, for a concrete
machine model and a concrete binary encoding of CNF formulas:

* `Complexity.sat_np_complete`: SAT, the set of codes of satisfiable CNF
  formulas, is NP-complete.
* `Complexity.threeSAT_np_complete`: 3-SAT, the set of codes of satisfiable
  CNF formulas with at most three literals per clause, is NP-complete.

NP-complete means: in NP, and every language in NP reduces to it by a
polynomial-time many-one (Karp) reduction.

## Reading guide

* Machines (`Machine`, `run`): deterministic Turing machines with one two-way
  infinite tape over the alphabet {blank, 0, 1, separator} and finitely many
  control states. Each step either halts with a Boolean decision, or writes the
  scanned cell, moves the head at most one cell, and changes state. Time is the
  number of steps, the halting step included.
* Complexity (`PolynomialTimeMachine`, `PolyTime`, `InNP`, `PolyRed`, `NPHard`,
  `NPComplete`): languages are sets of binary words, and polynomial bounds
  are `c * (n + 1) ^ k`. A polynomial-time function leaves its output on the
  tape, from the head onward. NP is defined by polynomial-time verifiers and
  polynomially bounded certificates, given to the verifier as `pairWords x w`.
* Formulas (`Complexity.SAT`): variables are natural numbers, a clause is a list
  of literals, a CNF formula is a list of clauses. `encode` writes variable
  indices and list lengths in unary and a literal's sign as one bit. A word that
  is not the code of a formula belongs to neither language. 3-SAT allows clauses
  with fewer than three literals, repeated literals, and empty clauses.

Only Lean core is imported. `Solution.lean` proves both theorems without importing
this file, which `scripts/generate_challenge.py` generates from the library sources.
-/

@[expose] public section

namespace Complexity

/-- Tape symbols: the blank, the two bits, and a separator `sep` (a work symbol). -/
inductive Symbol where
  | blank
  | bit (value : Bool)
  | sep
  deriving DecidableEq, Repr

/-- A head movement: one cell left, none, or one cell right. -/
inductive Move where
  | left
  | stay
  | right
  deriving DecidableEq, Repr

/-- A two-way infinite tape with a head. `right` is the scanned cell followed by
the cells to its right; `left` holds the cells to the left of the head, nearest
first. All cells beyond both lists are blank. -/
structure Tape where
  left : List Symbol
  right : List Symbol
  deriving DecidableEq, Repr

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

/-- An instruction: halt with a decision (`true` accepts, `false` rejects), or
write a symbol, move the head, and enter control state `next`. -/
inductive Instruction (states : Nat) where
  | halt (decision : Bool)
  | step (write : Symbol) (move : Move) (next : Fin states)
  deriving DecidableEq, Repr

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

/-- One step from `c`: an instruction `halt b` stops with decision `b` and the
current tape (`.inl`); otherwise write, move, and change state (`.inr`). -/
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

/-- The pair `(x, y)` as one word: `|x|` ones, a zero, then `x` and `y`. A
verifier for NP receives an instance `x` and a certificate `y` this way. -/
def pairWords (x y : Word) : Word :=
  List.replicate x.length true ++ false :: (x ++ y)

/-- `M` accepts `input`: its run on `input` halts with decision `true`. -/
def Accepts (M : Machine) (input : Word) : Prop :=
  ∃ time tape, runInput M time input = some (true, tape)

/-- `M` runs in polynomial time: for some `c` and `k`, on every input of length
`n` it halts, accepting or rejecting, within `c * (n + 1) ^ k` steps. -/
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

/-- Polynomial-time many-one (Karp) reducibility of `A` to `B`: a polynomial-time
computable `f` with `x ∈ A ↔ f x ∈ B` for every word `x`. -/
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
deriving DecidableEq, Repr

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

/-- The code of a literal: its sign bit (`true` if positive), then its variable
index in unary. -/
def encodeLiteral (l : Literal) : Word :=
  l.positive :: writeNat l.var

/-- The code of a clause: the list of its literals. -/
def encodeClause : Clause → Word := writeList encodeLiteral

/-- The code of a CNF formula: the list of its clauses. -/
def encode : CNF → Word := writeList encodeClause

/-- SAT: the words `encode f` with `f` a satisfiable CNF formula. A word that is
not the code of a formula is not in SAT. -/
def SAT (input : Word) : Prop :=
  ∃ f, encode f = input ∧ Satisfiable f

/-- 3-SAT: the words `encode f` with `f` a satisfiable CNF formula all of whose
clauses have at most three literals. -/
def ThreeSAT (input : Word) : Prop :=
  ∃ f, encode f = input ∧ IsThreeCNF f ∧ Satisfiable f

end Complexity.SAT

namespace Complexity

/-- **Cook–Levin theorem.** SAT is NP-complete: it is in NP, and every language
in NP reduces to it by a polynomial-time many-one reduction. -/
theorem sat_np_complete : NPComplete SAT.SAT := by
  sorry

/-- **3-SAT is NP-complete**: in NP, and every language in NP reduces to it by a
polynomial-time many-one reduction. -/
theorem threeSAT_np_complete : NPComplete SAT.ThreeSAT := by
  sorry

end Complexity
