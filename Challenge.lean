module

public import Init

/-!
# NP-completeness of SAT and of variants of SAT

For one machine model and concrete binary codes of CNF formulas, the theorems at the end
state that SAT, 3-SAT (at most three literals per clause), exactly-3-SAT (exactly three, on
distinct variables), (≤1,≤2)-SAT and SAT with binary variable indices are NP-complete: in NP,
and every language in NP reduces to them by a polynomial-time many-one reduction. A last
theorem states that NP, defined by verifiers, is nondeterministic polynomial time.

* Machines: deterministic single-tape Turing machines over {blank, 0, 1, separator}; time is
  the number of steps, the halting step included. `NMachine` has two transition tables.
* Polynomial bounds are `c * (n + 1) ^ k`. A computed function leaves its output from the
  head onward; an NP verifier gets instance and certificate as `pairWords x w`.
* Formulas: variables are natural numbers, a clause is a list of literals, a formula a list
  of clauses. `encode` writes indices and lengths in unary, `encodeBinary` indices in binary.
  Words coding no formula belong to none of the languages.

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

/-- NP, defined by verifiers, is nondeterministic polynomial time. -/
theorem inNP_iff_nondeterministicPolyTime (L : Language) :
    InNP L ↔ NondeterministicPolyTime L := by sorry

end Complexity
