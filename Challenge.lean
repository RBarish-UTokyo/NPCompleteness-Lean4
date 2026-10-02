module

public import Init

/-!
Independent target statement for SAT and 3-SAT NP-completeness.

NP uses polynomial-length binary certificates checked by a deterministic finite
single-tape machine. Reductions are total polynomial-time machine computations.
SAT is encoded CNF satisfiability; 3-SAT means clauses of at most three literals.
The unary prefix encoding and malformed-input rejection are specified below.

The two intentional theorem holes are the submission targets. This independent
statement imports no project modules and is never imported by the proof library.
Solution.lean imports the completed proofs in a separate Lean environment.
Regenerate with `python3 scripts/generate_challenge.py` after definition edits;
`--check` checks source drift. Official comparison remains a separate check.
-/

@[expose] public section

namespace Complexity

inductive Symbol where
  | blank
  | bit (value : Bool)
  | sep
  deriving DecidableEq, Repr

inductive Move where
  | left
  | stay
  | right
  deriving DecidableEq, Repr

structure Tape where
  left : List Symbol
  right : List Symbol
  deriving DecidableEq, Repr

namespace Tape

def read (t : Tape) : Symbol := t.right.headD .blank

def write (a : Symbol) (t : Tape) : Tape :=
  { t with right := a :: t.right.drop 1 }

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

def ofInput (input : List Bool) : Tape := ⟨[], input.map Symbol.bit⟩

def bits : List Symbol → List Bool
  | .bit b :: rest => b :: bits rest
  | _ => []

def output (t : Tape) : List Bool := bits t.right

def size (t : Tape) : Nat := t.left.length + t.right.length

end Tape

inductive Instruction (states : Nat) where
  | halt (decision : Bool)
  | step (write : Symbol) (move : Move) (next : Fin states)
  deriving DecidableEq, Repr

def Instruction.mapState {n m : Nat} (rename : Fin n → Fin m) :
    Instruction n → Instruction m
  | .halt b => .halt b
  | .step a d q => .step a d (rename q)

structure Machine where
  states : Nat
  start : Fin (states + 1)
  code : Fin (states + 1) → Symbol → Instruction (states + 1)

structure Config (M : Machine) where
  state : Fin (M.states + 1)
  tape : Tape

def initial (M : Machine) (input : List Bool) : Config M :=
  ⟨M.start, Tape.ofInput input⟩

def step (M : Machine) (c : Config M) : (Bool × Tape) ⊕ Config M :=
  match M.code c.state c.tape.read with
  | .halt b => .inl (b, c.tape)
  | .step a d q => .inr ⟨q, (c.tape.write a).move d⟩

def run (M : Machine) : Nat → Config M → Option (Bool × Tape)
  | 0, _ => none
  | fuel + 1, c =>
    match M.code c.state c.tape.read with
    | .halt b => some (b, c.tape)
    | .step a d q => run M fuel ⟨q, (c.tape.write a).move d⟩

def runInput (M : Machine) (fuel : Nat) (input : List Bool) :
    Option (Bool × Tape) := run M fuel (initial M input)

abbrev Word := List Bool

abbrev Language := Word → Prop

def powerBound (coefficient exponent inputSize : Nat) : Nat :=
  coefficient * (inputSize + 1) ^ exponent

def pairWords (x y : Word) : Word :=
  List.replicate x.length true ++ false :: (x ++ y)

def Accepts (M : Machine) (input : Word) : Prop :=
  ∃ time tape, runInput M time input = some (true, tape)

def PolynomialTimeMachine (M : Machine) : Prop :=
  ∃ coefficient exponent, ∀ input : Word,
    ∃ time decision tape,
      time ≤ powerBound coefficient exponent input.length ∧
      runInput M time input = some (decision, tape)

def PolyTime (f : Word → Word) : Prop :=
  ∃ M : Machine, ∃ coefficient exponent, ∀ input : Word,
    ∃ time tape,
      time ≤ powerBound coefficient exponent input.length ∧
      runInput M time input = some (true, tape) ∧
      tape.output = f input

def InP (L : Language) : Prop :=
  ∃ M : Machine, PolynomialTimeMachine M ∧
    ∀ input, L input ↔ Accepts M input

def InNP (L : Language) : Prop :=
  ∃ M : Machine, ∃ coefficient exponent,
    PolynomialTimeMachine M ∧
    ∀ input, L input ↔
      ∃ witness : Word,
        witness.length ≤ powerBound coefficient exponent input.length ∧
        Accepts M (pairWords input witness)

def PolyRed (A B : Language) : Prop :=
  ∃ f : Word → Word, PolyTime f ∧ ∀ input, A input ↔ B (f input)

def NPHard (L : Language) : Prop :=
  ∀ A : Language, InNP A → PolyRed A L

def NPComplete (L : Language) : Prop :=
  InNP L ∧ NPHard L

end Complexity

namespace Complexity.SAT

abbrev Word := List Bool

abbrev Assignment := Nat → Bool

structure Literal where
  var : Nat
  positive : Bool
deriving DecidableEq, Repr

abbrev Clause := List Literal

abbrev CNF := List Clause

def evalLiteral (a : Assignment) (l : Literal) : Bool :=
  if l.positive then a l.var else !(a l.var)

def evalClause (a : Assignment) (c : Clause) : Bool :=
  c.any (evalLiteral a)

def evalCNF (a : Assignment) (f : CNF) : Bool :=
  f.all (evalClause a)

def Satisfiable (f : CNF) : Prop :=
  ∃ a, evalCNF a f = true

def IsThreeCNF (f : CNF) : Prop :=
  ∀ c ∈ f, c.length ≤ 3

abbrev Parser (α : Type) := Word → Option (α × Word)

def writeNat : Nat → Word
  | 0 => [false]
  | n + 1 => true :: writeNat n

def readNat : Parser Nat
  | [] => none
  | false :: rest => some (0, rest)
  | true :: rest => do
      let (n, tail) ← readNat rest
      pure (n + 1, tail)

def writeValues {α : Type} (enc : α → Word) : List α → Word
  | [] => []
  | x :: xs => enc x ++ writeValues enc xs

def readMany {α : Type} (parse : Parser α) : Nat → Parser (List α)
  | 0, rest => some ([], rest)
  | n + 1, input => do
      let (x, rest) ← parse input
      let (xs, tail) ← readMany parse n rest
      pure (x :: xs, tail)

def writeList {α : Type} (enc : α → Word) (xs : List α) : Word :=
  writeNat xs.length ++ writeValues enc xs

def readList {α : Type} (parse : Parser α) : Parser (List α) := fun input => do
  let (n, rest) ← readNat input
  readMany parse n rest

def encodeLiteral (l : Literal) : Word :=
  l.positive :: writeNat l.var

def readLiteral : Parser Literal
  | [] => none
  | sign :: rest => do
      let (v, tail) ← readNat rest
      pure (⟨v, sign⟩, tail)

def encodeClause : Clause → Word := writeList encodeLiteral

def readClause : Parser Clause := readList readLiteral

def encode : CNF → Word := writeList encodeClause

def readCNF : Parser CNF := readList readClause

def decode (input : Word) : Option CNF :=
  match readCNF input with
  | some (f, []) => some f
  | _ => none

def SAT (input : Word) : Prop :=
  ∃ f, decode input = some f ∧ Satisfiable f

def ThreeSAT (input : Word) : Prop :=
  ∃ f, decode input = some f ∧ IsThreeCNF f ∧ Satisfiable f

end Complexity.SAT

namespace Complexity

/-- Cook–Levin: encoded CNF satisfiability is NP-complete. -/
theorem sat_np_complete : NPComplete SAT.SAT := by
  sorry

/-- Encoded 3-CNF satisfiability is NP-complete. -/
theorem threeSAT_np_complete : NPComplete SAT.ThreeSAT := by
  sorry

end Complexity
