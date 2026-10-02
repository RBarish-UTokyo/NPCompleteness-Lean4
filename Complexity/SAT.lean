module

public import Init

/-!
Boolean satisfiability with a concrete, prefix-free binary representation.

List lengths and variable indices use unary numerals.  This module establishes
semantic and serialization facts only; it asserts no machine running-time bound.
3-CNF means that each clause has at most three literals, including empty clauses.
-/

@[expose] public section

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

/-- One more than the greatest occurring variable; zero for the empty clause. -/
def clauseBound : Clause → Nat
  | [] => 0
  | l :: c => max (l.var + 1) (clauseBound c)

/-- Every variable occurring in the formula is strictly below this bound. -/
def variableBound : CNF → Nat
  | [] => 0
  | c :: f => max (clauseBound c) (variableBound f)

theorem literal_lt_clauseBound {c : Clause} {l : Literal} (h : l ∈ c) :
    l.var < clauseBound c := by
  revert h
  induction c with
  | nil => simp
  | cons a c ih =>
      intro h
      rcases List.mem_cons.mp h with h | h
      · subst l
        exact Nat.lt_of_lt_of_le (Nat.lt_succ_self a.var) (Nat.le_max_left ..)
      · exact Nat.lt_of_lt_of_le (ih h) (Nat.le_max_right ..)

theorem clauseBound_le_variableBound {f : CNF} {c : Clause} (h : c ∈ f) :
    clauseBound c ≤ variableBound f := by
  revert h
  induction f with
  | nil => simp
  | cons a f ih =>
      intro h
      rcases List.mem_cons.mp h with h | h
      · subst c
        exact Nat.le_max_left ..
      · exact Nat.le_trans (ih h) (Nat.le_max_right ..)

theorem literal_lt_variableBound {f : CNF} {c : Clause} {l : Literal}
    (hc : c ∈ f) (hl : l ∈ c) : l.var < variableBound f :=
  Nat.lt_of_lt_of_le (literal_lt_clauseBound hl) (clauseBound_le_variableBound hc)

@[simp] theorem evalLiteral_positive (a : Assignment) (v : Nat) :
    evalLiteral a ⟨v, true⟩ = a v := rfl

@[simp] theorem evalLiteral_negative (a : Assignment) (v : Nat) :
    evalLiteral a ⟨v, false⟩ = !(a v) := rfl

@[simp] theorem evalClause_nil (a : Assignment) : evalClause a [] = false := rfl

@[simp] theorem evalClause_cons (a : Assignment) (l : Literal) (c : Clause) :
    evalClause a (l :: c) = (evalLiteral a l || evalClause a c) := rfl

@[simp] theorem evalCNF_nil (a : Assignment) : evalCNF a [] = true := rfl

@[simp] theorem evalCNF_cons (a : Assignment) (c : Clause) (f : CNF) :
    evalCNF a (c :: f) = (evalClause a c && evalCNF a f) := rfl

theorem evalClause_append (a : Assignment) (c d : Clause) :
    evalClause a (c ++ d) = (evalClause a c || evalClause a d) := by
  simp [evalClause, List.any_append]

theorem evalCNF_append (a : Assignment) (f g : CNF) :
    evalCNF a (f ++ g) = (evalCNF a f && evalCNF a g) := by
  simp [evalCNF, List.all_append]

@[simp] theorem satisfiable_empty : Satisfiable [] :=
  ⟨fun _ => false, rfl⟩

theorem not_satisfiable_empty_clause (f : CNF) : ¬ Satisfiable ([] :: f) := by
  intro ⟨a, h⟩
  simp at h

abbrev Parser (α : Type) := Word → Option (α × Word)

/-- A unary numeral consists of `n` true bits followed by one false bit. -/
def writeNat : Nat → Word
  | 0 => [false]
  | n + 1 => true :: writeNat n

def readNat : Parser Nat
  | [] => none
  | false :: rest => some (0, rest)
  | true :: rest => do
      let (n, tail) ← readNat rest
      pure (n + 1, tail)

@[simp] theorem readNat_writeNat (n : Nat) (rest : Word) :
    readNat (writeNat n ++ rest) = some (n, rest) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [writeNat, readNat, ih]

def writeValues {α : Type} (enc : α → Word) : List α → Word
  | [] => []
  | x :: xs => enc x ++ writeValues enc xs

def readMany {α : Type} (parse : Parser α) : Nat → Parser (List α)
  | 0, rest => some ([], rest)
  | n + 1, input => do
      let (x, rest) ← parse input
      let (xs, tail) ← readMany parse n rest
      pure (x :: xs, tail)

theorem readMany_writeValues {α : Type} (parse : Parser α) (enc : α → Word)
    (h : ∀ x rest, parse (enc x ++ rest) = some (x, rest))
    (xs : List α) (rest : Word) :
    readMany parse xs.length (writeValues enc xs ++ rest) = some (xs, rest) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp [writeValues, readMany, List.append_assoc, h, ih]

def writeList {α : Type} (enc : α → Word) (xs : List α) : Word :=
  writeNat xs.length ++ writeValues enc xs

def readList {α : Type} (parse : Parser α) : Parser (List α) := fun input => do
  let (n, rest) ← readNat input
  readMany parse n rest

theorem readList_writeList {α : Type} (parse : Parser α) (enc : α → Word)
    (h : ∀ x rest, parse (enc x ++ rest) = some (x, rest))
    (xs : List α) (rest : Word) :
    readList parse (writeList enc xs ++ rest) = some (xs, rest) := by
  simp [readList, writeList, List.append_assoc, readMany_writeValues parse enc h]

def encodeLiteral (l : Literal) : Word :=
  l.positive :: writeNat l.var

def readLiteral : Parser Literal
  | [] => none
  | sign :: rest => do
      let (v, tail) ← readNat rest
      pure (⟨v, sign⟩, tail)

@[simp] theorem readLiteral_encodeLiteral (l : Literal) (rest : Word) :
    readLiteral (encodeLiteral l ++ rest) = some (l, rest) := by
  cases l
  simp [encodeLiteral, readLiteral]

def encodeClause : Clause → Word := writeList encodeLiteral
def readClause : Parser Clause := readList readLiteral

@[simp] theorem readClause_encodeClause (c : Clause) (rest : Word) :
    readClause (encodeClause c ++ rest) = some (c, rest) :=
  readList_writeList readLiteral encodeLiteral readLiteral_encodeLiteral c rest

def encode : CNF → Word := writeList encodeClause
def readCNF : Parser CNF := readList readClause

@[simp] theorem readCNF_encode (f : CNF) (rest : Word) :
    readCNF (encode f ++ rest) = some (f, rest) :=
  readList_writeList readClause encodeClause readClause_encodeClause f rest

/-- Parse an entire word, rejecting trailing bits as well as malformed prefixes. -/
def decode (input : Word) : Option CNF :=
  match readCNF input with
  | some (f, []) => some f
  | _ => none

@[simp] theorem decode_encode (f : CNF) : decode (encode f) = some f := by
  have h := readCNF_encode f []
  simp only [List.append_nil] at h
  simp [decode, h]

theorem encode_injective (f g : CNF) (h : encode f = encode g) : f = g := by
  have h' := congrArg decode h
  simpa using h'

theorem encode_prefix_free {f g : CNF} {rest : Word}
    (h : encode f ++ rest = encode g) : f = g ∧ rest = [] := by
  have hf := readCNF_encode f rest
  have hg := readCNF_encode g []
  simp only [List.append_nil] at hg
  rw [h, hg] at hf
  have hp : (g, ([] : Word)) = (f, rest) := Option.some.inj hf
  exact ⟨(congrArg Prod.fst hp).symm, (congrArg Prod.snd hp).symm⟩

/-- SAT as a language of binary words; failed decodings are not members. -/
def SAT (input : Word) : Prop :=
  ∃ f, decode input = some f ∧ Satisfiable f

/-- 3-SAT uses the same encoding and clauses of at most three literals. -/
def ThreeSAT (input : Word) : Prop :=
  ∃ f, decode input = some f ∧ IsThreeCNF f ∧ Satisfiable f

@[simp] theorem SAT_encode_iff (f : CNF) : SAT (encode f) ↔ Satisfiable f := by
  simp [SAT]

@[simp] theorem ThreeSAT_encode_iff (f : CNF) :
    ThreeSAT (encode f) ↔ IsThreeCNF f ∧ Satisfiable f := by
  simp [ThreeSAT]

theorem not_SAT_of_decode_none {input : Word} (h : decode input = none) :
    ¬ SAT input := by
  simp [SAT, h]

theorem not_ThreeSAT_of_decode_none {input : Word} (h : decode input = none) :
    ¬ ThreeSAT input := by
  simp [ThreeSAT, h]

theorem ThreeSAT_implies_SAT {input : Word} (h : ThreeSAT input) : SAT input := by
  obtain ⟨f, hf, _, hs⟩ := h
  exact ⟨f, hf, hs⟩

end Complexity.SAT
