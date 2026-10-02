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

/-- A parser reads a value from the front of a word and returns it together with
the rest of the word, or fails. -/
abbrev Parser (α : Type) := Word → Option (α × Word)

/-- The unary code of `n`: `n` ones followed by a zero. -/
def writeNat : Nat → Word
  | 0 => [false]
  | n + 1 => true :: writeNat n

/-- Parse a unary code, as written by `writeNat`. -/
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

/-- Concatenate the codes of the elements of a list. -/
def writeValues {α : Type} (enc : α → Word) : List α → Word
  | [] => []
  | x :: xs => enc x ++ writeValues enc xs

/-- Parse exactly `n` values one after the other. -/
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

/-- The code of a list: its length in unary, then the codes of its elements. -/
def writeList {α : Type} (enc : α → Word) (xs : List α) : Word :=
  writeNat xs.length ++ writeValues enc xs

/-- Parse a list, as written by `writeList`. -/
def readList {α : Type} (parse : Parser α) : Parser (List α) := fun input => do
  let (n, rest) ← readNat input
  readMany parse n rest

theorem readList_writeList {α : Type} (parse : Parser α) (enc : α → Word)
    (h : ∀ x rest, parse (enc x ++ rest) = some (x, rest))
    (xs : List α) (rest : Word) :
    readList parse (writeList enc xs ++ rest) = some (xs, rest) := by
  simp [readList, writeList, List.append_assoc, readMany_writeValues parse enc h]

/-- The code of a literal: its sign bit (`true` if positive), then its index in unary. -/
def encodeLiteral (l : Literal) : Word :=
  l.positive :: writeNat l.var

/-- Parse a literal, as written by `encodeLiteral`. -/
def readLiteral : Parser Literal
  | [] => none
  | sign :: rest => do
      let (v, tail) ← readNat rest
      pure (⟨v, sign⟩, tail)

@[simp] theorem readLiteral_encodeLiteral (l : Literal) (rest : Word) :
    readLiteral (encodeLiteral l ++ rest) = some (l, rest) := by
  cases l
  simp [encodeLiteral, readLiteral]

/-- The code of a clause: the list of its literals. -/
def encodeClause : Clause → Word := writeList encodeLiteral

/-- Parse a clause, as written by `encodeClause`. -/
def readClause : Parser Clause := readList readLiteral

@[simp] theorem readClause_encodeClause (c : Clause) (rest : Word) :
    readClause (encodeClause c ++ rest) = some (c, rest) :=
  readList_writeList readLiteral encodeLiteral readLiteral_encodeLiteral c rest

/-- The code of a CNF formula: the list of its clauses. -/
def encode : CNF → Word := writeList encodeClause

/-- Parse a formula, as written by `encode`. -/
def readCNF : Parser CNF := readList readClause

@[simp] theorem readCNF_encode (f : CNF) (rest : Word) :
    readCNF (encode f ++ rest) = some (f, rest) :=
  readList_writeList readClause encodeClause readClause_encodeClause f rest

/-- Decode a whole word as a formula: `none` unless the word is exactly the code
`encode f` of a formula `f`, in which case the result is `some f`. -/
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

/-- SAT: the words `encode f` with `f` satisfiable (no other word is in SAT). -/
def SAT (input : Word) : Prop :=
  ∃ f, encode f = input ∧ Satisfiable f

/-- 3-SAT: the words `encode f` with `f` satisfiable and `IsThreeCNF f`. -/
def ThreeSAT (input : Word) : Prop :=
  ∃ f, encode f = input ∧ IsThreeCNF f ∧ Satisfiable f

@[simp] theorem SAT_encode_iff (f : CNF) : SAT (encode f) ↔ Satisfiable f := by
  constructor
  · rintro ⟨g, hg, hs⟩
    rwa [encode_injective g f hg] at hs
  · exact fun hs => ⟨f, rfl, hs⟩

@[simp] theorem ThreeSAT_encode_iff (f : CNF) :
    ThreeSAT (encode f) ↔ IsThreeCNF f ∧ Satisfiable f := by
  constructor
  · rintro ⟨g, hg, h3, hs⟩
    rw [encode_injective g f hg] at h3 hs
    exact ⟨h3, hs⟩
  · exact fun ⟨h3, hs⟩ => ⟨f, rfl, h3, hs⟩

theorem not_SAT_of_decode_none {input : Word} (h : decode input = none) :
    ¬ SAT input := by
  rintro ⟨f, rfl, _⟩
  simp at h

theorem not_ThreeSAT_of_decode_none {input : Word} (h : decode input = none) :
    ¬ ThreeSAT input := by
  rintro ⟨f, rfl, _⟩
  simp at h

theorem ThreeSAT_implies_SAT {input : Word} (h : ThreeSAT input) : SAT input := by
  obtain ⟨f, hf, _, hs⟩ := h
  exact ⟨f, hf, hs⟩

/-- A successful unary parser determines exactly the consumed prefix. -/
theorem readNat_eq_some {input : Word} {n : Nat} {rest : Word}
    (h : readNat input = some (n, rest)) : input = writeNat n ++ rest := by
  induction input generalizing n with
  | nil => simp [readNat] at h
  | cons bit input ih =>
    cases bit with
    | false =>
      simp only [readNat, Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      rfl
    | true =>
      cases hp : readNat input with
      | none => simp [readNat, hp] at h
      | some pair =>
        rcases pair with ⟨m, tail⟩
        simp [readNat, hp] at h
        rcases h with ⟨rfl, rfl⟩
        simp [writeNat, ih hp]

theorem readLiteral_eq_some {input : Word} {l : Literal} {rest : Word}
    (h : readLiteral input = some (l, rest)) : input = encodeLiteral l ++ rest := by
  cases input with
  | nil => simp [readLiteral] at h
  | cons bit input =>
    cases hp : readNat input with
    | none => simp [readLiteral, hp] at h
    | some pair =>
      rcases pair with ⟨n, tail⟩
      simp [readLiteral, hp] at h
      rcases h with ⟨rfl, rfl⟩
      simp [encodeLiteral, readNat_eq_some hp]

theorem readMany_eq_some {α : Type} (parse : Parser α) (enc : α → Word)
    (hparse : ∀ {input x rest}, parse input = some (x, rest) → input = enc x ++ rest)
    {n : Nat} {input : Word} {xs : List α} {rest : Word}
    (h : readMany parse n input = some (xs, rest)) :
    xs.length = n ∧ input = writeValues enc xs ++ rest := by
  induction n generalizing input xs with
  | zero =>
    simp only [readMany, Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩
    simp [writeValues]
  | succ n ih =>
    cases hp : parse input with
    | none => simp [readMany, hp] at h
    | some pair =>
      rcases pair with ⟨x, tail⟩
      cases ht : readMany parse n tail with
      | none => simp [readMany, hp, ht] at h
      | some pair =>
        rcases pair with ⟨ys, tail'⟩
        simp [readMany, hp, ht] at h
        rcases h with ⟨rfl, rfl⟩
        obtain ⟨hlen, htail⟩ := ih ht
        constructor
        · simp [hlen]
        · rw [hparse hp, htail]
          simp [writeValues, List.append_assoc]

theorem readList_eq_some {α : Type} (parse : Parser α) (enc : α → Word)
    (hparse : ∀ {input x rest}, parse input = some (x, rest) → input = enc x ++ rest)
    {input : Word} {xs : List α} {rest : Word}
    (h : readList parse input = some (xs, rest)) : input = writeList enc xs ++ rest := by
  cases hp : readNat input with
  | none => simp [readList, hp] at h
  | some pair =>
    rcases pair with ⟨n, tail⟩
    simp [readList, hp] at h
    obtain ⟨hlen, htail⟩ := readMany_eq_some parse enc hparse h
    rw [readNat_eq_some hp, htail]
    simp [writeList, hlen, List.append_assoc]

theorem readClause_eq_some {input : Word} {c : Clause} {rest : Word}
    (h : readClause input = some (c, rest)) : input = encodeClause c ++ rest :=
  readList_eq_some readLiteral encodeLiteral readLiteral_eq_some h

theorem readCNF_eq_some {input : Word} {f : CNF} {rest : Word}
    (h : readCNF input = some (f, rest)) : input = encode f ++ rest :=
  readList_eq_some readClause encodeClause readClause_eq_some h

/-- Every accepted word is the unique canonical encoding of its decoded formula. -/
theorem decode_eq_some_iff (input : Word) (f : CNF) :
    decode input = some f ↔ input = encode f := by
  constructor
  · intro h
    cases hp : readCNF input with
    | none => simp [decode, hp] at h
    | some pair =>
      rcases pair with ⟨g, tail⟩
      cases tail with
      | nil =>
        have hg : g = f := by simpa [decode, hp] using h
        subst g
        simpa using readCNF_eq_some hp
      | cons bit tail => simp [decode, hp] at h
  · rintro rfl
    exact decode_encode f

/-- Membership in SAT, read through the parser `decode`. -/
theorem SAT_iff_decode (input : Word) :
    SAT input ↔ ∃ f, decode input = some f ∧ Satisfiable f := by
  constructor
  · rintro ⟨f, rfl, hs⟩
    exact ⟨f, decode_encode f, hs⟩
  · rintro ⟨f, hf, hs⟩
    exact ⟨f, ((decode_eq_some_iff input f).mp hf).symm, hs⟩

/-- Membership in 3-SAT, read through the parser `decode`. -/
theorem ThreeSAT_iff_decode (input : Word) :
    ThreeSAT input ↔ ∃ f, decode input = some f ∧ IsThreeCNF f ∧ Satisfiable f := by
  constructor
  · rintro ⟨f, rfl, h3, hs⟩
    exact ⟨f, decode_encode f, h3, hs⟩
  · rintro ⟨f, hf, h3, hs⟩
    exact ⟨f, ((decode_eq_some_iff input f).mp hf).symm, h3, hs⟩

end Complexity.SAT
