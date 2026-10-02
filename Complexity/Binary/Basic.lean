module

public import Complexity.SATVariants
public import Complexity.SATBounds
import Lean.Elab.Tactic.Omega

/-!
# Binary numerals and the parser for binary-indexed formulas

Binary digits are least significant first, as in `SAT.binaryValue`.

* `inc` and `binOf`: a binary counter, with `binaryValue (binOf n) = n`;
* `norm`: removal of trailing `false` digits, with
  `norm a = norm b ↔ binaryValue a = binaryValue b`;
* `decodeBinary`: a parser with `decodeBinary w = some f ↔ w = encodeBinary f`.
-/

@[expose] public section

namespace Complexity.Binary

open Complexity.SAT

/-! ## Binary counters -/

/-- Increment a binary numeral (least significant digit first). -/
def inc : List Bool → List Bool
  | [] => [true]
  | false :: bs => true :: bs
  | true :: bs => false :: inc bs

theorem binaryValue_inc (bs : List Bool) : binaryValue (inc bs) = binaryValue bs + 1 := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    cases b with
    | false => simp [inc, binaryValue]; omega
    | true => simp [inc, binaryValue, ih]; omega

theorem length_inc_le (bs : List Bool) : (inc bs).length ≤ bs.length + 1 := by
  induction bs with
  | nil => simp [inc]
  | cons b bs ih => cases b <;> simp [inc] <;> omega

/-- `inc` on a numeral written as `k` ones followed by the rest. -/
theorem inc_replicate_nil (k : Nat) :
    inc (List.replicate k true) = List.replicate k false ++ [true] := by
  induction k with
  | zero => rfl
  | succ k ih => simp [List.replicate_succ, inc, ih]

theorem inc_replicate_false (k : Nat) (rest : List Bool) :
    inc (List.replicate k true ++ false :: rest) = List.replicate k false ++ true :: rest := by
  induction k with
  | zero => rfl
  | succ k ih => simp [List.replicate_succ, inc, ih]

/-- The binary numeral of `n`, obtained by `n` increments of the empty numeral. -/
def binOf : Nat → List Bool
  | 0 => []
  | n + 1 => inc (binOf n)

@[simp] theorem binaryValue_binOf (n : Nat) : binaryValue (binOf n) = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [binOf, binaryValue_inc, ih]

theorem length_binOf_le (n : Nat) : (binOf n).length ≤ n := by
  induction n with
  | zero => simp [binOf]
  | succ n ih => exact Nat.le_trans (length_inc_le _) (by omega)

/-! ## Normal forms -/

/-- Remove trailing `false` digits. -/
def norm : List Bool → List Bool
  | [] => []
  | b :: bs => if (norm bs).isEmpty && !b then [] else b :: norm bs

theorem binaryValue_norm (bs : List Bool) : binaryValue (norm bs) = binaryValue bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    by_cases h : (norm bs).isEmpty && !b
    · have h' : norm bs = [] ∧ b = false := by
        simpa [List.isEmpty_iff] using h
      obtain ⟨hn, rfl⟩ := h'
      rw [hn] at ih
      simp [norm, hn, binaryValue, ← ih]
    · simp only [norm, h]
      simp [binaryValue, ih]

/-- The canonical numeral of a value. -/
def canon (v : Nat) : List Bool :=
  if h : v = 0 then [] else (v % 2 == 1) :: canon (v / 2)
termination_by v
decreasing_by omega

theorem canon_zero : canon 0 = [] := by
  rw [canon]; simp

theorem canon_pos {v : Nat} (h : v ≠ 0) : canon v = (v % 2 == 1) :: canon (v / 2) := by
  rw [canon]; simp [h]

theorem binaryValue_canon (v : Nat) : binaryValue (canon v) = v := by
  induction v using Nat.strongRecOn with
  | ind v ih =>
    by_cases h : v = 0
    · subst v; rw [canon_zero]; rfl
    · rw [canon_pos h]
      simp only [binaryValue]
      rw [ih (v / 2) (by omega)]
      cases hm : v % 2 == 1 <;> simp at hm <;> simp <;> omega

theorem norm_eq_canon (bs : List Bool) : norm bs = canon (binaryValue bs) := by
  induction bs with
  | nil => simp [norm, binaryValue, canon_zero]
  | cons b bs ih =>
    by_cases hv : b.toNat + 2 * binaryValue bs = 0
    · have hb : b = false := by cases b <;> simp at hv ⊢
      subst b
      have hz : binaryValue bs = 0 := by simp at hv; omega
      rw [hz, canon_zero] at ih
      simp [norm, ih, binaryValue, hz, canon_zero]
    · have hcond : ¬ ((norm bs).isEmpty && !b) = true := by
        intro hc
        have h' : norm bs = [] ∧ b = false := by simpa [List.isEmpty_iff] using hc
        obtain ⟨hn, rfl⟩ := h'
        have := binaryValue_norm bs
        rw [hn] at this
        simp [binaryValue] at this
        simp [← this] at hv
      simp only [norm, hcond, binaryValue]
      rw [canon_pos hv, ih]
      have h1 : ((b.toNat + 2 * binaryValue bs) % 2 == 1) = b := by
        cases b <;> simp <;> omega
      have h2 : (b.toNat + 2 * binaryValue bs) / 2 = binaryValue bs := by
        cases b <;> simp <;> omega
      rw [h1, h2]
      simp

/-- Two digit lists name the same variable iff their normal forms agree. -/
theorem norm_eq_norm_iff (a b : List Bool) :
    norm a = norm b ↔ binaryValue a = binaryValue b := by
  constructor
  · intro h
    rw [← binaryValue_norm a, ← binaryValue_norm b, h]
  · intro h
    rw [norm_eq_canon, norm_eq_canon, h]

/-- The normal form, as computed by popping leading `false` digits off the reversed list. -/
theorem reverse_dropWhile_reverse (bs : List Bool) :
    (bs.reverse.dropWhile (fun b => !b)).reverse = norm bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    simp only [List.reverse_cons, List.dropWhile_append]
    by_cases h : (List.dropWhile (fun b => !b) bs.reverse).isEmpty
    · have hn : norm bs = [] := by
        rw [← ih]
        simpa [List.isEmpty_iff] using h
      cases b <;> simp [h, norm, hn]
    · have hn : ¬ (norm bs).isEmpty := by
        rw [← ih]
        simpa [List.isEmpty_iff] using h
      simp only [h, Bool.false_eq_true, ite_false, List.reverse_append, ih]
      simp [norm, hn]

/-! ## Parsing binary-indexed formulas -/

/-- Read one bit. -/
def readBit : Parser Bool
  | [] => none
  | b :: rest => some (b, rest)

@[simp] theorem readBit_encode (b : Bool) (rest : Word) :
    readBit ([b] ++ rest) = some (b, rest) := rfl

theorem readBit_eq_some {input : Word} {b : Bool} {rest : Word}
    (h : readBit input = some (b, rest)) : input = [b] ++ rest := by
  cases input with
  | nil => simp [readBit] at h
  | cons c input =>
    simp only [readBit, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl

theorem writeValues_single (bits : List Bool) : writeValues (fun b => [b]) bits = bits := by
  induction bits with
  | nil => rfl
  | cons b bits ih => simp [writeValues, ih]

/-- Parse a binary literal, as written by `encodeBinaryLiteral`. -/
def readBinaryLiteral : Parser BinaryLiteral
  | [] => none
  | sign :: rest => do
      let (bits, tail) ← readList readBit rest
      pure (⟨bits, sign⟩, tail)

@[simp] theorem readBinaryLiteral_encode (l : BinaryLiteral) (rest : Word) :
    readBinaryLiteral (encodeBinaryLiteral l ++ rest) = some (l, rest) := by
  cases l with
  | mk bits positive =>
    have h := readList_writeList readBit (fun b => [b]) readBit_encode bits rest
    simp [encodeBinaryLiteral, readBinaryLiteral, h]

theorem readBinaryLiteral_eq_some {input : Word} {l : BinaryLiteral} {rest : Word}
    (h : readBinaryLiteral input = some (l, rest)) : input = encodeBinaryLiteral l ++ rest := by
  cases input with
  | nil => simp [readBinaryLiteral] at h
  | cons sign input =>
    cases hp : readList readBit input with
    | none => simp [readBinaryLiteral, hp] at h
    | some pair =>
      obtain ⟨bits, tail⟩ := pair
      simp only [readBinaryLiteral, hp, Option.bind_eq_bind, Option.bind_some,
        Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have he := readList_eq_some readBit (fun b => [b]) readBit_eq_some hp
      simp [encodeBinaryLiteral, he]

/-- Parse a clause of binary literals. -/
def readBinaryClause : Parser (List BinaryLiteral) := readList readBinaryLiteral

/-- Parse a formula of binary literals. -/
def readBinaryCNF : Parser (List (List BinaryLiteral)) := readList readBinaryClause

/-- The code of a clause of binary literals. -/
def encodeBinaryClause : List BinaryLiteral → Word := writeList encodeBinaryLiteral

theorem encodeBinary_eq (f : List (List BinaryLiteral)) :
    encodeBinary f = writeList encodeBinaryClause f := rfl

@[simp] theorem readBinaryClause_encode (c : List BinaryLiteral) (rest : Word) :
    readBinaryClause (encodeBinaryClause c ++ rest) = some (c, rest) :=
  readList_writeList readBinaryLiteral encodeBinaryLiteral readBinaryLiteral_encode c rest

theorem readBinaryClause_eq_some {input : Word} {c : List BinaryLiteral} {rest : Word}
    (h : readBinaryClause input = some (c, rest)) : input = encodeBinaryClause c ++ rest :=
  readList_eq_some readBinaryLiteral encodeBinaryLiteral readBinaryLiteral_eq_some h

@[simp] theorem readBinaryCNF_encode (f : List (List BinaryLiteral)) (rest : Word) :
    readBinaryCNF (encodeBinary f ++ rest) = some (f, rest) :=
  readList_writeList readBinaryClause encodeBinaryClause readBinaryClause_encode f rest

theorem readBinaryCNF_eq_some {input : Word} {f : List (List BinaryLiteral)} {rest : Word}
    (h : readBinaryCNF input = some (f, rest)) : input = encodeBinary f ++ rest :=
  readList_eq_some readBinaryClause encodeBinaryClause readBinaryClause_eq_some h

/-- Decode a whole word as a binary-indexed formula. -/
def decodeBinary (input : Word) : Option (List (List BinaryLiteral)) :=
  match readBinaryCNF input with
  | some (f, []) => some f
  | _ => none

@[simp] theorem decodeBinary_encode (f : List (List BinaryLiteral)) :
    decodeBinary (encodeBinary f) = some f := by
  have h := readBinaryCNF_encode f []
  simp only [List.append_nil] at h
  simp [decodeBinary, h]

theorem decodeBinary_eq_some_iff (input : Word) (f : List (List BinaryLiteral)) :
    decodeBinary input = some f ↔ input = encodeBinary f := by
  constructor
  · intro h
    cases hp : readBinaryCNF input with
    | none => simp [decodeBinary, hp] at h
    | some pair =>
      obtain ⟨g, tail⟩ := pair
      cases tail with
      | nil =>
        have hg : g = f := by simpa [decodeBinary, hp] using h
        subst g
        simpa using readBinaryCNF_eq_some hp
      | cons b tail => simp [decodeBinary, hp] at h
  · rintro rfl
    exact decodeBinary_encode f

theorem encodeBinary_injective {f g : List (List BinaryLiteral)}
    (h : encodeBinary f = encodeBinary g) : f = g := by
  have h' := congrArg decodeBinary h
  simpa using h'

@[simp] theorem BinarySAT_encodeBinary_iff (f : List (List BinaryLiteral)) :
    BinarySAT (encodeBinary f) ↔ Satisfiable (f.map (List.map BinaryLiteral.toLiteral)) := by
  constructor
  · rintro ⟨g, hg, hs⟩
    rwa [encodeBinary_injective hg] at hs
  · exact fun hs => ⟨f, rfl, hs⟩

theorem BinarySAT_iff_decode (input : Word) :
    BinarySAT input ↔ ∃ f, decodeBinary input = some f ∧
      Satisfiable (f.map (List.map BinaryLiteral.toLiteral)) := by
  constructor
  · rintro ⟨f, rfl, hs⟩
    exact ⟨f, decodeBinary_encode f, hs⟩
  · rintro ⟨f, hf, hs⟩
    exact ⟨f, ((decodeBinary_eq_some_iff input f).mp hf).symm, hs⟩

theorem not_BinarySAT_of_decode_none {input : Word} (h : decodeBinary input = none) :
    ¬ BinarySAT input := by
  rintro ⟨f, rfl, _⟩
  simp at h

end Complexity.Binary
