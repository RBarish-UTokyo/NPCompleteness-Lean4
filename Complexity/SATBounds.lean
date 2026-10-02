module

public import Complexity.ThreeSAT
import Lean.Elab.Tactic.Omega

/-!
# Encoded sizes for SAT and the 3-CNF transformation

All lengths in the final bounds count bits of the concrete unary-index encoding
from `Complexity.SAT`.  These are output-size results, not machine-time results.
-/

@[expose] public section

namespace Complexity.SATBounds

open Complexity.SAT Complexity.ThreeSAT

@[simp] theorem writeNat_length (n : Nat) : (writeNat n).length = n + 1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [writeNat, ih, Nat.add_assoc]

@[simp] theorem encodeLiteral_length (l : Literal) :
    (encodeLiteral l).length = l.var + 2 := by
  simp [encodeLiteral, Nat.add_assoc]

@[simp] theorem encodeClause_nil_length : (encodeClause []).length = 1 := rfl

theorem encodeClause_cons_length (l : Literal) (c : Clause) :
    (encodeClause (l :: c)).length = l.var + 3 + (encodeClause c).length := by
  simp [encodeClause, writeList, writeValues, Nat.add_assoc, Nat.add_comm,
    Nat.add_left_comm]
  omega

@[simp] theorem encode_nil_length : (encode []).length = 1 := rfl

theorem encode_cons_length (c : Clause) (f : CNF) :
    (encode (c :: f)).length = (encodeClause c).length + 1 + (encode f).length := by
  simp [encode, writeList, writeValues, Nat.add_assoc, Nat.add_comm,
    Nat.add_left_comm]
  omega

theorem clauseBound_add_length_le_encodeClause (c : Clause) :
    clauseBound c + c.length + 1 ≤ (encodeClause c).length := by
  induction c with
  | nil => simp [clauseBound]
  | cons l c ih =>
    rw [encodeClause_cons_length]
    simp only [clauseBound, List.length_cons]
    have hm : max (l.var + 1) (clauseBound c) ≤ l.var + 1 + clauseBound c :=
      Nat.max_le.mpr ⟨by omega, by omega⟩
    omega

theorem variableBound_add_formulaSize_le_encode_length (f : CNF) :
    variableBound f + formulaSize f + 1 ≤ (encode f).length := by
  induction f with
  | nil => simp [variableBound, formulaSize]
  | cons c f ih =>
    rw [encode_cons_length]
    simp only [variableBound, formulaSize]
    have hc := clauseBound_add_length_le_encodeClause c
    have hm : max (clauseBound c) (variableBound f) ≤
        clauseBound c + variableBound f := Nat.max_le.mpr ⟨by omega, by omega⟩
    omega

theorem variableBound_le_encode_length (f : CNF) :
    variableBound f ≤ (encode f).length := by
  have := variableBound_add_formulaSize_le_encode_length f
  omega

theorem formulaSize_le_encode_length (f : CNF) :
    formulaSize f ≤ (encode f).length := by
  have := variableBound_add_formulaSize_le_encode_length f
  omega

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

theorem splitCNF_below (n : Nat) (f : CNF) (hf : CNFBelow n f) :
    CNFBelow (n + formulaSize f) (splitCNF n f) := by
  induction f generalizing n with
  | nil => simp [splitCNF, CNFBelow]
  | cons c rest ih =>
    have hc : ClauseBelow n c := hf c (by simp)
    have hr : CNFBelow (n + c.length + 1) rest := by
      intro d hd l hl
      have := hf d (by simp [hd]) l hl
      omega
    have hhead := splitClause_below n c hc
    have htail := ih (n + c.length + 1) hr
    intro d hd l hl
    simp only [splitCNF, List.mem_append] at hd
    rcases hd with hd | hd
    · have := hhead d hd l hl
      simp only [formulaSize]
      omega
    · have := htail d hd l hl
      simp only [formulaSize]
      omega

theorem encodeClause_length_le (n : Nat) (c : Clause) (hc : ClauseBelow n c) :
    (encodeClause c).length ≤ (n + 2) * c.length + 1 := by
  induction c with
  | nil => simp
  | cons l c ih =>
    have hl : l.var < n := hc l (by simp)
    have hr : ClauseBelow n c := by
      intro x hx
      exact hc x (by simp [hx])
    have ht := ih hr
    rw [encodeClause_cons_length]
    simp only [List.length_cons, Nat.mul_add, Nat.mul_one]
    omega

theorem encode_three_length_le (n : Nat) (f : CNF) (hf : CNFBelow n f)
    (hthree : IsThreeCNF f) :
    (encode f).length ≤ (3 * n + 8) * f.length + 1 := by
  induction f with
  | nil => simp
  | cons c f ih =>
    have hc : ClauseBelow n c := hf c (by simp)
    have hr : CNFBelow n f := by
      intro d hd
      exact hf d (by simp [hd])
    have hc3 : c.length ≤ 3 := hthree c (by simp)
    have hr3 : IsThreeCNF f := by
      intro d hd
      exact hthree d (by simp [hd])
    have ht := ih hr hr3
    have hcl := encodeClause_length_le n c hc
    have hmul := Nat.mul_le_mul_left (n + 2) hc3
    rw [encode_cons_length]
    simp only [List.length_cons, Nat.mul_add, Nat.mul_one]
    omega

/-- A size-sensitive bound before replacing input parameters by bit length. -/
theorem toThreeCNF_encode_length_precise (f : CNF) :
    (encode (toThreeCNF f)).length ≤
      (3 * (variableBound f + formulaSize f) + 8) * formulaSize f + 1 := by
  have hb := splitCNF_below (variableBound f) f (input_below_bound f)
  have hs := encode_three_length_le (variableBound f + formulaSize f)
    (toThreeCNF f) hb (toThreeCNF_three f)
  have hm := Nat.mul_le_mul_left
    (3 * (variableBound f + formulaSize f) + 8) (toThreeCNF_length f)
  omega

/-- Quadratic bit-size bound for canonical formula inputs. -/
theorem toThreeCNF_encode_length (f : CNF) :
    (encode (toThreeCNF f)).length ≤
      (3 * (encode f).length + 8) * (encode f).length + 1 := by
  have hs := toThreeCNF_encode_length_precise f
  have hb := variableBound_add_formulaSize_le_encode_length f
  have hp : 3 * (variableBound f + formulaSize f) + 8 ≤ 3 * (encode f).length + 8 := by
    omega
  have hm := Nat.mul_le_mul hp (formulaSize_le_encode_length f)
  omega

/-- The total encoded reduction has quadratic output length, including malformed inputs. -/
theorem reduceWord_length (input : Word) :
    (reduceWord input).length ≤ (3 * input.length + 8) * input.length + 3 := by
  cases hd : decode input with
  | none =>
    simp [reduceWord, hd, encode, encodeClause, writeList, writeValues, writeNat]
  | some f =>
    have heq := (decode_eq_some_iff input f).mp hd
    have hs := toThreeCNF_encode_length f
    simp only [reduceWord, hd]
    rw [heq]
    omega

end Complexity.SATBounds
