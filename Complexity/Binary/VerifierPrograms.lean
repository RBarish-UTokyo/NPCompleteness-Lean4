module

public import Complexity.Binary.Spec
public import Complexity.Binary.StackTools
import Lean.Elab.Tactic.Omega

/-!
# Small stack programs for the binary SAT verifier

The verifier stores one *entry* per literal occurrence: the certificate bit `c` of the
occurrence and the normal form `ds` of its digits, coded as `entryCode (c, ds)`: each digit
`d` as `true, d`, then `false, c`. This file gives the programs that read digits, normalize
them, write an entry, load an entry, and compare an entry with a stored digit list.
-/

@[expose] public section

namespace Complexity.Binary

open Complexity.StackMachine (Registers set branch)
open Complexity.StackProgram Complexity.StackWords
open Complexity.SAT (Word)

/-! ## Entry codes -/

/-- Each digit `d` as the pair `true, d`. -/
def pairs : List Bool → Word
  | [] => []
  | d :: ds => true :: d :: pairs ds

theorem pairs_append (xs ys : List Bool) : pairs (xs ++ ys) = pairs xs ++ pairs ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [pairs, ih]

@[simp] theorem pairs_length (ds : List Bool) : (pairs ds).length = 2 * ds.length := by
  induction ds with
  | nil => rfl
  | cons d ds ih => simp [pairs, ih]; omega

/-- The code of an entry. -/
def entryCode (e : Bool × List Bool) : Word := pairs e.2 ++ [false, e.1]

/-- The code of a list of entries. -/
def writeEntries : List (Bool × List Bool) → Word
  | [] => []
  | e :: es => entryCode e ++ writeEntries es

theorem writeEntries_append (es fs : List (Bool × List Bool)) :
    writeEntries (es ++ fs) = writeEntries es ++ writeEntries fs := by
  induction es with
  | nil => rfl
  | cons e es ih => simp [writeEntries, ih, List.append_assoc]

/-- Read an entry. -/
def readEntry : Word → Option ((Bool × List Bool) × Word)
  | true :: d :: rest =>
    match readEntry rest with
    | none => none
    | some ((c, ds), tail) => some ((c, d :: ds), tail)
  | false :: c :: rest => some ((c, []), rest)
  | _ => none

theorem readEntry_pairs (ds : List Bool) (c : Bool) (rest : Word) :
    readEntry (pairs ds ++ false :: c :: rest) = some ((c, ds), rest) := by
  induction ds with
  | nil => rfl
  | cons d ds ih => simp [pairs, readEntry, ih]

@[simp] theorem readEntry_entryCode (e : Bool × List Bool) (rest : Word) :
    readEntry (entryCode e ++ rest) = some (e, rest) := by
  simpa [entryCode] using readEntry_pairs e.2 e.1 rest

/-! ## Reading bits -/

/-- Move one bit from `src` to `dst`; fail on an empty source. -/
def takeBit {k : Nat} (src dst : Fin (k + 1)) : Program k (Fin 5) where
  start := 0
  code := fun q => if q = 0 then .pop src 1 2 3
    else if q = 1 then .halt false
    else if q = 2 then .push dst false 4
    else if q = 3 then .push dst true 4
    else .halt true

theorem exec_takeBit_cons {k : Nat} (src dst : Fin (k + 1)) (hsd : src ≠ dst)
    (r : Registers k) (b : Bool) (tail : List Bool) (hr : r src = b :: tail) :
    Exec (takeBit src dst) 0 r 3 (true, set (set r src tail) dst (b :: r dst)) := by
  have hp : StackProgram.step (takeBit src dst) 0 r =
      .inr ((if b then 3 else 2), set r src tail) := by
    cases b <;> simp [StackProgram.step, takeBit, hr, branch]
  have hs : StackProgram.step (takeBit src dst) (if b then 3 else 2) (set r src tail) =
      .inr (4, set (set r src tail) dst (b :: r dst)) := by
    cases b <;> simp [StackProgram.step, takeBit, Ne.symm hsd]
  exact .next hp (.next hs (.halt (by simp [StackProgram.step, takeBit])))

theorem exec_takeBit_nil {k : Nat} (src dst : Fin (k + 1)) (r : Registers k) (hr : r src = []) :
    Exec (takeBit src dst) 0 r 2 (false, r) := by
  have hset : set r src [] = r := by rw [← hr, set_unchanged]
  apply Exec.next (q' := 1) (r' := r)
  · simp [StackProgram.step, takeBit, hr, branch, hset]
  · exact .halt (by simp [StackProgram.step, takeBit])

def takeBitEncoding : Encoding (Fin 5) := Encoding.fin 4

/-- Move `n` bits, `n` given by a unary counter. -/
def takeBits {k : Nat} (cnt src dst : Fin (k + 1)) := whileCounter cnt (takeBit src dst)

def takeBitsEncoding : Encoding (Sum Bool (Fin 5)) := Encoding.bool.sum takeBitEncoding

theorem exec_takeBits {k : Nat} (cnt src dst : Fin (k + 1)) (hsd : src ≠ dst)
    (hcs : cnt ≠ src) (hcd : cnt ≠ dst) (bits rest : List Bool) (r : Registers k)
    (hi : r src = bits ++ rest) (hc : r cnt = List.replicate bits.length true) :
    Exec (takeBits cnt src dst) (.inl false) r (4 * bits.length + 2)
      (true, set (set (set r src rest) cnt []) dst (bits.reverse ++ r dst)) := by
  induction bits generalizing r with
  | nil =>
    have hh := exec_whileCounter_done cnt (takeBit src dst) r (by simpa using hc)
    have hout : set (set (set r src rest) cnt []) dst ([].reverse ++ r dst) = r := by
      funext a
      by_cases hd : a = dst
      · subst a; simp
      · by_cases hcnt : a = cnt
        · subst a; simp [hd, hc]
        · by_cases hs : a = src
          · subst a; simp [hd, hcnt, hi]
          · simp [StackMachine.set, hd, hcnt, hs]
    rw [hout]
    exact hh
  | cons b bits ih =>
    let r₀ := set r cnt (List.replicate bits.length true)
    let r₁ := set (set r₀ src (bits ++ rest)) dst (b :: r₀ dst)
    have hi₀ : r₀ src = b :: (bits ++ rest) := by simpa [r₀, Ne.symm hcs] using hi
    have hbody := exec_takeBit_cons src dst hsd r₀ b (bits ++ rest) hi₀
    have hi₁ : r₁ src = bits ++ rest := by simp [r₁, hsd]
    have hc₁ : r₁ cnt = List.replicate bits.length true := by simp [r₁, r₀, hcs, hcd]
    have hrest := ih r₁ hi₁ hc₁
    have hh := exec_whileCounter_next cnt (takeBit src dst)
      (by simpa [List.replicate_succ] using hc) hbody hrest
    have hout : set (set (set r₁ src rest) cnt []) dst (bits.reverse ++ r₁ dst) =
        set (set (set r src rest) cnt []) dst ((b :: bits).reverse ++ r dst) := by
      funext a
      by_cases hd : a = dst
      · subst a; simp [r₁, r₀, Ne.symm hcd, List.append_assoc]
      · by_cases hcnt : a = cnt
        · subst a; simp [hd]
        · by_cases hs : a = src
          · subst a; simp [hd, hcnt]
          · simp [r₁, r₀, StackMachine.set, hd, hcnt, hs]
    rw [hout] at hh
    have hcost : 3 + (4 * bits.length + 2) + 1 = 4 * (b :: bits).length + 2 := by simp; omega
    rw [hcost] at hh
    exact hh

theorem exec_takeBits_short {k : Nat} (cnt src dst : Fin (k + 1)) (hsd : src ≠ dst)
    (hcs : cnt ≠ src) (hcd : cnt ≠ dst) (xs : List Bool) (n : Nat) (r : Registers k)
    (hi : r src = xs) (hc : r cnt = List.replicate n true) (hn : xs.length < n) :
    ∃ out, Exec (takeBits cnt src dst) (.inl false) r (4 * xs.length + 3) (false, out) := by
  induction xs generalizing n r with
  | nil =>
    cases n with
    | zero => simp at hn
    | succ n =>
      let r₀ := set r cnt (List.replicate n true)
      have he := exec_takeBit_nil src dst r₀ (by simpa [r₀, Ne.symm hcs] using hi)
      exact ⟨r₀, exec_whileCounter_failure cnt (takeBit src dst)
        (by simpa [List.replicate_succ] using hc) he⟩
  | cons b xs ih =>
    cases n with
    | zero => simp at hn
    | succ n =>
      let r₀ := set r cnt (List.replicate n true)
      let r₁ := set (set r₀ src xs) dst (b :: r₀ dst)
      have hb := exec_takeBit_cons src dst hsd r₀ b xs (by simpa [r₀, Ne.symm hcs] using hi)
      obtain ⟨out, ht⟩ := ih n r₁ (by simp [r₁, hsd]) (by simp [r₁, r₀, hcs, hcd])
        (by simpa using hn)
      have hh := exec_whileCounter_next cnt (takeBit src dst)
        (by simpa [List.replicate_succ] using hc) hb ht
      refine ⟨out, ?_⟩
      have hcost : 3 + (4 * xs.length + 3) + 1 = 4 * (b :: xs).length + 3 := by simp; omega
      rw [hcost] at hh
      exact hh

/-! ## Normalizing digits -/

/-- Pop leading `false` bits. -/
def stripZeros {k : Nat} (j : Fin (k + 1)) : Program k (Fin 3) where
  start := 0
  code := fun q => if q = 0 then .peek j 2 1 2
    else if q = 1 then .pop j 0 0 0
    else .halt true

def stripZerosEncoding : Encoding (Fin 3) := Encoding.fin 2

theorem exec_stripZeros {k : Nat} (j : Fin (k + 1)) (r : Registers k) :
    ∃ t, t ≤ 2 * (r j).length + 2 ∧
      Exec (stripZeros j) 0 r t (true, set r j ((r j).dropWhile (fun b => !b))) := by
  generalize hx : r j = xs
  induction xs generalizing r with
  | nil =>
    refine ⟨2, by simp, ?_⟩
    have hset : set r j [] = r := by rw [← hx, set_unchanged]
    simp only [List.dropWhile_nil, hset]
    apply Exec.next (q' := 2) (r' := r)
    · simp [StackProgram.step, stripZeros, hx, branch]
    · exact .halt (by simp [StackProgram.step, stripZeros])
  | cons b xs ih =>
    cases b with
    | true =>
      refine ⟨2, by simp, ?_⟩
      have hset : set r j (true :: xs) = r := by rw [← hx, set_unchanged]
      simp only [List.dropWhile_cons, Bool.not_true, Bool.false_eq_true, ite_false, hset]
      apply Exec.next (q' := 2) (r' := r)
      · simp [StackProgram.step, stripZeros, hx, branch]
      · exact .halt (by simp [StackProgram.step, stripZeros])
    | false =>
      obtain ⟨t, ht, he⟩ := ih (set r j xs) (by simp)
      refine ⟨t + 2, by simp; omega, ?_⟩
      have h₁ : StackProgram.step (stripZeros j) 0 r = .inr (1, r) := by
        simp [StackProgram.step, stripZeros, hx, branch]
      have h₂ : StackProgram.step (stripZeros j) 1 r = .inr (0, set r j xs) := by
        simp [StackProgram.step, stripZeros, hx, branch]
      have hh := Exec.next h₁ (Exec.next h₂ he)
      simp only [List.dropWhile_cons, Bool.not_false, ite_true]
      simpa [set_overwrite, Nat.add_assoc] using hh

/-! ## Writing an entry -/

/-- Pop each bit `d` of `src` and push `d` then `true` onto `dst`. -/
def emitPairs {k : Nat} (src dst : Fin (k + 1)) : Program k (Fin 5) where
  start := 0
  code := fun q => if q = 0 then .pop src 4 1 2
    else if q = 1 then .push dst false 3
    else if q = 2 then .push dst true 3
    else if q = 3 then .push dst true 0
    else .halt true

def emitPairsEncoding : Encoding (Fin 5) := Encoding.fin 4

theorem exec_emitPairs {k : Nat} (src dst : Fin (k + 1)) (hsd : src ≠ dst) (r : Registers k) :
    Exec (emitPairs src dst) 0 r (3 * (r src).length + 2)
      (true, set (set r src []) dst (pairs (r src).reverse ++ r dst)) := by
  generalize hx : r src = xs
  induction xs generalizing r with
  | nil =>
    have hset : set r src [] = r := by rw [← hx, set_unchanged]
    simp only [List.length_nil, Nat.mul_zero, Nat.zero_add, List.reverse_nil, pairs,
      List.nil_append, hset, set_unchanged]
    apply Exec.next (q' := 4) (r' := r)
    · simp [StackProgram.step, emitPairs, hx, branch, hset]
    · exact .halt (by simp [StackProgram.step, emitPairs])
  | cons b xs ih =>
    let r₁ := set r src xs
    let r₂ := set r₁ dst (b :: r₁ dst)
    let r₃ := set r₂ dst (true :: r₂ dst)
    have h₁ : StackProgram.step (emitPairs src dst) 0 r = .inr ((if b then 2 else 1), r₁) := by
      cases b <;> simp [StackProgram.step, emitPairs, hx, branch, r₁]
    have h₂ : StackProgram.step (emitPairs src dst) (if b then 2 else 1) r₁ = .inr (3, r₂) := by
      cases b <;> simp [StackProgram.step, emitPairs, r₂]
    have h₃ : StackProgram.step (emitPairs src dst) 3 r₂ = .inr (0, r₃) := by
      simp [StackProgram.step, emitPairs, r₃]
    have he := ih r₃ (by simp [r₃, r₂, r₁, hsd])
    have hh := Exec.next h₁ (Exec.next h₂ (Exec.next h₃ he))
    have hout : set (set r₃ src []) dst (pairs xs.reverse ++ r₃ dst) =
        set (set r src []) dst (pairs (b :: xs).reverse ++ r dst) := by
      funext a
      by_cases hd : a = dst
      · subst a
        simp [r₃, r₂, r₁, Ne.symm hsd, pairs_append, pairs, List.append_assoc]
      · by_cases hs : a = src
        · subst a; simp [hd]
        · simp [r₃, r₂, r₁, StackMachine.set, hd, hs]
    rw [hout] at hh
    have hcost : 3 * xs.length + 2 + 1 + 1 + 1 = 3 * (b :: xs).length + 2 := by simp; omega
    rw [hcost] at hh
    exact hh

/-! ## Loading an entry -/

/-- Read an entry from `src`: its digits are pushed onto `D` (so `D` gets them reversed)
and its bit onto `C`. Fail on a malformed entry. -/
def loadEntry {k : Nat} (src D C : Fin (k + 1)) : Program k (Fin 9) where
  start := 0
  code := fun q => if q = 0 then .pop src 8 5 1
    else if q = 1 then .pop src 8 2 3
    else if q = 2 then .push D false 0
    else if q = 3 then .push D true 0
    else if q = 4 then .halt true
    else if q = 5 then .pop src 8 6 7
    else if q = 6 then .push C false 4
    else if q = 7 then .push C true 4
    else .halt false

def loadEntryEncoding : Encoding (Fin 9) := Encoding.fin 8

theorem exec_loadEntry_pairs {k : Nat} (src D C : Fin (k + 1)) (hsD : src ≠ D)
    (hsC : src ≠ C) (hDC : D ≠ C) (ds : List Bool) (c : Bool) (rest : Word) (r : Registers k)
    (hr : r src = pairs ds ++ false :: c :: rest) :
    Exec (loadEntry src D C) 0 r (3 * ds.length + 4)
      (true, set (set (set r src rest) D (ds.reverse ++ r D)) C (c :: r C)) := by
  induction ds generalizing r with
  | nil =>
    let r₁ := set r src (c :: rest)
    let r₂ := set r₁ src rest
    let r₃ := set r₂ C (c :: r₂ C)
    have h₁ : StackProgram.step (loadEntry src D C) 0 r = .inr (5, r₁) := by
      simp [StackProgram.step, loadEntry, hr, branch, pairs, r₁]
    have h₂ : StackProgram.step (loadEntry src D C) 5 r₁ = .inr ((if c then 7 else 6), r₂) := by
      cases c <;> simp [StackProgram.step, loadEntry, r₂, r₁, branch]
    have h₃ : StackProgram.step (loadEntry src D C) (if c then 7 else 6) r₂ = .inr (4, r₃) := by
      cases c <;> simp [StackProgram.step, loadEntry, r₃]
    have hh := Exec.next h₁ (Exec.next h₂ (Exec.next h₃
      (Exec.halt (result := (true, r₃)) (by simp [StackProgram.step, loadEntry]))))
    have hout : r₃ = set (set (set r src rest) D ([].reverse ++ r D)) C (c :: r C) := by
      funext a
      by_cases hc : a = C
      · subst a; simp [r₃, r₂, r₁, Ne.symm hsC]
      · by_cases hd : a = D
        · subst a; simp [r₃, r₂, r₁, hc, Ne.symm hsD]
        · by_cases hs : a = src
          · subst a; simp [r₃, r₂, r₁, hc, hd]
          · simp [r₃, r₂, r₁, StackMachine.set, hc, hd, hs]
    rw [hout] at hh
    exact hh
  | cons d ds ih =>
    let r₁ := set r src (d :: (pairs ds ++ false :: c :: rest))
    let r₂ := set r₁ src (pairs ds ++ false :: c :: rest)
    let r₃ := set r₂ D (d :: r₂ D)
    have h₁ : StackProgram.step (loadEntry src D C) 0 r = .inr (1, r₁) := by
      simp [StackProgram.step, loadEntry, hr, branch, pairs, r₁]
    have h₂ : StackProgram.step (loadEntry src D C) 1 r₁ = .inr ((if d then 3 else 2), r₂) := by
      cases d <;> simp [StackProgram.step, loadEntry, r₂, r₁, branch]
    have h₃ : StackProgram.step (loadEntry src D C) (if d then 3 else 2) r₂ = .inr (0, r₃) := by
      cases d <;> simp [StackProgram.step, loadEntry, r₃]
    have he := ih r₃ (by simp [r₃, r₂, r₁, hsD])
    have hh := Exec.next h₁ (Exec.next h₂ (Exec.next h₃ he))
    have hout : set (set (set r₃ src rest) D (ds.reverse ++ r₃ D)) C (c :: r₃ C) =
        set (set (set r src rest) D ((d :: ds).reverse ++ r D)) C (c :: r C) := by
      funext a
      by_cases hc : a = C
      · subst a; simp [r₃, r₂, r₁, Ne.symm hsC, Ne.symm hDC]
      · by_cases hd : a = D
        · subst a; simp [r₃, r₂, r₁, hc, Ne.symm hsD, List.append_assoc]
        · by_cases hs : a = src
          · subst a; simp [r₃, r₂, r₁, hc, hd]
          · simp [r₃, r₂, r₁, StackMachine.set, hc, hd, hs]
    rw [hout] at hh
    have hcost : 3 * ds.length + 4 + 1 + 1 + 1 = 3 * (d :: ds).length + 4 := by simp; omega
    rw [hcost] at hh
    exact hh


theorem exec_loadEntry_malformed {k : Nat} (src D C : Fin (k + 1)) (hsD : src ≠ D) :
    ∀ (xs : Word) (r : Registers k), r src = xs → readEntry xs = none →
      ∃ t out, t ≤ 3 * xs.length + 3 ∧ Exec (loadEntry src D C) 0 r t (false, out)
  | [], r, hr, _ => by
    refine ⟨2, r, by simp, ?_⟩
    have hset : set r src [] = r := by rw [← hr, set_unchanged]
    apply Exec.next (q' := 8) (r' := r)
    · simp [StackProgram.step, loadEntry, hr, branch, hset]
    · exact .halt (by simp [StackProgram.step, loadEntry])
  | [b], r, hr, _ => by
    refine ⟨3, set r src [], by simp, ?_⟩
    cases b with
    | true =>
      apply Exec.next (q' := 1) (r' := set r src [])
      · simp [StackProgram.step, loadEntry, hr, branch]
      · apply Exec.next (q' := 8) (r' := set r src [])
        · simp [StackProgram.step, loadEntry, branch]
        · exact .halt (by simp [StackProgram.step, loadEntry])
    | false =>
      apply Exec.next (q' := 5) (r' := set r src [])
      · simp [StackProgram.step, loadEntry, hr, branch]
      · apply Exec.next (q' := 8) (r' := set r src [])
        · simp [StackProgram.step, loadEntry, branch]
        · exact .halt (by simp [StackProgram.step, loadEntry])
  | false :: c :: rest, _, _, hx => by simp [readEntry] at hx
  | true :: d :: rest, r, hr, hx => by
    have hrest : readEntry rest = none := by
      cases h : readEntry rest with
      | none => rfl
      | some p =>
        obtain ⟨⟨c, ds⟩, tail⟩ := p
        simp [readEntry, h] at hx
    let r₁ := set r src (d :: rest)
    let r₂ := set r₁ src rest
    let r₃ := set r₂ D (d :: r₂ D)
    have h₁ : StackProgram.step (loadEntry src D C) 0 r = .inr (1, r₁) := by
      simp [StackProgram.step, loadEntry, hr, branch, r₁]
    have h₂ : StackProgram.step (loadEntry src D C) 1 r₁ =
        .inr ((if d then 3 else 2), r₂) := by
      cases d <;> simp [StackProgram.step, loadEntry, r₂, r₁, branch]
    have h₃ : StackProgram.step (loadEntry src D C) (if d then 3 else 2) r₂ =
        .inr (0, r₃) := by
      cases d <;> simp [StackProgram.step, loadEntry, r₃]
    obtain ⟨t, out, ht, he⟩ :=
      exec_loadEntry_malformed src D C hsD rest r₃ (by simp [r₃, r₂, r₁, hsD]) hrest
    exact ⟨t + 1 + 1 + 1, out, by simp; omega, Exec.next h₁ (Exec.next h₂ (Exec.next h₃ he))⟩

/-! ## Comparing an entry with a digit list -/

/-- Pop an entry from `src` and compare its digits with the list in `E` (destroying `E`).
If they agree, the entry's bit must equal the top bit of `C`. -/
def cmpEntry {k : Nat} (src E C : Fin (k + 1)) : Program k (Fin 14) where
  start := 0
  code := fun q =>
    if q = 0 then .pop src 13 6 1
    else if q = 1 then .pop src 13 2 3
    else if q = 2 then .pop E 4 0 4
    else if q = 3 then .pop E 4 4 0
    else if q = 4 then .pop src 13 7 5
    else if q = 5 then .pop src 13 4 4
    else if q = 6 then .peek E 8 7 7
    else if q = 7 then .pop src 13 12 12
    else if q = 8 then .pop src 13 9 10
    else if q = 9 then .peek C 13 12 13
    else if q = 10 then .peek C 13 13 12
    else if q = 12 then .halt true
    else .halt false

def cmpEntryEncoding : Encoding (Fin 14) := Encoding.fin 13

/-- Skip the rest of an entry. -/
def skipSpec : Word → Option Word
  | false :: _ :: rest => some rest
  | true :: _ :: rest => skipSpec rest
  | _ => none

/-- The source after comparing an entry with `e`, or `none` on a malformed entry or on an
agreeing entry whose bit differs from the top of `ci`. -/
def cmpSpec (ci : Word) : Word → Word → Option Word
  | false :: c :: rest, e =>
    if e.isEmpty then
      (match ci with
        | [] => none
        | b :: _ => if b == c then some rest else none)
    else some rest
  | true :: _ :: rest, [] => skipSpec rest
  | true :: d :: rest, b :: e => if b == d then cmpSpec ci rest e else skipSpec rest
  | _, _ => none

theorem skipSpec_pairs (ds : List Bool) (c : Bool) (rest : Word) :
    skipSpec (pairs ds ++ false :: c :: rest) = some rest := by
  induction ds with
  | nil => rfl
  | cons d ds ih => simpa [pairs, skipSpec] using ih

theorem cmpSpec_entry (b : Bool) (ciTail : Word) (c : Bool) (ds : List Bool) (rest : Word)
    (e : List Bool) :
    cmpSpec (b :: ciTail) (entryCode (c, ds) ++ rest) e =
      if ds = e ∧ b ≠ c then none else some rest := by
  induction ds generalizing e with
  | nil =>
    cases e with
    | nil => cases b <;> cases c <;> simp [entryCode, pairs, cmpSpec]
    | cons x e => simp [entryCode, pairs, cmpSpec]
  | cons d ds ih =>
    have hent : entryCode (c, d :: ds) ++ rest = true :: d :: (entryCode (c, ds) ++ rest) := by
      simp [entryCode, pairs]
    rw [hent]
    cases e with
    | nil =>
      simp only [cmpSpec, entryCode, List.append_assoc, List.cons_append, List.nil_append]
      simpa using skipSpec_pairs ds c rest
    | cons x e =>
      by_cases hx : x = d
      · subst hx
        simp only [cmpSpec, beq_self_eq_true, ite_true, ih, List.cons.injEq, true_and]
      · have hne : (x == d) = false := by simpa using hx
        simp only [cmpSpec, hne]
        have hs : skipSpec (entryCode (c, ds) ++ rest) = some rest := by
          simpa [entryCode, List.append_assoc] using skipSpec_pairs ds c rest
        rw [hs]
        simp [Ne.symm hx]

/-- A run of `cmpEntry` with the given specification: on success the source holds the
rest, and every register other than the source and `E` is unchanged. -/
def CmpResult {k : Nat} (spec : Option Word) (src E : Fin (k + 1)) (r : Registers k)
    (b : Bool) (out : Registers k) : Prop :=
  match spec with
  | none => b = false
  | some rest => b = true ∧ out src = rest ∧ (out E).length ≤ (r E).length ∧
      ∀ j, j ≠ src → j ≠ E → out j = r j

theorem exec_cmp_skip {k : Nat} (src E C : Fin (k + 1)) (hsE : src ≠ E) :
    ∀ (xs : Word) (r : Registers k), r src = xs →
      ∃ t b out, t ≤ 2 * xs.length + 4 ∧ Exec (cmpEntry src E C) 4 r t (b, out) ∧
        CmpResult (skipSpec xs) src E r b out
  | [], r, hr => by
    refine ⟨2, false, r, by simp, ?_, by simp [CmpResult, skipSpec]⟩
    have hset : set r src [] = r := by rw [← hr, set_unchanged]
    apply Exec.next (q' := 13) (r' := r)
    · simp [StackProgram.step, cmpEntry, hr, branch, hset]
    · exact .halt (by simp [StackProgram.step, cmpEntry])
  | [x], r, hr => by
    refine ⟨3, false, set r src [], by simp, ?_, by simp [CmpResult, skipSpec]⟩
    cases x with
    | false =>
      apply Exec.next (q' := 7) (r' := set r src [])
      · simp [StackProgram.step, cmpEntry, hr, branch]
      · apply Exec.next (q' := 13) (r' := set r src [])
        · simp [StackProgram.step, cmpEntry, branch]
        · exact .halt (by simp [StackProgram.step, cmpEntry])
    | true =>
      apply Exec.next (q' := 5) (r' := set r src [])
      · simp [StackProgram.step, cmpEntry, hr, branch]
      · apply Exec.next (q' := 13) (r' := set r src [])
        · simp [StackProgram.step, cmpEntry, branch]
        · exact .halt (by simp [StackProgram.step, cmpEntry])
  | false :: c :: rest, r, hr => by
    refine ⟨3, true, set r src rest, by simp, ?_, ?_⟩
    · apply Exec.next (q' := 7) (r' := set r src (c :: rest))
      · simp [StackProgram.step, cmpEntry, hr, branch]
      · apply Exec.next (q' := 12) (r' := set r src rest)
        · cases c <;> simp [StackProgram.step, cmpEntry, branch]
        · exact .halt (by simp [StackProgram.step, cmpEntry])
    · simp only [CmpResult, skipSpec, StackMachine.set_same, true_and]
      refine ⟨by simp [Ne.symm hsE], ?_⟩
      intro j hj _
      simp [hj]
  | true :: d :: rest, r, hr => by
    let r₂ := set r src rest
    obtain ⟨t, b, out, ht, he, hres⟩ := exec_cmp_skip src E C hsE rest r₂ (by simp [r₂])
    refine ⟨t + 2, b, out, by simp; omega, ?_, ?_⟩
    · apply Exec.next (q' := 5) (r' := set r src (d :: rest))
      · simp [StackProgram.step, cmpEntry, hr, branch]
      · apply Exec.next (q' := 4) (r' := r₂)
        · cases d <;> simp [StackProgram.step, cmpEntry, branch, r₂]
        · exact he
    · unfold CmpResult at hres ⊢
      simp only [skipSpec]
      cases hs : skipSpec rest with
      | none => simpa [hs] using hres
      | some tail =>
        simp only [hs] at hres
        refine ⟨hres.1, hres.2.1, ?_, ?_⟩
        · have := hres.2.2.1
          simpa [r₂, Ne.symm hsE] using this
        · intro j hj hE
          rw [hres.2.2.2 j hj hE]
          simp [r₂, hj]

theorem exec_cmpEntry {k : Nat} (src E C : Fin (k + 1)) (hsE : src ≠ E) (hsC : src ≠ C)
    (hEC : E ≠ C) :
    ∀ (xs : Word) (r : Registers k), r src = xs →
      ∃ t b out, t ≤ 3 * xs.length + 6 ∧ Exec (cmpEntry src E C) 0 r t (b, out) ∧
        CmpResult (cmpSpec (r C) xs (r E)) src E r b out
  | [], r, hr => by
    refine ⟨2, false, r, by simp, ?_, by simp [CmpResult, cmpSpec]⟩
    have hset : set r src [] = r := by rw [← hr, set_unchanged]
    apply Exec.next (q' := 13) (r' := r)
    · simp [StackProgram.step, cmpEntry, hr, branch, hset]
    · exact .halt (by simp [StackProgram.step, cmpEntry])
  | [false], r, hr => by
    refine ⟨4, false, set r src [], by simp, ?_, by simp [CmpResult, cmpSpec]⟩
    apply Exec.next (q' := 6) (r' := set r src [])
    · simp [StackProgram.step, cmpEntry, hr, branch]
    · cases he : r E with
      | nil =>
        apply Exec.next (q' := 8) (r' := set r src [])
        · simp [StackProgram.step, cmpEntry, branch, Ne.symm hsE, he]
        · apply Exec.next (q' := 13) (r' := set r src [])
          · simp [StackProgram.step, cmpEntry, branch]
          · exact .halt (by simp [StackProgram.step, cmpEntry])
      | cons x e =>
        apply Exec.next (q' := 7) (r' := set r src [])
        · cases x <;> simp [StackProgram.step, cmpEntry, branch, Ne.symm hsE, he]
        · apply Exec.next (q' := 13) (r' := set r src [])
          · simp [StackProgram.step, cmpEntry, branch]
          · exact .halt (by simp [StackProgram.step, cmpEntry])
  | [true], r, hr => by
    refine ⟨3, false, set r src [], by simp, ?_, by simp [CmpResult, cmpSpec]⟩
    apply Exec.next (q' := 1) (r' := set r src [])
    · simp [StackProgram.step, cmpEntry, hr, branch]
    · apply Exec.next (q' := 13) (r' := set r src [])
      · simp [StackProgram.step, cmpEntry, branch]
      · exact .halt (by simp [StackProgram.step, cmpEntry])
  | false :: c :: rest, r, hr => by
    cases he : r E with
    | cons x e =>
      refine ⟨4, true, set r src rest, by simp, ?_, ?_⟩
      · apply Exec.next (q' := 6) (r' := set r src (c :: rest))
        · simp [StackProgram.step, cmpEntry, hr, branch]
        · apply Exec.next (q' := 7) (r' := set r src (c :: rest))
          · cases x <;> simp [StackProgram.step, cmpEntry, branch, Ne.symm hsE, he]
          · apply Exec.next (q' := 12) (r' := set r src rest)
            · cases c <;> simp [StackProgram.step, cmpEntry, branch]
            · exact .halt (by simp [StackProgram.step, cmpEntry])
      · simp only [CmpResult, cmpSpec, List.isEmpty_cons, Bool.false_eq_true, ite_false,
          StackMachine.set_same, true_and]
        refine ⟨by simp [Ne.symm hsE], ?_⟩
        intro j hj _
        simp [hj]
    | nil =>
      have h₁ : StackProgram.step (cmpEntry src E C) 0 r = .inr (6, set r src (c :: rest)) := by
        simp [StackProgram.step, cmpEntry, hr, branch]
      have h₂ : StackProgram.step (cmpEntry src E C) 6 (set r src (c :: rest)) =
          .inr (8, set r src (c :: rest)) := by
        simp [StackProgram.step, cmpEntry, branch, Ne.symm hsE, he]
      have h₃ : StackProgram.step (cmpEntry src E C) 8 (set r src (c :: rest)) =
          .inr ((if c then 10 else 9), set r src rest) := by
        cases c <;> simp [StackProgram.step, cmpEntry, branch]
      cases hc : r C with
      | nil =>
        refine ⟨5, false, set r src rest, by simp, ?_, by simp [CmpResult, cmpSpec]⟩
        refine Exec.next h₁ (Exec.next h₂ (Exec.next h₃ (Exec.next (q' := 13)
          (r' := set r src rest) ?_ (.halt (by simp [StackProgram.step, cmpEntry])))))
        cases c <;> simp [StackProgram.step, cmpEntry, branch, Ne.symm hsC, hc]
      | cons y ys =>
        let q := if y == c then (12 : Fin 14) else 13
        have h₄ : StackProgram.step (cmpEntry src E C) (if c then 10 else 9) (set r src rest) =
            .inr (q, set r src rest) := by
          cases c <;> cases y <;> simp [StackProgram.step, cmpEntry, branch, Ne.symm hsC, hc, q]
        refine ⟨5, y == c, set r src rest, by simp, ?_, ?_⟩
        · refine Exec.next h₁ (Exec.next h₂ (Exec.next h₃ (Exec.next h₄ (.halt ?_))))
          cases y <;> cases c <;> simp [StackProgram.step, cmpEntry, q]
        · cases hyc : y == c
          · simp [CmpResult, cmpSpec, hyc]
          · simp only [CmpResult, cmpSpec, hyc, List.isEmpty_nil, ite_true,
              StackMachine.set_same, true_and]
            refine ⟨by simp [Ne.symm hsE], ?_⟩
            intro j hj _
            simp [hj]
  | true :: d :: rest, r, hr => by
    let r₁ := set r src (d :: rest)
    let r₂ := set r₁ src rest
    have h₁ : StackProgram.step (cmpEntry src E C) 0 r = .inr (1, r₁) := by
      simp [StackProgram.step, cmpEntry, hr, branch, r₁]
    have h₂ : StackProgram.step (cmpEntry src E C) 1 r₁ = .inr ((if d then 3 else 2), r₂) := by
      cases d <;> simp [StackProgram.step, cmpEntry, branch, r₂, r₁]
    have hE₂ : r₂ E = r E := by simp [r₂, r₁, Ne.symm hsE]
    have hC₂ : r₂ C = r C := by simp [r₂, r₁, Ne.symm hsC]
    cases he : r E with
    | nil =>
      have h₃ : StackProgram.step (cmpEntry src E C) (if d then 3 else 2) r₂ = .inr (4, r₂) := by
        have hset : set r₂ E [] = r₂ := by rw [← he, ← hE₂, set_unchanged]
        cases d <;> simp [StackProgram.step, cmpEntry, branch, hE₂, he, hset]
      obtain ⟨t, b, out, ht, hex, hres⟩ := exec_cmp_skip src E C hsE rest r₂ (by simp [r₂, r₁])
      refine ⟨t + 3, b, out, by simp; omega, Exec.next h₁ (Exec.next h₂ (Exec.next h₃ hex)), ?_⟩
      unfold CmpResult at hres ⊢
      simp only [cmpSpec]
      cases hs : skipSpec rest with
      | none => simpa [hs] using hres
      | some tail =>
        simp only [hs] at hres
        refine ⟨hres.1, hres.2.1, ?_, ?_⟩
        · have := hres.2.2.1
          rw [hE₂] at this
          exact this
        · intro j hj hjE
          rw [hres.2.2.2 j hj hjE]
          simp [r₂, r₁, hj]
    | cons x e =>
      let r₃ := set r₂ E e
      have hE₃ : r₃ E = e := by simp [r₃]
      have hC₃ : r₃ C = r C := by simp [r₃, hEC.symm, hC₂]
      by_cases hxd : x = d
      · subst hxd
        have h₃ : StackProgram.step (cmpEntry src E C) (if x then 3 else 2) r₂ =
            .inr (0, r₃) := by
          cases x <;> simp [StackProgram.step, cmpEntry, branch, hE₂, he, r₃]
        obtain ⟨t, b, out, ht, hex, hres⟩ :=
          exec_cmpEntry src E C hsE hsC hEC rest r₃ (by simp [r₃, r₂, r₁, hsE])
        refine ⟨t + 3, b, out, by simp; omega, Exec.next h₁ (Exec.next h₂ (Exec.next h₃ hex)), ?_⟩
        rw [hE₃, hC₃] at hres
        unfold CmpResult at hres ⊢
        simp only [cmpSpec, beq_self_eq_true, ite_true]
        cases hs : cmpSpec (r C) rest e with
        | none => simpa [hs] using hres
        | some tail =>
          simp only [hs] at hres
          refine ⟨hres.1, hres.2.1, ?_, ?_⟩
          · have := hres.2.2.1
            rw [he]
            simp only [r₃, StackMachine.set_same] at this
            simp only [List.length_cons]
            omega
          · intro j hj hjE
            rw [hres.2.2.2 j hj hjE]
            simp [r₃, r₂, r₁, hj, hjE]
      · have h₃ : StackProgram.step (cmpEntry src E C) (if d then 3 else 2) r₂ =
            .inr (4, r₃) := by
          cases d <;> cases x
          all_goals first
            | exact absurd rfl hxd
            | simp [StackProgram.step, cmpEntry, branch, hE₂, he, r₃]
        obtain ⟨t, b, out, ht, hex, hres⟩ := exec_cmp_skip src E C hsE rest r₃
          (by simp [r₃, r₂, r₁, hsE])
        refine ⟨t + 3, b, out, by simp; omega, Exec.next h₁ (Exec.next h₂ (Exec.next h₃ hex)), ?_⟩
        unfold CmpResult at hres ⊢
        have hne : (x == d) = false := by simpa using hxd
        simp only [cmpSpec, hne]
        cases hs : skipSpec rest with
        | none => simpa [hs] using hres
        | some tail =>
          simp only [hs] at hres
          refine ⟨hres.1, hres.2.1, ?_, ?_⟩
          · have := hres.2.2.1
            rw [he]
            simp only [r₃, StackMachine.set_same] at this
            simp only [List.length_cons]
            omega
          · intro j hj hjE
            rw [hres.2.2.2 j hj hjE]
            simp [r₃, r₂, r₁, hj, hjE]

end Complexity.Binary
