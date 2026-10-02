module

public import Complexity.Binary.VerifierPrograms
public import Complexity.PolynomialBound
import Lean.Elab.Tactic.Omega

/-!
# The first phase of the binary SAT verifier

The first phase parses the input as a binary-indexed formula. For every literal occurrence
it pops the next certificate bit `c`, records whether `c` agrees with the sign, and pushes
the entry `(c, norm digits)` onto the `entries` register (and a `true` onto `count`). After
each clause it requires some occurrence to agree with its sign. This file gives the
programs, their partial register semantics and their instruction counts.
-/

@[expose] public section

namespace Complexity.Binary.Verify

open Complexity.StackMachine (Registers set branch)
open Complexity.StackProgram Complexity.StackWords Complexity.StackParse
open Complexity.SAT
open Complexity.Binary

abbrev Reg := Fin 18
abbrev input : Reg := 0
abbrev cert : Reg := 1
abbrev outer : Reg := 2
abbrev inner : Reg := 3
abbrev len : Reg := 4
abbrev temp : Reg := 5
abbrev flag : Reg := 6
abbrev entries : Reg := 7
abbrev count : Reg := 8
abbrev list₁ : Reg := 9
abbrev list₂ : Reg := 10
abbrev count₁ : Reg := 11
abbrev count₂ : Reg := 12
abbrev digitsRev : Reg := 13
abbrev digits : Reg := 14
abbrev digitsCmp : Reg := 15
abbrev bit : Reg := 16
abbrev scratch : Reg := 17

attribute [simp] input cert outer inner len temp flag entries count list₁ list₂ count₁ count₂
  digitsRev digits digitsCmp bit scratch

theorem regs_ext {r s : Registers 17} (h0 : r 0 = s 0) (h1 : r 1 = s 1) (h2 : r 2 = s 2)
    (h3 : r 3 = s 3) (h4 : r 4 = s 4) (h5 : r 5 = s 5) (h6 : r 6 = s 6) (h7 : r 7 = s 7)
    (h8 : r 8 = s 8) (h9 : r 9 = s 9) (h10 : r 10 = s 10) (h11 : r 11 = s 11)
    (h12 : r 12 = s 12) (h13 : r 13 = s 13) (h14 : r 14 = s 14) (h15 : r 15 = s 15)
    (h16 : r 16 = s 16) (h17 : r 17 = s 17) : r = s := by
  funext a
  obtain ⟨n, hn⟩ := a
  match n, hn with
  | 0, _ => exact h0
  | 1, _ => exact h1
  | 2, _ => exact h2
  | 3, _ => exact h3
  | 4, _ => exact h4
  | 5, _ => exact h5
  | 6, _ => exact h6
  | 7, _ => exact h7
  | 8, _ => exact h8
  | 9, _ => exact h9
  | 10, _ => exact h10
  | 11, _ => exact h11
  | 12, _ => exact h12
  | 13, _ => exact h13
  | 14, _ => exact h14
  | 15, _ => exact h15
  | 16, _ => exact h16
  | 17, _ => exact h17
  | n + 18, h => omega

/-! ## Parsing helpers -/

theorem length_norm_le (bs : List Bool) : (norm bs).length ≤ bs.length := by
  induction bs with
  | nil => simp [norm]
  | cons b bs ih =>
    simp only [norm]
    split <;> simp <;> omega

theorem readMany_readBit (n : Nat) (y : Word) :
    readMany readBit n y = if n ≤ y.length then some (y.take n, y.drop n) else none := by
  induction n generalizing y with
  | zero => simp [readMany]
  | succ n ih =>
    cases y with
    | nil => simp [readMany, readBit]
    | cons b y =>
      simp only [readMany, readBit, ih, List.length_cons]
      by_cases h : n ≤ y.length
      · simp [h]
      · have h' : ¬ n + 1 ≤ y.length + 1 := by omega
        simp [h, h']

/-! ## One literal occurrence -/

/-- Pop the sign and the next certificate bit `c`; push `c` and the entry terminator onto
`entries`, and a `true` onto `flag` if `c` agrees with the sign. -/
def litHead : Program 17 (Fin 12) where
  start := 0
  code := fun q =>
    if q = 0 then .pop input 9 1 2
    else if q = 1 then .pop cert 9 3 4
    else if q = 2 then .pop cert 9 5 6
    else if q = 3 then .push entries false 7
    else if q = 4 then .push entries true 8
    else if q = 5 then .push entries false 8
    else if q = 6 then .push entries true 7
    else if q = 7 then .push entries false 10
    else if q = 8 then .push entries false 11
    else if q = 9 then .halt false
    else if q = 10 then .push flag true 11
    else .halt true

def litHeadEncoding : Encoding (Fin 12) := Encoding.fin 11

def headFinish (r : Registers 17) (s c : Bool) (x w : Word) : Registers 17 :=
  set (set (set (set r input x) cert w) entries (false :: c :: r entries)) flag
    (if c == s then true :: r flag else r flag)

theorem exec_litHead (r : Registers 17) (s c : Bool) (x w : Word) (hi : r input = s :: x)
    (hc : r cert = c :: w) :
    Exec litHead 0 r (if c == s then 6 else 5) (true, headFinish r s c x w) := by
  let r₁ := set r input x
  let r₂ := set r₁ cert w
  let r₃ := set r₂ entries (c :: r₂ entries)
  let r₄ := set r₃ entries (false :: r₃ entries)
  let q₁ : Fin 12 := if s then 2 else 1
  let q₂ : Fin 12 := if s then (if c then 6 else 5) else (if c then 4 else 3)
  let q₃ : Fin 12 := if c == s then 7 else 8
  have h₁ : StackProgram.step litHead 0 r = .inr (q₁, r₁) := by
    cases s <;> simp [StackProgram.step, litHead, hi, branch, q₁, r₁]
  have h₂ : StackProgram.step litHead q₁ r₁ = .inr (q₂, r₂) := by
    cases s <;> cases c <;> simp [StackProgram.step, litHead, hc, branch, q₁, q₂, r₂, r₁]
  have h₃ : StackProgram.step litHead q₂ r₂ = .inr (q₃, r₃) := by
    cases s <;> cases c <;> simp [StackProgram.step, litHead, q₂, q₃, r₃]
  cases hcs : c == s with
  | true =>
    have h₄ : StackProgram.step litHead q₃ r₃ = .inr (10, r₄) := by
      simp [StackProgram.step, litHead, q₃, hcs, r₄]
    have h₅ : StackProgram.step litHead 10 r₄ = .inr (11, set r₄ flag (true :: r₄ flag)) := by
      simp [StackProgram.step, litHead]
    have hh := Exec.next h₁ (Exec.next h₂ (Exec.next h₃ (Exec.next h₄ (Exec.next h₅
      (Exec.halt (result := (true, set r₄ flag (true :: r₄ flag)))
        (by simp [StackProgram.step, litHead]))))))
    have hout : set r₄ flag (true :: r₄ flag) = headFinish r s c x w := by
      apply regs_ext <;> simp [r₄, r₃, r₂, r₁, headFinish, hcs]
    rw [hout] at hh
    exact hh
  | false =>
    have h₄ : StackProgram.step litHead q₃ r₃ = .inr (11, r₄) := by
      simp [StackProgram.step, litHead, q₃, hcs, r₄]
    have hh := Exec.next h₁ (Exec.next h₂ (Exec.next h₃ (Exec.next h₄
      (Exec.halt (result := (true, r₄)) (by simp [StackProgram.step, litHead])))))
    have hout : r₄ = headFinish r s c x w := by
      apply regs_ext <;> simp [r₄, r₃, r₂, r₁, headFinish, hcs]
    rw [hout] at hh
    exact hh

theorem exec_litHead_noInput (r : Registers 17) (hi : r input = []) :
    Exec litHead 0 r 2 (false, r) := by
  have hset : set r input [] = r := by rw [← hi, set_unchanged]
  apply Exec.next (q' := 9) (r' := r)
  · simp [StackProgram.step, litHead, hi, branch, hset]
  · exact .halt (by simp [StackProgram.step, litHead])

theorem exec_litHead_noCert (r : Registers 17) (s : Bool) (x : Word) (hi : r input = s :: x)
    (hc : r cert = []) : Exec litHead 0 r 3 (false, set r input x) := by
  have hset : set (set r input x) cert [] = set r input x := by
    have : (set r input x) cert = [] := by simpa using hc
    rw [← this, set_unchanged]
  apply Exec.next (q' := if s then 2 else 1) (r' := set r input x)
  · cases s <;> simp [StackProgram.step, litHead, hi, branch]
  · apply Exec.next (q' := 9) (r' := set r input x)
    · cases s <;> simp [StackProgram.step, litHead, branch, hc, hset]
    · exact .halt (by simp [StackProgram.step, litHead])

/-- Read one literal occurrence and record its entry. -/
def literal :=
  seq litHead (seq (readUnary input len) (seq (takeBits len input temp)
    (seq (stripZeros temp) (seq (emitPairs temp entries) (push count true)))))

def literalEncoding :=
  litHeadEncoding.sum (readUnaryEncoding.sum (takeBitsEncoding.sum (stripZerosEncoding.sum
    (emitPairsEncoding.sum Encoding.bool))))

/-- The work registers of a literal are empty. -/
structure Clean (r : Registers 17) : Prop where
  len_eq : r 4 = []
  temp_eq : r 5 = []

theorem Clean.set {r : Registers 17} (h : Clean r) (j : Reg) (hl : j ≠ len) (ht : j ≠ temp)
    (xs : Word) : Clean (StackMachine.set r j xs) := by
  constructor
  · simpa [Ne.symm hl] using h.len_eq
  · simpa [Ne.symm ht] using h.temp_eq

def litFinish (r : Registers 17) (l : BinaryLiteral) (c : Bool) (rest w : Word) :
    Registers 17 :=
  set (set (set (set (set r input rest) cert w) entries (entryCode (c, norm l.bits) ++ r entries))
    count (true :: r count)) flag (if c == l.positive then true :: r flag else r flag)

/-- The partial register semantics of `literal`. -/
def litStep (r : Registers 17) : Option (Registers 17) :=
  match readBinaryLiteral (r input), r cert with
  | some (l, rest), c :: w => some (litFinish r l c rest w)
  | _, _ => none

def litCost (bound : Nat) : Nat := 11 * bound + 18

theorem literal_success (r : Registers 17) (hc : Clean r) (l : BinaryLiteral) (rest : Word)
    (c : Bool) (w : Word) (hi : r input = encodeBinaryLiteral l ++ rest)
    (hw : r cert = c :: w) :
    ∃ t, t ≤ 11 * l.bits.length + 18 ∧
      Exec literal literal.start r t (true, litFinish r l c rest w) := by
  obtain ⟨bits, s⟩ := l
  let L := bits.length
  have hi' : r input = s :: (writeNat L ++ (bits ++ rest)) := by
    rw [hi]; simp [encodeBinaryLiteral, writeList, writeValues_single, List.append_assoc, L]
  have h₁ := exec_litHead r s c (writeNat L ++ (bits ++ rest)) w hi' hw
  let r₁ := headFinish r s c (writeNat L ++ (bits ++ rest)) w
  have h₂ := exec_readUnary_encoded input len (by decide) L (bits ++ rest) r₁ (by simp [r₁, headFinish])
  let r₂ := set (set r₁ input (bits ++ rest)) len (List.replicate L true)
  have h₃ := exec_takeBits len input temp (by decide) (by decide) (by decide) bits rest r₂
    (by simp [r₂]) (by simp [r₂, L])
  let r₃ := set (set (set r₂ input rest) len []) temp (bits.reverse ++ r₂ temp)
  obtain ⟨t₄, ht₄, h₄⟩ := exec_stripZeros temp r₃
  let r₄ := set r₃ temp ((r₃ temp).dropWhile (fun b => !b))
  have h₅ := exec_emitPairs temp entries (by decide) r₄
  let r₅ := set (set r₄ temp []) entries (pairs (r₄ temp).reverse ++ r₄ entries)
  have h₆ := exec_push count true r₅
  have he := exec_seq _ _ h₁ (exec_seq _ _ h₂ (exec_seq _ _ h₃ (exec_seq _ _ h₄
    (exec_seq _ _ h₅ h₆))))
  have htemp₃ : r₃ temp = bits.reverse := by
    simp [r₃, r₂, r₁, headFinish, hc.temp_eq]
  have htemp₄ : r₄ temp = (bits.reverse.dropWhile (fun b => !b)) := by
    simp [r₄, htemp₃]
  have hrev : (r₄ temp).reverse = norm bits := by
    rw [htemp₄, reverse_dropWhile_reverse]
  have hout : set r₅ count (true :: r₅ count) = litFinish r ⟨bits, s⟩ c rest w := by
    apply regs_ext <;>
      simp [r₅, litFinish, entryCode, headFinish, r₄, r₃, r₂, r₁, hc.len_eq,
        hc.temp_eq, List.append_assoc, reverse_dropWhile_reverse]
  rw [hout] at he
  refine ⟨_, ?_, he⟩
  have hlen₁ : (r₁ len).length = 0 := by simp [r₁, headFinish, hc.len_eq]
  have hlen₄ : (r₄ temp).length ≤ L := by
    rw [htemp₄]
    have := (List.dropWhile_sublist (l := bits.reverse) (fun b => !b)).length_le
    simpa [L] using this
  have hlen₃ : (r₃ temp).length = L := by simp [htemp₃, L]
  rw [hlen₃] at ht₄
  rw [hlen₁]
  cases c == s <;> simp only [Bool.false_eq_true, ite_false, ite_true] <;> omega


@[simp] theorem encodeBinaryLiteral_length (l : BinaryLiteral) :
    (encodeBinaryLiteral l).length = 2 * l.bits.length + 2 := by
  simp [encodeBinaryLiteral, writeList, writeValues_single, SATBounds.writeNat_length]
  omega

@[simp] theorem entryCode_length (e : Bool × List Bool) :
    (entryCode e).length = 2 * e.2.length + 2 := by
  simp [entryCode]

theorem literal_runs (bound : Nat) (r : Registers 17) (hc : Clean r)
    (hb : (r input).length ≤ bound) :
    ∃ t b out, t ≤ litCost bound ∧ Exec literal literal.start r t (b, out) ∧
      Realizes (litStep r) b out := by
  cases hl : readBinaryLiteral (r input) with
  | some pair =>
    obtain ⟨l, rest⟩ := pair
    have hi := readBinaryLiteral_eq_some hl
    have hlen := congrArg List.length hi
    simp only [List.length_append, encodeBinaryLiteral_length] at hlen
    cases hw : r cert with
    | nil =>
      have hi' : r input = l.positive :: (writeList (fun b => [b]) l.bits ++ rest) := by
        rw [hi]; rfl
      have he := exec_seq_failure _ (seq (readUnary input len) (seq (takeBits len input temp)
        (seq (stripZeros temp) (seq (emitPairs temp entries) (push count true)))))
        (exec_litHead_noCert r _ _ hi' hw)
      refine ⟨3, false, _, by unfold litCost; omega, he, by simp [litStep, hl, hw]⟩
    | cons c w =>
      obtain ⟨t, ht, he⟩ := literal_success r hc l rest c w hi hw
      refine ⟨t, true, _, by unfold litCost; omega, he, by simp [litStep, hl, hw]⟩
  | none =>
    have hstep : litStep r = none := by simp [litStep, hl]
    rw [hstep]
    cases hi : r input with
    | nil =>
      have he := exec_seq_failure _ (seq (readUnary input len) (seq (takeBits len input temp)
        (seq (stripZeros temp) (seq (emitPairs temp entries) (push count true)))))
        (exec_litHead_noInput r hi)
      exact ⟨2, false, _, by unfold litCost; omega, he, rfl⟩
    | cons s x =>
      have hx : x.length < bound := by rw [hi] at hb; simp at hb; omega
      cases hw : r cert with
      | nil =>
        have he := exec_seq_failure _ (seq (readUnary input len) (seq (takeBits len input temp)
          (seq (stripZeros temp) (seq (emitPairs temp entries) (push count true)))))
          (exec_litHead_noCert r s x hi hw)
        exact ⟨3, false, _, by unfold litCost; omega, he, rfl⟩
      | cons c w =>
        have h₁ := exec_litHead r s c x w hi hw
        let r₁ := headFinish r s c x w
        have hlen₁ : (r₁ len).length = 0 := by simp [r₁, headFinish, hc.len_eq]
        have hcost₁ : (if c == s then 6 else 5) ≤ 6 := by split <;> omega
        cases hn : readNat x with
        | none =>
          have hu := exec_readUnary_malformed input len (by decide) x.length r₁
            (by simpa [r₁, headFinish] using readNat_none_eq hn)
          have he := exec_seq _ _ h₁ (exec_seq_failure _ (seq (takeBits len input temp)
            (seq (stripZeros temp) (seq (emitPairs temp entries) (push count true)))) hu)
          refine ⟨_, false, _, ?_, he, rfl⟩
          rw [hlen₁]
          unfold litCost
          omega
        | some pair =>
          obtain ⟨L, y⟩ := pair
          have hxy := readNat_eq_some hn
          have hlenx := congrArg List.length hxy
          simp only [List.length_append, SATBounds.writeNat_length] at hlenx
          have hshort : y.length < L := by
            by_cases hle : L ≤ y.length
            · have hm : readMany readBit L y = some (y.take L, y.drop L) := by
                simp [readMany_readBit, hle]
              have : readBinaryLiteral (r input) ≠ none := by
                simp [hi, readBinaryLiteral, readList, hn, hm]
              exact absurd hl this
            · omega
          have h₂ := exec_readUnary_encoded input len (by decide) L y r₁
            (by simpa [r₁, headFinish] using hxy)
          let r₂ := set (set r₁ input y) len (List.replicate L true)
          obtain ⟨out, h₃⟩ := exec_takeBits_short len input temp (by decide) (by decide)
            (by decide) y L r₂ (by simp [r₂]) (by simp [r₂]) hshort
          have he := exec_seq _ _ h₁ (exec_seq _ _ h₂ (exec_seq_failure _
            (seq (stripZeros temp) (seq (emitPairs temp entries) (push count true))) h₃))
          refine ⟨_, false, _, ?_, he, rfl⟩
          rw [hlen₁]
          unfold litCost
          omega

/-! ## The literal loop -/

/-- Invariant of the literal loop. Every literal consumes at least as many input bits as it
adds to `flag`, `entries` and `count`. -/
structure LitInv (bound : Nat) (o : Word) (q : Registers 17) : Prop where
  clean : Clean q
  flag_le : (q input).length + (q flag).length ≤ bound
  entries_le : (q input).length + (q entries).length ≤ bound
  count_le : (q input).length + (q count).length ≤ bound
  outer_eq : q outer = o

theorem LitInv.set_inner {bound : Nat} {o : Word} {q : Registers 17} (h : LitInv bound o q)
    (xs : Word) : LitInv bound o (set q inner xs) := by
  constructor
  · exact h.clean.set inner (by decide) (by decide) xs
  · simpa using h.flag_le
  · simpa using h.entries_le
  · simpa using h.count_le
  · simpa using h.outer_eq

theorem LitInv.step {bound : Nat} {o : Word} {q out : Registers 17} (h : LitInv bound o q)
    (hs : litStep q = some out) : LitInv bound o out ∧ out inner = q inner := by
  unfold litStep at hs
  cases hl : readBinaryLiteral (q input) with
  | none => simp [hl] at hs
  | some pair =>
    obtain ⟨l, rest⟩ := pair
    cases hw : q cert with
    | nil => simp [hl, hw] at hs
    | cons c w =>
      simp only [hl, hw, Option.some.injEq] at hs
      subst hs
      have hlen := congrArg List.length (readBinaryLiteral_eq_some hl)
      simp only [List.length_append, encodeBinaryLiteral_length] at hlen
      have hnorm := length_norm_le l.bits
      have h₁ := h.flag_le
      have h₂ := h.entries_le
      have h₃ := h.count_le
      have hflag : (if c == l.positive then true :: q flag else q flag).length ≤
          (q flag).length + 1 := by split <;> simp
      refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
      · exact ((((h.clean.set input (by decide) (by decide) _).set cert (by decide) (by decide)
          _).set entries (by decide) (by decide) _).set count (by decide) (by decide) _).set
          flag (by decide) (by decide) _
      · simp only [litFinish, StackMachine.set_same,
          StackMachine.set_other _ (by decide : input ≠ flag),
          StackMachine.set_other _ (by decide : input ≠ count),
          StackMachine.set_other _ (by decide : input ≠ entries),
          StackMachine.set_other _ (by decide : input ≠ cert)]
        simp only [input, flag] at h₁ hlen hflag ⊢
        omega
      · simp [litFinish] at h₂ hlen ⊢
        omega
      · simp [litFinish] at h₃ hlen ⊢
        omega
      · simpa [litFinish] using h.outer_eq
      · simp [litFinish]

theorem literals_runs (bound : Nat) (o : Word) (m : Nat) (r : Registers 17)
    (hI : LitInv bound o r) (hr : r inner = List.replicate m true) :
    ∃ t b out, t ≤ m * (litCost bound + 1) + 2 ∧
      Exec (whileCounter inner literal) (.inl false) r t (b, out) ∧
      Realizes (iterStep inner litStep m r) b out :=
  whileCounter_iter literal inner litStep (LitInv bound o) (litCost bound)
    (fun _ tail hq _ => hq.set_inner tail)
    (fun q hq => literal_runs bound q hq.clean (by have := hq.flag_le; omega))
    (fun _ _ hq hs => hq.step hs) m r hr hI

theorem literals_invariant (bound : Nat) (o : Word) (m : Nat) (r : Registers 17)
    (hI : LitInv bound o r) (hr : r inner = List.replicate m true) (out : Registers 17)
    (h : iterStep inner litStep m r = some out) : LitInv bound o out ∧ out inner = [] :=
  iterStep_invariant inner litStep (LitInv bound o) (fun _ tail hq _ => hq.set_inner tail)
    (fun _ _ hq hs => hq.step hs) m r hr hI out h

/-! ## One clause -/

/-- Read a literal count, record all literals, require an agreeing occurrence. -/
def clauseProg :=
  seq (readUnary input inner) (seq (whileCounter inner literal)
    (seq (testEmpty flag false true) (clear flag)))

def clauseEncoding :=
  readUnaryEncoding.sum ((Encoding.bool.sum literalEncoding).sum
    ((Encoding.fin 2).sum Encoding.bool))

/-- The partial register semantics of `clauseProg`. -/
def clauseStep (r : Registers 17) : Option (Registers 17) :=
  match readNat (r input) with
  | none => none
  | some (m, rest) =>
    match iterStep inner litStep m (set (set r input rest) inner (List.replicate m true)) with
    | none => none
    | some q => if (q flag).isEmpty then none else some (set q flag [])

def clauseCost (bound : Nat) : Nat := bound * (litCost bound + 1) + 4 * bound + 10

/-- Invariant of the clause loop. -/
structure ClauseInv (bound : Nat) (q : Registers 17) : Prop where
  clean : Clean q
  flag_eq : q flag = []
  entries_le : (q input).length + (q entries).length ≤ bound
  count_le : (q input).length + (q count).length ≤ bound
  inner_le : (q inner).length ≤ bound

theorem ClauseInv.literals {bound : Nat} {q : Registers 17} (h : ClauseInv bound q) (m : Nat)
    (rest : Word) (hrest : rest.length ≤ (q input).length) :
    LitInv bound (q outer) (set (set q input rest) inner (List.replicate m true)) := by
  have h₁ := h.entries_le
  have h₂ := h.count_le
  constructor
  · exact (h.clean.set input (by decide) (by decide) _).set inner (by decide) (by decide) _
  · simp [h.flag_eq]; omega
  · simp only [input, entries] at h₁ hrest ⊢; simp; omega
  · simp only [input, count] at h₂ hrest ⊢; simp; omega
  · simp

theorem clause_runs (bound : Nat) (r : Registers 17) (hI : ClauseInv bound r) :
    ∃ t b out, t ≤ clauseCost bound ∧ Exec clauseProg clauseProg.start r t (b, out) ∧
      Realizes (clauseStep r) b out := by
  have hb : (r input).length ≤ bound := by have := hI.entries_le; omega
  have hi := hI.inner_le
  cases hp : readNat (r input) with
  | none =>
    have he := exec_readUnary_malformed input inner (by decide) (r input).length r
      (readNat_none_eq hp)
    have hf := exec_seq_failure _ (seq (whileCounter inner literal)
      (seq (testEmpty flag false true) (clear flag))) he
    refine ⟨_, false, _, ?_, hf, by simp [clauseStep, hp]⟩
    unfold clauseCost
    omega
  | some pair =>
    obtain ⟨m, rest⟩ := pair
    have hlen := congrArg List.length (readNat_eq_some hp)
    simp only [List.length_append, SATBounds.writeNat_length] at hlen
    have hm : m ≤ bound := by omega
    have hread := exec_readUnary_encoded input inner (by decide) m rest r (readNat_eq_some hp)
    let r₁ := set (set r input rest) inner (List.replicate m true)
    have hI₁ : LitInv bound (r outer) r₁ := hI.literals m rest (by omega)
    obtain ⟨t, b, mid, ht, he, hspec⟩ := literals_runs bound (r outer) m r₁ hI₁ (by simp [r₁])
    have hloopCost : m * (litCost bound + 1) ≤ bound * (litCost bound + 1) :=
      Nat.mul_le_mul_right _ hm
    cases hex : iterStep inner litStep m r₁ with
    | none =>
      have hfalse : b = false := by simpa [hex] using hspec
      subst b
      have hfull := exec_seq _ _ hread (exec_seq_failure _ (seq (testEmpty flag false true)
        (clear flag)) he)
      refine ⟨_, false, mid, ?_, hfull, by simp [clauseStep, hp, r₁, hex]⟩
      unfold clauseCost
      omega
    | some q =>
      have hs : b = true ∧ mid = q := by simpa [hex] using hspec
      obtain ⟨rfl, rfl⟩ := hs
      obtain ⟨hIq, _⟩ := literals_invariant bound (r outer) m r₁ hI₁ (by simp [r₁]) mid hex
      have hex' : iterStep inner litStep m (set (set r input rest) inner
          (List.replicate m true)) = some mid := hex
      have htest := exec_testEmpty flag false true mid
      have hflagle : (mid flag).length ≤ bound := by have := hIq.flag_le; omega
      cases hfe : (mid flag).isEmpty with
      | true =>
        have htest' : Exec (testEmpty flag false true) (testEmpty flag false true).start mid 2
            (false, mid) := by simpa [hfe] using htest
        have hfull := exec_seq _ _ hread (exec_seq _ _ he (exec_seq_failure _ (clear flag) htest'))
        refine ⟨_, false, mid, ?_, hfull, by simp [clauseStep, hp, hex', hfe]⟩
        unfold clauseCost
        omega
      | false =>
        have htest' : Exec (testEmpty flag false true) (testEmpty flag false true).start mid 2
            (true, mid) := by simpa [hfe] using htest
        have hfull := exec_seq _ _ hread (exec_seq _ _ he (exec_seq _ _ htest'
          (exec_clear flag mid)))
        refine ⟨_, true, _, ?_, hfull, by simp [clauseStep, hp, hex', hfe]⟩
        unfold clauseCost
        omega

theorem ClauseInv.set_outer {bound : Nat} {q : Registers 17} (h : ClauseInv bound q)
    (xs : Word) : ClauseInv bound (set q outer xs) := by
  constructor
  · exact h.clean.set outer (by decide) (by decide) xs
  · simpa using h.flag_eq
  · simpa using h.entries_le
  · simpa using h.count_le
  · simpa using h.inner_le

theorem ClauseInv.step {bound : Nat} {q out : Registers 17} (h : ClauseInv bound q)
    (hs : clauseStep q = some out) : ClauseInv bound out ∧ out outer = q outer := by
  unfold clauseStep at hs
  cases hp : readNat (q input) with
  | none => simp [hp] at hs
  | some pair =>
    obtain ⟨m, rest⟩ := pair
    simp only [hp] at hs
    have hlen := congrArg List.length (readNat_eq_some hp)
    simp only [List.length_append, SATBounds.writeNat_length] at hlen
    let r₁ := set (set q input rest) inner (List.replicate m true)
    have hI₁ : LitInv bound (q outer) r₁ := h.literals m rest (by omega)
    cases hex : iterStep inner litStep m r₁ with
    | none =>
      have hex' : iterStep inner litStep m (set (set q input rest) inner
          (List.replicate m true)) = none := hex
      simp [hex'] at hs
    | some mid =>
      have hex' : iterStep inner litStep m (set (set q input rest) inner
          (List.replicate m true)) = some mid := hex
      obtain ⟨hIm, hinner⟩ := literals_invariant _ _ m r₁ hI₁ (by simp [r₁]) mid hex
      simp only [hex'] at hs
      cases hfe : (mid flag).isEmpty with
      | true => simp [hfe] at hs
      | false =>
        simp only [hfe, Bool.false_eq_true, ite_false, Option.some.injEq] at hs
        subst hs
        have h₁ := hIm.entries_le
        have h₂ := hIm.count_le
        have h₃ := hIm.flag_le
        refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
        · exact hIm.clean.set flag (by decide) (by decide) _
        · simp
        · simpa using h₁
        · simpa using h₂
        · simp [hinner]
        · simpa using hIm.outer_eq

theorem clauses_runs (bound n : Nat) (r : Registers 17) (hI : ClauseInv bound r)
    (hr : r outer = List.replicate n true) :
    ∃ t b out, t ≤ n * (clauseCost bound + 1) + 2 ∧
      Exec (whileCounter outer clauseProg) (.inl false) r t (b, out) ∧
      Realizes (iterStep outer clauseStep n r) b out :=
  whileCounter_iter clauseProg outer clauseStep (ClauseInv bound) (clauseCost bound)
    (fun _ tail hq _ => hq.set_outer tail) (fun q hq => clause_runs bound q hq)
    (fun _ _ hq hs => hq.step hs) n r hr hI

theorem clauses_invariant (bound n : Nat) (r : Registers 17) (hI : ClauseInv bound r)
    (hr : r outer = List.replicate n true) (out : Registers 17)
    (h : iterStep outer clauseStep n r = some out) : ClauseInv bound out ∧ out outer = [] :=
  iterStep_invariant outer clauseStep (ClauseInv bound) (fun _ tail hq _ => hq.set_outer tail)
    (fun _ _ hq hs => hq.step hs) n r hr hI out h

/-! ## The formula -/

/-- Read the clause count, check all clauses, and require the input to be used up. -/
def parse :=
  seq (readUnary input outer) (seq (whileCounter outer clauseProg) (testEmpty input true false))

def parseEncoding :=
  readUnaryEncoding.sum ((Encoding.bool.sum clauseEncoding).sum (Encoding.fin 2))

/-- The partial register semantics of `parse`. -/
def parseStep (r : Registers 17) : Option (Registers 17) :=
  match readNat (r input) with
  | none => none
  | some (n, rest) =>
    match iterStep outer clauseStep n (set (set r input rest) outer (List.replicate n true)) with
    | none => none
    | some q => if (q input).isEmpty then some q else none

def parseCost (bound : Nat) : Nat := bound * (clauseCost bound + 1) + 3 * bound + 8

theorem parse_runs (bound : Nat) (r : Registers 17) (hI : ClauseInv bound r)
    (ho : (r outer).length ≤ bound) :
    ∃ t b out, t ≤ parseCost bound ∧ Exec parse parse.start r t (b, out) ∧
      Realizes (parseStep r) b out := by
  have hb : (r input).length ≤ bound := by have := hI.entries_le; omega
  cases hp : readNat (r input) with
  | none =>
    have he := exec_readUnary_malformed input outer (by decide) (r input).length r
      (readNat_none_eq hp)
    have hf := exec_seq_failure _ (seq (whileCounter outer clauseProg)
      (testEmpty input true false)) he
    refine ⟨_, false, _, ?_, hf, by simp [parseStep, hp]⟩
    unfold parseCost
    omega
  | some pair =>
    obtain ⟨n, rest⟩ := pair
    have hlen := congrArg List.length (readNat_eq_some hp)
    simp only [List.length_append, SATBounds.writeNat_length] at hlen
    have hn : n ≤ bound := by omega
    have hread := exec_readUnary_encoded input outer (by decide) n rest r (readNat_eq_some hp)
    let r₁ := set (set r input rest) outer (List.replicate n true)
    have hI₁ : ClauseInv bound r₁ := by
      have h₁ := hI.entries_le
      have h₂ := hI.count_le
      constructor
      · exact (hI.clean.set input (by decide) (by decide) _).set outer (by decide) (by decide) _
      · simpa [r₁] using hI.flag_eq
      · simp only [input, entries] at h₁ hlen ⊢; simp [r₁]; omega
      · simp only [input, count] at h₂ hlen ⊢; simp [r₁]; omega
      · simpa [r₁] using hI.inner_le
    obtain ⟨t, b, mid, ht, he, hspec⟩ := clauses_runs bound n r₁ hI₁ (by simp [r₁])
    have hloopCost : n * (clauseCost bound + 1) ≤ bound * (clauseCost bound + 1) :=
      Nat.mul_le_mul_right _ hn
    cases hex : iterStep outer clauseStep n r₁ with
    | none =>
      have hfalse : b = false := by simpa [hex] using hspec
      subst b
      have hfull := exec_seq _ _ hread (exec_seq_failure _ (testEmpty input true false) he)
      refine ⟨_, false, mid, ?_, hfull, by simp [parseStep, hp, r₁, hex]⟩
      unfold parseCost
      omega
    | some q =>
      have hs : b = true ∧ mid = q := by simpa [hex] using hspec
      obtain ⟨rfl, rfl⟩ := hs
      have htest := exec_testEmpty input true false mid
      have hfull := exec_seq _ _ hread (exec_seq _ _ he htest)
      refine ⟨_, _, mid, ?_, hfull, ?_⟩
      · unfold parseCost
        omega
      · have hex' : iterStep outer clauseStep n (set (set r input rest) outer
            (List.replicate n true)) = some mid := hex
        simp only [parseStep, hp, hex']
        cases hh : (mid input).isEmpty <;> simp

theorem parseStep_invariant (bound : Nat) (r : Registers 17) (hI : ClauseInv bound r)
    (q : Registers 17) (h : parseStep r = some q) : ClauseInv bound q := by
  unfold parseStep at h
  cases hp : readNat (r input) with
  | none => simp [hp] at h
  | some pair =>
    obtain ⟨n, rest⟩ := pair
    simp only [hp] at h
    have hlen := congrArg List.length (readNat_eq_some hp)
    simp only [List.length_append, SATBounds.writeNat_length] at hlen
    let r₁ := set (set r input rest) outer (List.replicate n true)
    have hI₁ : ClauseInv bound r₁ := by
      have h₁ := hI.entries_le
      have h₂ := hI.count_le
      constructor
      · exact (hI.clean.set input (by decide) (by decide) _).set outer (by decide) (by decide) _
      · simpa [r₁] using hI.flag_eq
      · simp only [input, entries] at h₁ hlen ⊢; simp [r₁]; omega
      · simp only [input, count] at h₂ hlen ⊢; simp [r₁]; omega
      · simpa [r₁] using hI.inner_le
    cases hex : iterStep outer clauseStep n r₁ with
    | none =>
      have hex' : iterStep outer clauseStep n (set (set r input rest) outer
          (List.replicate n true)) = none := hex
      simp [hex'] at h
    | some mid =>
      have hex' : iterStep outer clauseStep n (set (set r input rest) outer
          (List.replicate n true)) = some mid := hex
      simp only [hex'] at h
      obtain ⟨hIm, _⟩ := clauses_invariant bound n r₁ hI₁ (by simp [r₁]) mid hex
      cases hh : (mid input).isEmpty
      · simp [hh] at h
      · simp only [hh, ite_true, Option.some.injEq] at h
        subst h
        exact hIm

end Complexity.Binary.Verify
