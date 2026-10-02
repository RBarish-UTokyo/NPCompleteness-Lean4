module

public import Complexity.StackParse
public import Complexity.StackTableauArithmetic
public import Complexity.ChainThreeSAT
import Lean.Elab.Tactic.Omega

/-!
# A polynomial-time finite stack transducer from SAT to 3-SAT

Unary parsing, fresh-variable allocation, clause serialization, and malformed-input
recovery are performed by explicit finite programs. The complete machine halts
on every input within `4096 * (input.length + 1)^4` primitive instructions.
Its equivalence to the implication-chain reduction is proved separately in
`StackThreeSATSemantics`; `StackThreeSATReduction` transfers this runtime to the
original single-tape machine model.
-/
@[expose] public section
namespace Complexity.StackThreeSAT
open StackMachine (Registers set)
open StackProgram StackWords StackParse StackTableauArithmetic
open SAT

/-- Prepend a fixed compile-time word, using one literal push per bit. -/
def prependWord {k : Nat} (output : Fin (k + 1)) (word : Word) :
    Program k (Fin (word.length + 1)) where
  start := ⟨word.length, by omega⟩
  code q := if h : q.val = 0 then .halt true else
    .push output word[q.val - 1] (⟨q.val - 1, by have := q.isLt; omega⟩)

def prependWordEncoding (word : Word) : Encoding (Fin (word.length + 1)) :=
  Encoding.fin word.length

theorem exec_prependWord_aux {k : Nat} (output : Fin (k + 1)) (word : Word)
    (n : Nat) (hn : n ≤ word.length) (r : Registers k) :
    Exec (prependWord output word) ⟨n, by omega⟩ r (n + 1)
      (true, set r output (word.take n ++ r output)) := by
  induction n generalizing r with
  | zero =>
    simpa [set_unchanged] using (Exec.halt (p := prependWord output word)
      (q := (0 : Fin (word.length + 1))) (r := r) (by simp [StackProgram.step, prependWord]))
  | succ n ih =>
    have hlt : n < word.length := by omega
    let r' := set r output (word[n] :: r output)
    have he := ih (by omega) r'
    have hs : StackProgram.step (prependWord output word) ⟨n + 1, by omega⟩ r =
        .inr (⟨n, by omega⟩, r') := by
      simp [StackProgram.step, prependWord, r']
    have h := Exec.next hs he
    have ho : set r' output (word.take n ++ r' output) =
        set r output (word.take (n + 1) ++ r output) := by
      rw [List.take_succ_eq_append_getElem hlt]
      simp only [r', StackMachine.set_same, set_overwrite, List.append_assoc, List.singleton_append]
    simpa only [ho, Nat.add_assoc] using h

theorem exec_prependWord {k : Nat} (output : Fin (k + 1)) (word : Word)
    (r : Registers k) :
    Exec (prependWord output word) (prependWord output word).start r (word.length + 1)
      (true, set r output (word ++ r output)) := by
  simpa [prependWord, List.take_length] using exec_prependWord_aux output word
    word.length (Nat.le_refl _) r

/-- A fixed unary header uses width+2 genuine instructions. -/
def prependHeader {k : Nat} (output : Fin (k + 1)) (width : Nat) :=
  prependWord output (writeNat width)

theorem exec_prependHeader {k : Nat} (output : Fin (k + 1)) (width : Nat)
    (r : Registers k) :
    Exec (prependHeader output width) (prependHeader output width).start r (width + 2)
      (true, set r output (writeNat width ++ r output)) := by
  simpa [prependHeader, SATBounds.writeNat_length, Nat.add_assoc] using
    exec_prependWord output (writeNat width) r

abbrev ReadLiteralLabel := Sum Unit (Sum Unit
  (Sum (Sum Bool (Sum (Sum Bool (Fin 4)) PrependLiteralLabel))
       (Sum Bool (Sum (Sum Bool (Fin 4)) PrependLiteralLabel))))

/-- Consume a literal with known sign; reject a missing variable-index terminator. -/
def readLiteralSign {k : Nat} (source varReg output scratch : Fin (k + 1))
    (sign : Bool) :=
  seq (pop source) (seq (readUnary source varReg)
    (prependLiteral varReg output scratch sign))

def readLiteralSignEncoding :=
  Encoding.bool.sum (readUnaryEncoding.sum prependLiteralEncoding)

/-- Read and prepend one literal. Parsing failure is an actual rejecting halt. -/
def copyLiteral {k : Nat} (source varReg output scratch : Fin (k + 1)) :=
  peekCase source (stop k false)
    (readLiteralSign source varReg output scratch false)
    (readLiteralSign source varReg output scratch true)

def copyLiteralEncoding : Encoding ReadLiteralLabel :=
  Encoding.unit.sum (Encoding.unit.sum (readLiteralSignEncoding.sum readLiteralSignEncoding))

structure LiteralValid {k : Nat} (source varReg output scratch : Fin (k + 1)) : Prop where
  sv : source ≠ varReg
  so : source ≠ output
  ss : source ≠ scratch
  vo : varReg ≠ output
  vs : varReg ≠ scratch
  os : output ≠ scratch

def literalFinish {k : Nat} (source varReg output : Fin (k + 1))
    (r : Registers k) (l : Literal) (rest : Word) : Registers k :=
  set (set (set r source rest) varReg (List.replicate l.var true)) output
    (encodeLiteral l ++ r output)

theorem readLiteralSign_success {k : Nat} (source varReg output scratch : Fin (k + 1))
    (hv : LiteralValid source varReg output scratch) (r : Registers k)
    (hs : r scratch = []) (sign : Bool) (n : Nat) (rest : Word)
    (hi : r source = sign :: (writeNat n ++ rest)) :
    Exec (readLiteralSign source varReg output scratch sign)
      (readLiteralSign source varReg output scratch sign).start r
      ((r varReg).length + 7 * n + 14)
      (true, literalFinish source varReg output r ⟨n, sign⟩ rest) := by
  let r₀ := set r source (writeNat n ++ rest)
  let r₁ := set (set r₀ source rest) varReg (List.replicate n true)
  have hp : Exec (pop source) false r 2 (true, r₀) := by
    simpa [hi, r₀] using exec_pop source r
  have hparse := exec_readUnary_encoded source varReg hv.sv n rest r₀ (by simp [r₀])
  have hscratch : r₁ scratch = [] := by simp [r₁, r₀, Ne.symm hv.vs, Ne.symm hv.ss, hs]
  have hemit := exec_prependLiteral varReg output scratch hv.vo hv.vs hv.os sign r₁ hscratch
  have he := exec_seq (pop source)
    (seq (readUnary source varReg) (prependLiteral varReg output scratch sign)) hp
    (exec_seq (readUnary source varReg) (prependLiteral varReg output scratch sign) hparse hemit)
  have hcost : 2 + ((r₀ varReg).length + 2 * n + 4 +
      (5 * (r₁ varReg).length + 8)) = (r varReg).length + 7 * n + 14 := by
    simp [r₀, r₁, Ne.symm hv.sv]
    omega
  rw [hcost] at he
  simpa [readLiteralSign, seq, pop, literalFinish, r₁, r₀, Ne.symm hv.vo,
    Ne.symm hv.so, set_overwrite] using he

theorem copyLiteral_success {k : Nat} (source varReg output scratch : Fin (k + 1))
    (hv : LiteralValid source varReg output scratch) (r : Registers k)
    (hs : r scratch = []) (l : Literal) (rest : Word)
    (hi : readLiteral (r source) = some (l, rest)) :
    Exec (copyLiteral source varReg output scratch)
      (copyLiteral source varReg output scratch).start r
      ((r varReg).length + 7 * l.var + 15)
      (true, literalFinish source varReg output r l rest) := by
  have hi' := SATBounds.readLiteral_eq_some hi
  cases l with
  | mk n sign =>
    have hh := readLiteralSign_success source varReg output scratch hv r hs sign n rest hi'
    cases sign with
    | false =>
      simpa [copyLiteral, peekCase, Nat.add_assoc] using
        exec_peekCase_zero source (stop k false)
          (readLiteralSign source varReg output scratch false)
          (readLiteralSign source varReg output scratch true) hi' hh
    | true =>
      simpa [copyLiteral, peekCase, Nat.add_assoc] using
        exec_peekCase_one source (stop k false)
          (readLiteralSign source varReg output scratch false)
          (readLiteralSign source varReg output scratch true) hi' hh


theorem copyLiteral_failure {k : Nat} (source varReg output scratch : Fin (k + 1))
    (hv : LiteralValid source varReg output scratch) (r : Registers k)
    (hi : readLiteral (r source) = none) :
    ∃ t out, t ≤ (r varReg).length + 2 * (r source).length + 7 ∧
      Exec (copyLiteral source varReg output scratch)
        (copyLiteral source varReg output scratch).start r t (false, out) := by
  cases hr : r source with
  | nil =>
    refine ⟨2, r, by omega, ?_⟩
    exact exec_peekCase_empty source (stop k false)
      (readLiteralSign source varReg output scratch false)
      (readLiteralSign source varReg output scratch true) hr (exec_stop k false r)
  | cons sign rest =>
    have hp : readNat rest = none := by
      cases hh : readNat rest with
      | none => rfl
      | some value => cases value; simp [readLiteral, hr, hh] at hi
    let r₀ := set r source rest
    let result := set (set r₀ source []) varReg (List.replicate rest.length true)
    have hparse : Exec (readUnary source varReg) (readUnary source varReg).start r₀
        ((r₀ varReg).length + 2 * rest.length + 4) (false, result) :=
      exec_readUnary_malformed source varReg hv.sv rest.length r₀
        (by simpa only [r₀, StackMachine.set_same] using readNat_none_eq hp)
    have hrest := exec_seq_failure (readUnary source varReg)
      (prependLiteral varReg output scratch sign) hparse
    have hpop : Exec (pop source) false r 2 (true, r₀) := by
      simpa [r₀, hr] using exec_pop source r
    have hbody := exec_seq (pop source)
      (seq (readUnary source varReg) (prependLiteral varReg output scratch sign)) hpop hrest
    have hbody' : Exec (readLiteralSign source varReg output scratch sign)
        (readLiteralSign source varReg output scratch sign).start r
        ((r varReg).length + 2 * rest.length + 6) (false, result) := by
      have ht : 2 + ((r₀ varReg).length + 2 * rest.length + 4) =
          (r varReg).length + 2 * rest.length + 6 := by
        simp [r₀, Ne.symm hv.sv]
        omega
      rw [ht] at hbody
      exact hbody
    refine ⟨(r varReg).length + 2 * rest.length + 7, result, by simp; omega, ?_⟩
    cases sign with
    | false =>
      simpa [copyLiteral, peekCase, Nat.add_assoc] using
        exec_peekCase_zero source (stop k false)
          (readLiteralSign source varReg output scratch false)
          (readLiteralSign source varReg output scratch true) hr hbody'
    | true =>
      simpa [copyLiteral, peekCase, Nat.add_assoc] using
        exec_peekCase_one source (stop k false)
          (readLiteralSign source varReg output scratch false)
          (readLiteralSign source varReg output scratch true) hr hbody'

abbrev Reg := Fin 8
def input : Reg := 0
def fresh : Reg := 1
def outer : Reg := 2
def inner : Reg := 3
def work : Reg := 4
def scratch : Reg := 5
def output : Reg := 6
def count : Reg := 7

abbrev ChainLiteralLabel := Sum PrependLiteralLabel
  (Sum ReadLiteralLabel (Sum Bool (Sum PrependLiteralLabel (Sum (Fin 5) Bool))))

/-- One original literal produces the implication clause
`z_(i+1) ∨ literal ∨ ¬z_i`, then increments the output-clause count. -/
def chainLiteral : Program 7 ChainLiteralLabel :=
  seq (prependLiteral fresh output scratch false)
    (seq (copyLiteral input work output scratch)
      (seq (increment fresh)
        (seq (prependLiteral fresh output scratch true)
          (seq (prependHeader output 3) (increment count)))))

def chainLiteralEncoding : Encoding ChainLiteralLabel :=
  prependLiteralEncoding.sum (copyLiteralEncoding.sum (Encoding.bool.sum
    (prependLiteralEncoding.sum ((Encoding.fin 4).sum Encoding.bool))))

abbrev implicationClause := ChainThreeSAT.implicationClause

def chainLiteralFinish (r : Registers 7) (l : Literal) (rest : Word) : Registers 7 :=
  set (set (set (set (set r input rest) work (List.replicate l.var true))
    fresh (true :: r fresh)) output
    (encodeClause (implicationClause (r fresh).length l) ++ r output))
    count (true :: r count)

theorem chainLiteral_success (r : Registers 7) (hs : r scratch = [])
    (l : Literal) (rest : Word) (hp : readLiteral (r input) = some (l, rest)) :
    Exec chainLiteral chainLiteral.start r
      ((r work).length + 7 * l.var + 10 * (r fresh).length + 45)
      (true, chainLiteralFinish r l rest) := by
  let r₀ := set r output (encodeLiteral ⟨(r fresh).length, false⟩ ++ r output)
  let r₁ := literalFinish input work output r₀ l rest
  let r₂ := set r₁ fresh (true :: r₁ fresh)
  let r₃ := set r₂ output (encodeLiteral ⟨(r₂ fresh).length, true⟩ ++ r₂ output)
  let r₄ := set r₃ output (writeNat 3 ++ r₃ output)
  have h₀ := exec_prependLiteral fresh output scratch (by decide) (by decide)
    (by decide) false r hs
  have hs₀ : r₀ scratch = [] := by simpa [r₀, scratch, output] using hs
  have hp₀ : readLiteral (r₀ input) = some (l, rest) := by simpa [r₀, input, output] using hp
  have hv : LiteralValid input work output scratch := by constructor <;> decide
  have h₁ := copyLiteral_success input work output scratch hv r₀ hs₀ l rest hp₀
  have h₂ := exec_push fresh true r₁
  have hs₂ : r₂ scratch = [] := by
    simpa [r₂, r₁, r₀, literalFinish, scratch, input, work, output, fresh] using hs
  have h₃ := exec_prependLiteral fresh output scratch (by decide) (by decide)
    (by decide) true r₂ hs₂
  have h₄ := exec_prependHeader output 3 r₃
  have h₅ := exec_push count true r₄
  have he := exec_seq (prependLiteral fresh output scratch false)
    (seq (copyLiteral input work output scratch)
      (seq (increment fresh) (seq (prependLiteral fresh output scratch true)
        (seq (prependHeader output 3) (increment count))))) h₀
    (exec_seq (copyLiteral input work output scratch)
      (seq (increment fresh) (seq (prependLiteral fresh output scratch true)
        (seq (prependHeader output 3) (increment count)))) h₁
      (exec_seq (increment fresh)
        (seq (prependLiteral fresh output scratch true)
          (seq (prependHeader output 3) (increment count))) h₂
        (exec_seq (prependLiteral fresh output scratch true)
          (seq (prependHeader output 3) (increment count)) h₃
          (exec_seq (prependHeader output 3) (increment count) h₄ h₅))))
  have htime : 5 * (r fresh).length + 8 +
      ((r₀ work).length + 7 * l.var + 15 +
        (2 + (5 * (r₂ fresh).length + 8 + (3 + 2 + 2)))) =
      (r work).length + 7 * l.var + 10 * (r fresh).length + 45 := by
    simp [r₂, r₁, r₀, literalFinish, fresh, input, work, output, Nat.mul_add]
    omega
  rw [htime] at he
  have hout : set r₄ count (true :: r₄ count) = chainLiteralFinish r l rest := by
    funext a
    by_cases hc : a = count
    · subst a
      simp [r₄, r₃, r₂, r₁, r₀, chainLiteralFinish, literalFinish, count, output,
        fresh, input, work]
    · by_cases ho : a = output
      · subst a
        simp [r₄, r₃, r₂, r₁, r₀, chainLiteralFinish, literalFinish, implicationClause, ChainThreeSAT.implicationClause,
          encodeClause, writeList, writeValues, ThreeSAT.pos, ThreeSAT.neg,
          output, count, fresh, input, work, List.append_assoc]
      · by_cases hf : a = fresh
        · subst a
          simp [r₄, r₃, r₂, r₁, r₀, chainLiteralFinish, literalFinish,
            fresh, count, output, input, work]
        · by_cases hw : a = work
          · subst a
            simp [r₄, r₃, r₂, r₁, r₀, chainLiteralFinish, literalFinish,
              work, fresh, count, output, input]
          · by_cases hi : a = input
            · subst a
              simp [r₄, r₃, r₂, r₁, r₀, chainLiteralFinish, literalFinish,
                input, work, fresh, count, output]
            · simp [r₄, r₃, r₂, r₁, r₀, chainLiteralFinish, literalFinish,
                StackMachine.set, hc, ho, hf, hw, hi]
  rw [hout] at he
  exact he


theorem chainLiteral_failure (r : Registers 7)
    (hs : r scratch = []) (hp : readLiteral (r input) = none) :
    ∃ t out, t ≤ (r work).length + 2 * (r input).length + 5 * (r fresh).length + 15 ∧
      Exec chainLiteral chainLiteral.start r t (false, out) := by
  let r₀ := set r output (encodeLiteral ⟨(r fresh).length, false⟩ ++ r output)
  have h₀ := exec_prependLiteral fresh output scratch (by decide) (by decide)
    (by decide) false r hs
  have hp₀ : readLiteral (r₀ input) = none := by simpa [r₀, input, output] using hp
  have hv : LiteralValid input work output scratch := by constructor <;> decide
  obtain ⟨t, out, ht, he⟩ := copyLiteral_failure input work output scratch hv r₀ hp₀
  have hfailed := exec_seq_failure (copyLiteral input work output scratch)
    (seq (increment fresh) (seq (prependLiteral fresh output scratch true)
      (seq (prependHeader output 3) (increment count)))) he
  have h := exec_seq (prependLiteral fresh output scratch false)
    (seq (copyLiteral input work output scratch)
      (seq (increment fresh) (seq (prependLiteral fresh output scratch true)
        (seq (prependHeader output 3) (increment count))))) h₀ hfailed
  refine ⟨5 * (r fresh).length + 8 + t, out, ?_, h⟩
  simp only [r₀, StackMachine.set_other _ (by decide : work ≠ output),
    StackMachine.set_other _ (by decide : input ≠ output)] at ht
  omega

@[simp] theorem chainFinish_input (r : Registers 7) (l : Literal) (rest : Word) :
    chainLiteralFinish r l rest input = rest := by
  simp [chainLiteralFinish, input, work, fresh, output, count]

@[simp] theorem chainFinish_work (r : Registers 7) (l : Literal) (rest : Word) :
    chainLiteralFinish r l rest work = List.replicate l.var true := by
  simp [chainLiteralFinish, input, work, fresh, output, count]

@[simp] theorem chainFinish_fresh (r : Registers 7) (l : Literal) (rest : Word) :
    chainLiteralFinish r l rest fresh = true :: r fresh := by
  simp [chainLiteralFinish, input, work, fresh, output, count]

@[simp] theorem chainFinish_output (r : Registers 7) (l : Literal) (rest : Word) :
    chainLiteralFinish r l rest output =
      encodeClause (implicationClause (r fresh).length l) ++ r output := by
  simp [chainLiteralFinish, input, work, fresh, output, count]

@[simp] theorem chainFinish_count (r : Registers 7) (l : Literal) (rest : Word) :
    chainLiteralFinish r l rest count = true :: r count := by
  simp [chainLiteralFinish]

@[simp] theorem chainFinish_inner (r : Registers 7) (l : Literal) (rest : Word) :
    chainLiteralFinish r l rest inner = r inner := by
  simp [chainLiteralFinish, inner, input, work, fresh, output, count]

@[simp] theorem chainFinish_outer (r : Registers 7) (l : Literal) (rest : Word) :
    chainLiteralFinish r l rest outer = r outer := by
  simp [chainLiteralFinish, outer, input, work, fresh, output, count]

@[simp] theorem chainFinish_scratch (r : Registers 7) (l : Literal) (rest : Word) :
    chainLiteralFinish r l rest scratch = r scratch := by
  simp [chainLiteralFinish, scratch, input, work, fresh, output, count]

structure Bounded (bound : Nat) (r : Registers 7) : Prop where
  input_le : (r input).length ≤ bound
  work_le : (r work).length ≤ bound
  scratch_eq : r scratch = []

theorem Bounded.literal {bound : Nat} {r : Registers 7} (h : Bounded bound r)
    (l : Literal) (rest : Word) (hp : readLiteral (r input) = some (l, rest)) :
    Bounded bound (chainLiteralFinish r l rest) := by
  have he := congrArg List.length (SATBounds.readLiteral_eq_some hp)
  simp only [List.length_append, SATBounds.encodeLiteral_length] at he
  have hin := h.input_le
  constructor
  · simp only [chainFinish_input]; omega
  · simp only [chainFinish_work, List.length_replicate]; omega
  · simpa using h.scratch_eq

theorem Bounded.set_inner {bound : Nat} {r : Registers 7} (h : Bounded bound r)
    (xs : Word) : Bounded bound (set r inner xs) := by
  constructor
  · simpa [input, inner] using h.input_le
  · simpa [work, inner] using h.work_le
  · simpa [scratch, inner] using h.scratch_eq

/-- High-level partial semantics for the exact finite loop body. -/
def literalStep (r : Registers 7) : Option (Registers 7) := do
  let (l, rest) ← readLiteral (r input)
  pure (chainLiteralFinish r l rest)

def literalsStep : Nat → Registers 7 → Option (Registers 7)
  | 0, r => some r
  | n + 1, r => do
      let next ← literalStep (set r inner (List.replicate n true))
      literalsStep n next

def Realizes (expected : Option (Registers 7)) (b : Bool) (r : Registers 7) : Prop :=
  match expected with
  | none => b = false
  | some q => b = true ∧ r = q

theorem chainLiteral_runs (bound capacity : Nat) (r : Registers 7)
    (hb : Bounded bound r) (hc : (r fresh).length ≤ capacity) :
    ∃ t b out, t ≤ 8 * bound + 10 * capacity + 45 ∧
      Exec chainLiteral chainLiteral.start r t (b, out) ∧
      Realizes (literalStep r) b out := by
  cases hp : readLiteral (r input) with
  | none =>
    obtain ⟨t, out, ht, he⟩ := chainLiteral_failure r hb.scratch_eq hp
    refine ⟨t, false, out, ?_, he, ?_⟩
    · have hwork := hb.work_le; have hin := hb.input_le
      omega
    · simp [Realizes, literalStep, hp]
  | some pair =>
    obtain ⟨l, rest⟩ := pair
    have hlen := congrArg List.length (SATBounds.readLiteral_eq_some hp)
    simp only [List.length_append, SATBounds.encodeLiteral_length] at hlen
    refine ⟨(r work).length + 7 * l.var + 10 * (r fresh).length + 45,
      true, chainLiteralFinish r l rest, ?_, chainLiteral_success r hb.scratch_eq l rest hp, ?_⟩
    · have hwork := hb.work_le; have hin := hb.input_le
      omega
    · simp [Realizes, literalStep, hp]

theorem literals_runs (bound capacity n : Nat) (r : Registers 7)
    (hb : Bounded bound r) (hr : r inner = List.replicate n true)
    (hc : (r fresh).length + n ≤ capacity) :
    ∃ t b out, t ≤ n * (8 * bound + 10 * capacity + 46) + 2 ∧
      Exec (whileCounter inner chainLiteral) (.inl false) r t (b, out) ∧
      Realizes (literalsStep n r) b out ∧
      (b = true → Bounded bound out ∧ out inner = [] ∧
        (out fresh).length = (r fresh).length + n ∧ out outer = r outer) := by
  induction n generalizing r with
  | zero =>
    refine ⟨2, true, r, by simp, exec_whileCounter_done inner chainLiteral r (by simpa using hr), ?_, ?_⟩
    · simp [Realizes, literalsStep]
    · intro _; exact ⟨hb, by simpa using hr, by omega, rfl⟩
  | succ n ih =>
    let r₀ := set r inner (List.replicate n true)
    have hb₀ := hb.set_inner (List.replicate n true)
    have hf₀ : (r₀ fresh).length = (r fresh).length := by simp [r₀, fresh, inner]
    have hi₀ : r₀ input = r input := by simp [r₀, input, inner]
    have hcons : r inner = true :: List.replicate n true := by simpa [List.replicate_succ] using hr
    obtain ⟨t, b, mid, ht, he, hspec⟩ := chainLiteral_runs bound capacity r₀ hb₀ (by omega)
    cases hp : readLiteral (r input) with
    | none =>
      have hbf : b = false := by simpa [Realizes, literalStep, hi₀, hp] using hspec
      subst b
      refine ⟨t + 1, false, mid, ?_, exec_whileCounter_failure inner chainLiteral hcons he, ?_, by simp⟩
      · have hm := Nat.mul_le_mul_right (8 * bound + 10 * capacity + 46) (Nat.le_succ n)
        rw [Nat.succ_mul]
        omega
      · simp [Realizes, literalsStep, literalStep, hi₀, hp, r₀]
    | some pair =>
      obtain ⟨l, rest⟩ := pair
      have hspec' : b = true ∧ mid = chainLiteralFinish r₀ l rest := by
        simpa [Realizes, literalStep, hi₀, hp] using hspec
      obtain ⟨rfl, rfl⟩ := hspec'
      have hp₀ : readLiteral (r₀ input) = some (l, rest) := by simpa [hi₀] using hp
      have hbm := hb₀.literal l rest hp₀
      have hinner : chainLiteralFinish r₀ l rest inner = List.replicate n true := by simp [r₀]
      have hfm : (chainLiteralFinish r₀ l rest fresh).length = (r fresh).length + 1 := by
        simp [hf₀]
      obtain ⟨s, b, out, hs, he', hspec', hout⟩ := ih (chainLiteralFinish r₀ l rest)
        hbm hinner (by omega)
      refine ⟨t + s + 1, b, out, ?_, exec_whileCounter_next inner chainLiteral hcons he he', ?_, ?_⟩
      · rw [Nat.succ_mul]
        omega
      · simpa [Realizes, literalsStep, literalStep, hi₀, hp, r₀] using hspec'
      · intro htrue
        obtain ⟨hbo, hio, hfo, hoo⟩ := hout htrue
        refine ⟨hbo, hio, by omega, ?_⟩
        rw [chainFinish_outer] at hoo
        simpa [r₀, outer, inner] using hoo


abbrev UnitLabel := Sum PrependLiteralLabel (Sum (Fin 3) Bool)

def emitUnit (sign : Bool) : Program 7 UnitLabel :=
  seq (prependLiteral fresh output scratch sign)
    (seq (prependHeader output 1) (increment count))

def emitUnitEncoding : Encoding UnitLabel :=
  prependLiteralEncoding.sum ((Encoding.fin 2).sum Encoding.bool)

def unitFinish (r : Registers 7) (sign : Bool) : Registers 7 :=
  set (set r output (encodeClause [⟨(r fresh).length, sign⟩] ++ r output))
    count (true :: r count)

theorem emitUnit_runs (sign : Bool) (r : Registers 7) (hs : r scratch = []) :
    Exec (emitUnit sign) (emitUnit sign).start r (5 * (r fresh).length + 13)
      (true, unitFinish r sign) := by
  let r₀ := set r output (encodeLiteral ⟨(r fresh).length, sign⟩ ++ r output)
  let r₁ := set r₀ output (writeNat 1 ++ r₀ output)
  have h₀ := exec_prependLiteral fresh output scratch (by decide) (by decide) (by decide) sign r hs
  have h₁ := exec_prependHeader output 1 r₀
  have h₂ := exec_push count true r₁
  have he := exec_seq (prependLiteral fresh output scratch sign)
    (seq (prependHeader output 1) (increment count)) h₀
    (exec_seq (prependHeader output 1) (increment count) h₁ h₂)
  have ho : set r₁ count (true :: r₁ count) = unitFinish r sign := by
    simp [unitFinish, r₁, r₀, encodeClause, writeList, writeValues, count, output,
      set_overwrite, List.append_assoc]
  rw [ho] at he
  have ht : 5 * (r fresh).length + 8 + (1 + 2 + 2) =
      5 * (r fresh).length + 13 := by omega
  rw [ht] at he
  exact he

@[simp] theorem unitFinish_output (r : Registers 7) (sign : Bool) :
    unitFinish r sign output = encodeClause [⟨(r fresh).length, sign⟩] ++ r output := by
  simp [unitFinish, output, count]

@[simp] theorem unitFinish_count (r : Registers 7) (sign : Bool) :
    unitFinish r sign count = true :: r count := by simp [unitFinish]

theorem unitFinish_frame (r : Registers 7) (sign : Bool) (j : Reg)
    (ho : j ≠ output) (hc : j ≠ count) : unitFinish r sign j = r j := by
  simp [unitFinish, ho, hc]

@[simp] theorem unitFinish_input (r : Registers 7) (sign : Bool) :
    unitFinish r sign input = r input := unitFinish_frame r sign input (by decide) (by decide)
@[simp] theorem unitFinish_fresh (r : Registers 7) (sign : Bool) :
    unitFinish r sign fresh = r fresh := unitFinish_frame r sign fresh (by decide) (by decide)
@[simp] theorem unitFinish_outer (r : Registers 7) (sign : Bool) :
    unitFinish r sign outer = r outer := unitFinish_frame r sign outer (by decide) (by decide)
@[simp] theorem unitFinish_inner (r : Registers 7) (sign : Bool) :
    unitFinish r sign inner = r inner := unitFinish_frame r sign inner (by decide) (by decide)
@[simp] theorem unitFinish_work (r : Registers 7) (sign : Bool) :
    unitFinish r sign work = r work := unitFinish_frame r sign work (by decide) (by decide)
@[simp] theorem unitFinish_scratch (r : Registers 7) (sign : Bool) :
    unitFinish r sign scratch = r scratch := unitFinish_frame r sign scratch (by decide) (by decide)

theorem Bounded.unit {bound : Nat} {r : Registers 7} (h : Bounded bound r)
    (sign : Bool) : Bounded bound (unitFinish r sign) := by
  constructor
  · simpa using h.input_le
  · simpa using h.work_le
  · simpa using h.scratch_eq

theorem Bounded.unary {bound : Nat} {r : Registers 7} (h : Bounded bound r)
    (n : Nat) (rest : Word) (hp : readNat (r input) = some (n, rest)) :
    Bounded bound (set (set r input rest) inner (List.replicate n true)) := by
  have he := congrArg List.length (SATBounds.readNat_eq_some hp)
  simp only [List.length_append, SATBounds.writeNat_length] at he
  have hin := h.input_le
  constructor
  · simp only [StackMachine.set_other _ (by decide : input ≠ inner), StackMachine.set_same]
    omega
  · simpa [work, input, inner] using h.work_le
  · simpa [scratch, input, inner] using h.scratch_eq

theorem Bounded.increment_fresh {bound : Nat} {r : Registers 7} (h : Bounded bound r) :
    Bounded bound (set r fresh (true :: r fresh)) := by
  constructor
  · simpa [input, fresh] using h.input_le
  · simpa [work, fresh] using h.work_le
  · simpa [scratch, fresh] using h.scratch_eq

abbrev ClauseLabel := Sum (Sum Bool (Fin 4))
  (Sum UnitLabel (Sum (Sum Bool ChainLiteralLabel) (Sum UnitLabel Bool)))

def clause : Program 7 ClauseLabel :=
  seq (readUnary input inner) (seq (emitUnit true)
    (seq (whileCounter inner chainLiteral) (seq (emitUnit false) (increment fresh))))

def clauseEncoding : Encoding ClauseLabel :=
  readUnaryEncoding.sum (emitUnitEncoding.sum
    ((Encoding.bool.sum chainLiteralEncoding).sum (emitUnitEncoding.sum Encoding.bool)))

def clauseStep (r : Registers 7) : Option (Registers 7) := do
  let (n, rest) ← readNat (r input)
  let q := unitFinish (set (set r input rest) inner (List.replicate n true)) true
  let out ← literalsStep n q
  pure (set (unitFinish out false) fresh (true :: out fresh))

def clauseBudget (bound capacity : Nat) :=
  bound * (8 * bound + 10 * capacity + 46) + 3 * bound + 10 * capacity + 34

theorem clause_runs (bound capacity : Nat) (r : Registers 7)
    (hb : Bounded bound r) (hi : (r inner).length ≤ bound)
    (hc : (r fresh).length + bound ≤ capacity) :
    ∃ t b out, t ≤ clauseBudget bound capacity ∧
      Exec clause clause.start r t (b, out) ∧ Realizes (clauseStep r) b out ∧
      (b = true → Bounded bound out ∧ out inner = [] ∧
        (out fresh).length ≤ (r fresh).length + bound + 1 ∧ out outer = r outer) := by
  cases hp : readNat (r input) with
  | none =>
    let out := set (set r input []) inner (List.replicate (r input).length true)
    have he : Exec (readUnary input inner) (readUnary input inner).start r
        ((r inner).length + 2 * (r input).length + 4) (false, out) :=
      exec_readUnary_malformed input inner (by decide) (r input).length r (readNat_none_eq hp)
    have hf := exec_seq_failure (readUnary input inner)
      (seq (emitUnit true) (seq (whileCounter inner chainLiteral)
        (seq (emitUnit false) (increment fresh)))) he
    refine ⟨_, false, out, ?_, hf, ?_, by simp⟩
    · have hh := hb.input_le
      unfold clauseBudget
      omega
    · simp [Realizes, clauseStep, hp]
  | some pair =>
    obtain ⟨n, rest⟩ := pair
    have hlen := congrArg List.length (SATBounds.readNat_eq_some hp)
    simp only [List.length_append, SATBounds.writeNat_length] at hlen
    have hn : n ≤ bound := by have h := hb.input_le; omega
    let r₀ := set (set r input rest) inner (List.replicate n true)
    let r₁ := unitFinish r₀ true
    have hb₀ := hb.unary n rest hp
    have hb₁ := hb₀.unit true
    have hinner : r₁ inner = List.replicate n true := by simp [r₁, r₀]
    have hfresh : r₁ fresh = r fresh := by
      simp only [r₁, unitFinish_fresh, r₀,
        StackMachine.set_other _ (by decide : fresh ≠ inner),
        StackMachine.set_other _ (by decide : fresh ≠ input)]
    have houter : r₁ outer = r outer := by
      simp only [r₁, unitFinish_outer, r₀,
        StackMachine.set_other _ (by decide : outer ≠ inner),
        StackMachine.set_other _ (by decide : outer ≠ input)]
    have hread := exec_readUnary_encoded input inner (by decide) n rest r
      (SATBounds.readNat_eq_some hp)
    have hstart := emitUnit_runs true r₀ hb₀.scratch_eq
    obtain ⟨t, b, mid, ht, he, hspec, hsuccess⟩ := literals_runs bound capacity n r₁ hb₁
      hinner (by simpa [hfresh] using Nat.le_trans (Nat.add_le_add_left hn _) hc)
    cases hex : literalsStep n r₁ with
    | none =>
      have hfalse : b = false := by simpa [Realizes, hex] using hspec
      subst b
      have hfailed := exec_seq_failure (whileCounter inner chainLiteral)
        (seq (emitUnit false) (increment fresh)) he
      have hfull := exec_seq (readUnary input inner)
        (seq (emitUnit true) (seq (whileCounter inner chainLiteral)
          (seq (emitUnit false) (increment fresh)))) hread
        (exec_seq (emitUnit true) (seq (whileCounter inner chainLiteral)
          (seq (emitUnit false) (increment fresh))) hstart hfailed)
      refine ⟨_, false, mid, ?_, hfull, ?_, by simp⟩
      · have hm := Nat.mul_le_mul_right (8 * bound + 10 * capacity + 46) hn
        have hf : (r₀ fresh).length ≤ capacity := by
          simp only [r₀, StackMachine.set_other _ (by decide : fresh ≠ inner),
            StackMachine.set_other _ (by decide : fresh ≠ input)]
          omega
        unfold clauseBudget
        omega
      · simp only [clauseStep, hp]
        change Realizes ((literalsStep n r₁).bind _) false mid
        simp [hex, Realizes]
    | some q =>
      have hs : b = true ∧ mid = q := by simpa [Realizes, hex] using hspec
      obtain ⟨rfl, rfl⟩ := hs
      obtain ⟨hbm, him, hfm, hom⟩ := hsuccess rfl
      have hfmcap : (mid fresh).length ≤ capacity := by rw [hfm, hfresh]; omega
      let r₂ := unitFinish mid false
      let out := set r₂ fresh (true :: mid fresh)
      have hend := emitUnit_runs false mid hbm.scratch_eq
      have hinc : Exec (increment fresh) (increment fresh).start r₂ 2 (true, out) := by
        change Exec (push fresh true) false r₂ 2 (true, out)
        simpa only [out, r₂, unitFinish_fresh] using exec_push fresh true r₂
      have hfull := exec_seq (readUnary input inner)
        (seq (emitUnit true) (seq (whileCounter inner chainLiteral)
          (seq (emitUnit false) (increment fresh)))) hread
        (exec_seq (emitUnit true) (seq (whileCounter inner chainLiteral)
          (seq (emitUnit false) (increment fresh))) hstart
          (exec_seq (whileCounter inner chainLiteral) (seq (emitUnit false) (increment fresh)) he
            (exec_seq (emitUnit false) (increment fresh) hend hinc)))
      refine ⟨_, true, out, ?_, hfull, ?_, ?_⟩
      · have hm := Nat.mul_le_mul_right (8 * bound + 10 * capacity + 46) hn
        have hf : (r₀ fresh).length ≤ capacity := by
          simp only [r₀, StackMachine.set_other _ (by decide : fresh ≠ inner),
            StackMachine.set_other _ (by decide : fresh ≠ input)]
          omega
        unfold clauseBudget
        omega
      · simp only [clauseStep, hp]
        change Realizes ((literalsStep n r₁).bind _) true out
        simp [hex, Realizes, out, r₂]
      · intro _
        have hbo := (hbm.unit false).increment_fresh
        refine ⟨by simpa [out, r₂] using hbo, ?_, ?_, ?_⟩
        · simpa only [out, StackMachine.set_other _ (by decide : inner ≠ fresh),
            r₂, unitFinish_inner] using him
        · simp only [out, StackMachine.set_same, List.length_cons]
          rw [hfm, hfresh]
          omega
        · simpa only [out, StackMachine.set_other _ (by decide : outer ≠ fresh),
            r₂, unitFinish_outer] using hom.trans houter


def clausesStep : Nat → Registers 7 → Option (Registers 7)
  | 0, r => some r
  | n + 1, r => do
      let next ← clauseStep (set r outer (List.replicate n true))
      clausesStep n next

theorem Bounded.set_outer {bound : Nat} {r : Registers 7} (h : Bounded bound r)
    (xs : Word) : Bounded bound (set r outer xs) := by
  constructor
  · simpa [input, outer] using h.input_le
  · simpa [work, outer] using h.work_le
  · simpa [scratch, outer] using h.scratch_eq

theorem clauses_runs (bound capacity n : Nat) (r : Registers 7)
    (hb : Bounded bound r) (hr : r outer = List.replicate n true)
    (hi : (r inner).length ≤ bound)
    (hc : (r fresh).length + n * (bound + 1) + bound ≤ capacity) :
    ∃ t b out, t ≤ n * (clauseBudget bound capacity + 1) + 2 ∧
      Exec (whileCounter outer clause) (.inl false) r t (b, out) ∧
      Realizes (clausesStep n r) b out ∧
      (b = true → Bounded bound out ∧ out outer = [] ∧
        (out fresh).length ≤ (r fresh).length + n * (bound + 1) ∧
        (out inner).length ≤ bound) := by
  induction n generalizing r with
  | zero =>
    refine ⟨2, true, r, by simp, exec_whileCounter_done outer clause r (by simpa using hr), ?_, ?_⟩
    · simp [Realizes, clausesStep]
    · intro _; exact ⟨hb, by simpa using hr, by omega, hi⟩
  | succ n ih =>
    let r₀ := set r outer (List.replicate n true)
    have hb₀ := hb.set_outer (List.replicate n true)
    have hf₀ : r₀ fresh = r fresh := by simp [r₀, fresh, outer]
    have hi₀ : r₀ inner = r inner := by simp [r₀, inner, outer]
    have hcons : r outer = true :: List.replicate n true := by simpa [List.replicate_succ] using hr
    obtain ⟨t, b, mid, ht, he, hspec, hsuccess⟩ := clause_runs bound capacity r₀ hb₀
      (by simpa [hi₀] using hi) (by simp only [hf₀]; omega)
    cases hp : clauseStep r₀ with
    | none =>
      have hbf : b = false := by simpa [Realizes, hp] using hspec
      subst b
      refine ⟨t + 1, false, mid, ?_, exec_whileCounter_failure outer clause hcons he, ?_, by simp⟩
      · rw [Nat.succ_mul]; omega
      · change Realizes ((clauseStep r₀).bind (clausesStep n)) false mid
        simp [Realizes, hp]
    | some q =>
      have hspec' : b = true ∧ mid = q := by simpa [Realizes, hp] using hspec
      obtain ⟨rfl, rfl⟩ := hspec'
      obtain ⟨hbm, him, hfm, hom⟩ := hsuccess rfl
      have houter : mid outer = List.replicate n true := by simpa [r₀] using hom
      have hroom : (mid fresh).length + n * (bound + 1) + bound ≤ capacity := by
        rw [Nat.succ_mul] at hc
        rw [hf₀] at hfm
        omega
      obtain ⟨s, b, out, hs, he', hspec', hout⟩ := ih mid hbm houter (by simp [him]) hroom
      refine ⟨t + s + 1, b, out, ?_, exec_whileCounter_next outer clause hcons he he', ?_, ?_⟩
      · rw [Nat.succ_mul]; omega
      · change Realizes ((clauseStep r₀).bind (clausesStep n)) b out
        simpa [Realizes, hp] using hspec'
      · intro htrue
        obtain ⟨hbo, hoo, hfo, hio⟩ := hout htrue
        refine ⟨hbo, hoo, ?_, hio⟩
        rw [Nat.succ_mul]
        rw [hf₀] at hfm
        omega

def testEmpty (j : Reg) : Program 7 (Fin 3) where
  start := 0
  code q := if q = 0 then .peek j 1 2 2
    else if q = 1 then .halt true else .halt false

theorem exec_testEmpty (j : Reg) (r : Registers 7) :
    Exec (testEmpty j) 0 r 2 ((r j).isEmpty, r) := by
  cases hr : r j with
  | nil =>
    apply Exec.next (q' := 1) (r' := r)
    · simp [StackProgram.step, testEmpty, hr, StackMachine.branch]
    · exact .halt (by simp [StackProgram.step, testEmpty])
  | cons b rest =>
    apply Exec.next (q' := 2) (r' := r)
    · cases b <;> simp [StackProgram.step, testEmpty, hr, StackMachine.branch]
    · exact .halt (by simp [StackProgram.step, testEmpty])

abbrev ParseCNFLabel := Sum (Sum Bool (Fin 4)) (Sum (Sum Bool ClauseLabel) (Fin 3))

def parseCNF : Program 7 ParseCNFLabel :=
  seq (readUnary input outer) (seq (whileCounter outer clause) (testEmpty input))

def parseCNFEncoding : Encoding ParseCNFLabel :=
  readUnaryEncoding.sum ((Encoding.bool.sum clauseEncoding).sum (Encoding.fin 2))

def parseCNFStep (r : Registers 7) : Option (Registers 7) := do
  let (n, rest) ← readNat (r input)
  let out ← clausesStep n (set (set r input rest) outer (List.replicate n true))
  if (out input).isEmpty then some out else none

def parseBudget (bound capacity : Nat) :=
  bound * (clauseBudget bound capacity + 1) + 3 * bound + 8

theorem parseCNF_runs (bound capacity : Nat) (r : Registers 7)
    (hb : Bounded bound r) (hi : (r inner).length ≤ bound) (ho : (r outer).length ≤ bound)
    (hc : (r fresh).length + bound * (bound + 1) + bound ≤ capacity) :
    ∃ t b out, t ≤ parseBudget bound capacity ∧
      Exec parseCNF parseCNF.start r t (b, out) ∧ Realizes (parseCNFStep r) b out ∧
      (b = true → Bounded bound out ∧ out input = []) := by
  cases hp : readNat (r input) with
  | none =>
    let out := set (set r input []) outer (List.replicate (r input).length true)
    have he : Exec (readUnary input outer) (readUnary input outer).start r
        ((r outer).length + 2 * (r input).length + 4) (false, out) :=
      exec_readUnary_malformed input outer (by decide) (r input).length r (readNat_none_eq hp)
    have hf := exec_seq_failure (readUnary input outer)
      (seq (whileCounter outer clause) (testEmpty input)) he
    refine ⟨_, false, out, ?_, hf, ?_, by simp⟩
    · have hh := hb.input_le
      unfold parseBudget
      omega
    · simp [Realizes, parseCNFStep, hp]
  | some pair =>
    obtain ⟨n, rest⟩ := pair
    have hlen := congrArg List.length (SATBounds.readNat_eq_some hp)
    simp only [List.length_append, SATBounds.writeNat_length] at hlen
    have hn : n ≤ bound := by have h := hb.input_le; omega
    let r₀ := set (set r input rest) outer (List.replicate n true)
    have hb₀ : Bounded bound r₀ := by
      constructor
      · simp only [r₀, StackMachine.set_other _ (by decide : input ≠ outer), StackMachine.set_same]
        have hh := hb.input_le; omega
      · simpa [r₀, work, input, outer] using hb.work_le
      · simpa [r₀, scratch, input, outer] using hb.scratch_eq
    have hi₀ : (r₀ inner).length ≤ bound := by simpa [r₀, inner, input, outer] using hi
    have hf₀ : r₀ fresh = r fresh := by simp [r₀, fresh, input, outer]
    have hc₀ : (r₀ fresh).length + n * (bound + 1) + bound ≤ capacity := by
      rw [hf₀]
      have hm := Nat.mul_le_mul_right (bound + 1) hn
      omega
    have hread := exec_readUnary_encoded input outer (by decide) n rest r
      (SATBounds.readNat_eq_some hp)
    obtain ⟨t, b, mid, ht, he, hspec, hsuccess⟩ := clauses_runs bound capacity n r₀ hb₀
      (by simp [r₀]) hi₀ hc₀
    cases hex : clausesStep n r₀ with
    | none =>
      have hfalse : b = false := by simpa [Realizes, hex] using hspec
      subst b
      have hfailed := exec_seq_failure (whileCounter outer clause) (testEmpty input) he
      have hfull := exec_seq (readUnary input outer)
        (seq (whileCounter outer clause) (testEmpty input)) hread hfailed
      refine ⟨_, false, mid, ?_, hfull, ?_, by simp⟩
      · have hm := Nat.mul_le_mul_right (clauseBudget bound capacity + 1) hn
        unfold parseBudget
        omega
      · simp only [parseCNFStep, hp]
        change Realizes ((clausesStep n r₀).bind _) false mid
        simp [hex, Realizes]
    | some q =>
      have hs : b = true ∧ mid = q := by simpa [Realizes, hex] using hspec
      obtain ⟨rfl, rfl⟩ := hs
      obtain ⟨hbm, _, _, _⟩ := hsuccess rfl
      have hend := exec_testEmpty input mid
      have hfull := exec_seq (readUnary input outer)
        (seq (whileCounter outer clause) (testEmpty input)) hread
        (exec_seq (whileCounter outer clause) (testEmpty input) he hend)
      refine ⟨_, (mid input).isEmpty, mid, ?_, hfull, ?_, ?_⟩
      · have hm := Nat.mul_le_mul_right (clauseBudget bound capacity + 1) hn
        unfold parseBudget
        omega
      · simp only [parseCNFStep, hp]
        change Realizes ((clausesStep n r₀).bind _) (mid input).isEmpty mid
        simp only [hex, Option.bind_some]
        cases hh : (mid input).isEmpty <;> simp [Realizes]
      · intro hh
        exact ⟨hbm, List.isEmpty_iff.mp hh⟩


/-- Send each terminal decision to an explicit finite continuation. -/
def branchResult {k : Nat} {A B C : Type} (p : Program k A)
    (yes : Program k B) (no : Program k C) : Program k (Sum A (Sum B C)) where
  start := .inl p.start
  code q := match q with
    | .inl a => mapOp Sum.inl
        (fun b => if b then .goto (.inr (.inl yes.start)) else .goto (.inr (.inr no.start))) (p.code a)
    | .inr (.inl b) => mapOp (fun b => .inr (.inl b)) Op.halt (yes.code b)
    | .inr (.inr c) => mapOp (fun c => .inr (.inr c)) Op.halt (no.code c)

theorem branchResult_step {k : Nat} {A B C : Type} (p : Program k A)
    (yes : Program k B) (no : Program k C) (q : A) (r : Registers k) :
    StackProgram.step (branchResult p yes no) (.inl q) r =
      match StackProgram.step p q r with
      | .inl (b, out) => .inr ((if b then .inr (.inl yes.start) else .inr (.inr no.start)), out)
      | .inr (next, out) => .inr (.inl next, out) := by
  cases hp : p.code q with
  | halt b => cases b <;> simp [StackProgram.step, branchResult, mapOp, hp]
  | goto a => simp [StackProgram.step, branchResult, mapOp, hp]
  | push j b a => simp [StackProgram.step, branchResult, mapOp, hp]
  | pop j a b c => simp [StackProgram.step, branchResult, mapOp, hp, branch_map]
  | peek j a b c => simp [StackProgram.step, branchResult, mapOp, hp, branch_map]

theorem exec_branchResult_true {k : Nat} {A B C : Type} (p : Program k A)
    (yes : Program k B) (no : Program k C) {q r t middle s result}
    (he : Exec p q r t (true, middle)) (hy : Exec yes yes.start middle s result) :
    Exec (branchResult p yes no) (.inl q) r (t + s) result := by
  apply exec_link p (branchResult p yes no) Sum.inl he
  · intro a r a' r' hh
    rw [branchResult_step, hh]
  · intro a r hh
    have hr : r = middle := by
      cases hp : p.code a <;> simp [StackProgram.step, hp] at hh
      exact hh.2
    subst r
    apply Exec.next (q' := .inr (.inl yes.start)) (r' := middle)
    · simp [branchResult_step, hh]
    · exact exec_embed yes (branchResult p yes no) (fun b => .inr (.inl b))
        (by intro b; rfl) hy

theorem exec_branchResult_false {k : Nat} {A B C : Type} (p : Program k A)
    (yes : Program k B) (no : Program k C) {q r t middle s result}
    (he : Exec p q r t (false, middle)) (hn : Exec no no.start middle s result) :
    Exec (branchResult p yes no) (.inl q) r (t + s) result := by
  apply exec_link p (branchResult p yes no) Sum.inl he
  · intro a r a' r' hh
    rw [branchResult_step, hh]
  · intro a r hh
    have hr : r = middle := by
      cases hp : p.code a <;> simp [StackProgram.step, hp] at hh
      exact hh.2
    subst r
    apply Exec.next (q' := .inr (.inr no.start)) (r' := middle)
    · simp [branchResult_step, hh]
    · exact exec_embed no (branchResult p yes no) (fun c => .inr (.inr c))
        (by intro c; rfl) hn

abbrev SuccessLabel := Sum PrependNatLabel (Sum Bool (Sum (Fin 4) (Fin 6)))
def finishSuccess : Program 7 SuccessLabel :=
  seq (prependNat count output scratch) (copy output input scratch)
def finishSuccessEncoding : Encoding SuccessLabel := prependNatEncoding.sum copyMapEncoding

def successFinish (r : Registers 7) : Registers 7 :=
  set (set r output (writeNat (r count).length ++ r output)) input
    (writeNat (r count).length ++ r output)

def successTime (r : Registers 7) :=
  (r input).length + 10 * (r count).length + 5 * (r output).length + 17

theorem finishSuccess_runs (r : Registers 7) (hs : r scratch = []) :
    Exec finishSuccess finishSuccess.start r (successTime r) (true, successFinish r) := by
  let r₀ := set r output (writeNat (r count).length ++ r output)
  have h₀ := exec_prependNat count output scratch (by decide) (by decide) (by decide) r hs
  have hs₀ : r₀ scratch = [] := by simpa [r₀, scratch, output] using hs
  have h₁ := exec_copy output input scratch (by decide) (by decide) (by decide) r₀ hs₀
  have he := exec_seq (prependNat count output scratch) (copy output input scratch) h₀ h₁
  have ht : 5 * (r count).length + 6 +
      ((r₀ input).length + 5 * (r₀ output).length + 6) = successTime r := by
    simp [r₀, input, output, successTime, SATBounds.writeNat_length, Nat.mul_add]
    omega
  rw [ht] at he
  exact he

abbrev FailureLabel := Sum Bool (Fin 4)
def finishFailure : Program 7 FailureLabel :=
  seq (clear input) (prependWord input (encode [[]]))
def finishFailureEncoding : Encoding FailureLabel := Encoding.bool.sum (Encoding.fin 3)

theorem finishFailure_runs (r : Registers 7) :
    Exec finishFailure finishFailure.start r ((r input).length + 6)
      (true, set r input (encode [[]])) := by
  have he := exec_seq (clear input) (prependWord input (encode [[]]))
    (exec_clear input r) (exec_prependWord input (encode [[]]) (set r input []))
  have ho : set (set r input []) input (encode [[]] ++ (set r input []) input) =
      set r input (encode [[]]) := by simp [set_overwrite]
  rw [ho] at he
  have ht : (r input).length + 2 + ((encode [[]]).length + 1) =
      (r input).length + 6 := by rfl
  rw [ht] at he
  exact he

abbrev TransformLabel := Sum ParseCNFLabel (Sum SuccessLabel FailureLabel)
def transform : Program 7 TransformLabel := branchResult parseCNF finishSuccess finishFailure
def transformEncoding : Encoding TransformLabel :=
  parseCNFEncoding.sum (finishSuccessEncoding.sum finishFailureEncoding)

def transformedWord (r : Registers 7) : Word :=
  match parseCNFStep r with
  | none => encode [[]]
  | some out => writeNat (out count).length ++ out output

theorem exec_length_le {k : Nat} {L : Type} (p : Program k L) (e : Encoding L)
    {q r t result} (he : Exec p q r t result) (bound : Nat)
    (hb : ∀ j, (r j).length ≤ bound) : ∀ j, (result.2 j).length ≤ bound + t :=
  StackMachine.run_length_le (compile p e) t ⟨e.encode q, r⟩ result
    (compile_exec e he) bound hb

def transformBudget (bound capacity : Nat) := 16 * parseBudget bound capacity + 15 * bound + 17

theorem transform_runs (bound capacity : Nat) (r : Registers 7)
    (hs : r scratch = []) (hb : ∀ j, (r j).length ≤ bound)
    (hc : (r fresh).length + bound * (bound + 1) + bound ≤ capacity) :
    ∃ t out, t ≤ transformBudget bound capacity ∧
      Exec transform transform.start r t (true, out) ∧ out input = transformedWord r := by
  have hbounded : Bounded bound r := ⟨hb input, hb work, hs⟩
  obtain ⟨t, b, mid, ht, he, hspec, hsuccess⟩ := parseCNF_runs bound capacity r hbounded
    (hb inner) (hb outer) hc
  have hsize := exec_length_le parseCNF parseCNFEncoding he bound hb
  cases hp : parseCNFStep r with
  | none =>
    have hfalse : b = false := by simpa [Realizes, hp] using hspec
    subst b
    have hfull := exec_branchResult_false parseCNF finishSuccess finishFailure he (finishFailure_runs mid)
    refine ⟨t + ((mid input).length + 6), set mid input (encode [[]]), ?_, hfull, ?_⟩
    · have hi := hsize input
      change (mid input).length ≤ bound + t at hi
      unfold transformBudget
      omega
    · simp [transformedWord, hp]
  | some q =>
    have hs : b = true ∧ mid = q := by simpa [Realizes, hp] using hspec
    obtain ⟨rfl, rfl⟩ := hs
    obtain ⟨hbm, him⟩ := hsuccess rfl
    have hfull := exec_branchResult_true parseCNF finishSuccess finishFailure he
      (finishSuccess_runs mid hbm.scratch_eq)
    refine ⟨t + successTime mid, successFinish mid, ?_, hfull, ?_⟩
    · have hn := hsize count
      have ho := hsize output
      change (mid count).length ≤ bound + t at hn
      change (mid output).length ≤ bound + t at ho
      simp only [successTime, him, List.length_nil, Nat.zero_add]
      unfold transformBudget
      omega
    · simp [successFinish, transformedWord, hp]

abbrev ReducerLabel := Sum (Sum Bool (Sum (Fin 4) (Fin 6))) TransformLabel

def reducer : Program 7 ReducerLabel := seq (length input fresh scratch) transform

def reducerEncoding : Encoding ReducerLabel := copyMapEncoding.sum transformEncoding

def initialRegisters (word : Word) : Registers 7 := fun j => if j = input then word else []

def preparedRegisters (word : Word) : Registers 7 :=
  set (initialRegisters word) fresh (List.replicate word.length true)

def reduceWord (word : Word) : Word := transformedWord (preparedRegisters word)

def capacity (n : Nat) := n + n * (n + 1) + n

def reducerBudget (n : Nat) := 5 * n + 6 + transformBudget n (capacity n)

theorem reducer_runs (word : Word) :
    ∃ t out, t ≤ reducerBudget word.length ∧
      Exec reducer reducer.start (initialRegisters word) t (true, out) ∧
      out input = reduceWord word := by
  have hs : initialRegisters word scratch = [] := by simp [initialRegisters, scratch, input]
  have hinit := exec_length input fresh scratch (by decide) (by decide) (by decide)
    (initialRegisters word) hs
  have ht : ((initialRegisters word) fresh).length + 5 * ((initialRegisters word) input).length + 6 =
      5 * word.length + 6 := by simp [initialRegisters, fresh, input]
  rw [ht] at hinit
  have hinit' : Exec (length input fresh scratch) (length input fresh scratch).start
      (initialRegisters word) (5 * word.length + 6) (true, preparedRegisters word) := by
    change Exec (length input fresh scratch) (.inl false)
      (initialRegisters word) (5 * word.length + 6) (true, preparedRegisters word)
    simpa [preparedRegisters, initialRegisters, input] using hinit
  have hs' : preparedRegisters word scratch = [] := by
    simp [preparedRegisters, initialRegisters, scratch, fresh, input]
  have hbound : ∀ j, (preparedRegisters word j).length ≤ word.length := by
    intro j
    by_cases hf : j = fresh
    · subst j; simp [preparedRegisters]
    · by_cases hi : j = input
      · subst j; simp [preparedRegisters, initialRegisters, input, fresh]
      · simp [preparedRegisters, initialRegisters, hf, hi]
  have hcap : ((preparedRegisters word) fresh).length + word.length * (word.length + 1) + word.length ≤
      capacity word.length := by simp [preparedRegisters, capacity]
  obtain ⟨t, out, ht, he, ho⟩ := transform_runs word.length (capacity word.length)
    (preparedRegisters word) hs' hbound hcap
  refine ⟨5 * word.length + 6 + t, out, ?_, exec_seq (length input fresh scratch) transform hinit' he, ho⟩
  unfold reducerBudget
  omega


theorem reducerBudget_polynomial (n : Nat) : reducerBudget n ≤ 4096 * (n + 1) ^ 4 := by
  simp only [reducerBudget, transformBudget, parseBudget, clauseBudget, capacity,
    Nat.pow_succ, Nat.pow_zero, Nat.mul_one, Nat.mul_add, Nat.add_mul, Nat.one_mul,
    Nat.add_assoc, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
  simp only [← Nat.mul_assoc, Nat.reduceMul]
  omega

def machine : StackMachine.Machine := compile reducer reducerEncoding

theorem machine_runs (word : Word) :
    ∃ out, StackMachine.runInput machine (4096 * (word.length + 1) ^ 4) word =
      some (true, out) ∧ StackMachine.output out = reduceWord word := by
  obtain ⟨t, out, ht, he, ho⟩ := reducer_runs word
  have hr := compile_exec reducerEncoding he
  have hbound := Nat.le_trans ht (reducerBudget_polynomial word.length)
  have hm := StackMachine.run_mono machine hbound
    ⟨reducerEncoding.encode reducer.start, initialRegisters word⟩ (true, out) hr
  refine ⟨out, ?_, ?_⟩
  · exact hm
  · exact ho

end Complexity.StackThreeSAT
