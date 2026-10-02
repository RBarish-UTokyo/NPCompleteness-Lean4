module

public import Complexity.Binary.ReductionMachine
public import Complexity.PolynomialBound
import Lean.Elab.Tactic.Omega

/-!
# The clause and formula loops of the SAT to binary SAT transducer

The literal program of `ReductionMachine` is iterated over the literals of a clause, the
clause program over the clauses of the formula; a final program moves the result into
register 0, and malformed words produce one empty clause. The complete stack machine halts
on every word within `transformCost` instructions, a polynomial in the input length.
-/

@[expose] public section

namespace Complexity.Binary.Reduce

open Complexity.StackMachine (Registers set)
open Complexity.StackProgram Complexity.StackWords Complexity.StackParse
open Complexity.SAT
open Complexity.Binary

/-! ## One clause -/

/-- Invariant of the literal loop: clean work registers, and every counted literal has
consumed at least one input bit. -/
structure LitInv (bound : Nat) (o : Word) (q : Registers 10) : Prop where
  clean : Clean q
  size : (q input).length + (q litCount).length ≤ bound
  outer_eq : q outer = o

theorem LitInv.set_inner {bound : Nat} {o : Word} {q : Registers 10} (h : LitInv bound o q)
    (xs : Word) : LitInv bound o (StackMachine.set q inner xs) := by
  constructor
  · exact h.clean.set inner (by decide) (by decide) (by decide) (by decide) (by decide) xs
  · simpa using h.size
  · simpa using h.outer_eq

theorem LitInv.step {bound : Nat} {o : Word} {q out : Registers 10} (h : LitInv bound o q)
    (hs : litStep q = some out) : LitInv bound o out ∧ out inner = q inner := by
  unfold litStep at hs
  cases hp : readLiteral (q input) with
  | none => simp [hp] at hs
  | some pair =>
    obtain ⟨l, rest⟩ := pair
    simp only [hp, Option.some.injEq] at hs
    subst hs
    have hlen := congrArg List.length (readLiteral_eq_some hp)
    simp only [List.length_append, SATBounds.encodeLiteral_length] at hlen
    have hsize := h.size
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
    · exact ((h.clean.set input (by decide) (by decide) (by decide) (by decide) (by decide) _).set
        output (by decide) (by decide) (by decide) (by decide) (by decide) _).set
        litCount (by decide) (by decide) (by decide) (by decide) (by decide) _
    · simp [litFinish] at hsize hlen ⊢; omega
    · simpa [litFinish] using h.outer_eq
    · simp [litFinish]

theorem literals_runs (bound : Nat) (o : Word) (m : Nat) (r : Registers 10)
    (hI : LitInv bound o r) (hr : r inner = List.replicate m true) :
    ∃ t b out, t ≤ m * (litCost bound + 1) + 2 ∧
      Exec (whileCounter inner literal) (.inl false) r t (b, out) ∧
      Realizes (iterStep inner litStep m r) b out :=
  whileCounter_iter literal inner litStep (LitInv bound o) (litCost bound)
    (fun _ tail hq _ => hq.set_inner tail)
    (fun q hq => literal_runs bound q hq.clean (by have := hq.size; omega))
    (fun _ _ hq hs => hq.step hs) m r hr hI

theorem literals_invariant (bound : Nat) (o : Word) (m : Nat) (r : Registers 10)
    (hI : LitInv bound o r) (hr : r inner = List.replicate m true) (out : Registers 10)
    (h : iterStep inner litStep m r = some out) : LitInv bound o out ∧ out inner = [] :=
  iterStep_invariant inner litStep (LitInv bound o) (fun _ tail hq _ => hq.set_inner tail)
    (fun _ _ hq hs => hq.step hs) m r hr hI out h

/-- Read a literal count, emit all literals, then prepend the count; count the clause. -/
def clauseProg :=
  seq (readUnary input inner)
  (seq (whileCounter inner literal)
  (seq (push output false)
  (seq (transfer litCount output) (push clauseCount true))))

def clauseEncoding :=
  readUnaryEncoding.sum ((Encoding.bool.sum literalEncoding).sum
    (Encoding.bool.sum ((Encoding.fin 3).sum Encoding.bool)))

def clauseFinish (q : Registers 10) : Registers 10 :=
  StackMachine.set (StackMachine.set (StackMachine.set q output
    ((q litCount).reverse ++ false :: q output)) litCount []) clauseCount (true :: q clauseCount)

/-- The partial register semantics of `clauseProg`. -/
def clauseStep (r : Registers 10) : Option (Registers 10) :=
  match readNat (r input) with
  | none => none
  | some (m, rest) =>
    (iterStep inner litStep m (StackMachine.set (StackMachine.set r input rest) inner
      (List.replicate m true))).map clauseFinish

def clauseCost (bound : Nat) : Nat := bound * (litCost bound + 1) + 5 * bound + 12

/-- Invariant of the clause loop. -/
structure ClauseInv (bound : Nat) (q : Registers 10) : Prop where
  clean : Clean q
  lit_eq : q litCount = []
  size : (q input).length ≤ bound
  inner_le : (q inner).length ≤ bound

theorem ClauseInv.literals {bound : Nat} {q : Registers 10} (h : ClauseInv bound q) (m : Nat)
    (rest : Word) (hrest : rest.length ≤ bound) :
    LitInv bound (q outer)
      (StackMachine.set (StackMachine.set q input rest) inner (List.replicate m true)) := by
  constructor
  · exact (h.clean.set input (by decide) (by decide) (by decide) (by decide) (by decide)
      _).set inner (by decide) (by decide) (by decide) (by decide) (by decide) _
  · simp [h.lit_eq]; omega
  · simp

theorem clause_runs (bound : Nat) (r : Registers 10) (hI : ClauseInv bound r) :
    ∃ t b out, t ≤ clauseCost bound ∧ Exec clauseProg clauseProg.start r t (b, out) ∧
      Realizes (clauseStep r) b out := by
  have hb := hI.size
  have hi := hI.inner_le
  cases hp : readNat (r input) with
  | none =>
    have he := exec_readUnary_malformed input inner (by decide) (r input).length r
      (readNat_none_eq hp)
    have hf := exec_seq_failure _ (seq (whileCounter inner literal) (seq (push output false)
      (seq (transfer litCount output) (push clauseCount true)))) he
    refine ⟨_, false, _, ?_, hf, by simp [clauseStep, hp]⟩
    unfold clauseCost
    omega
  | some pair =>
    obtain ⟨m, rest⟩ := pair
    have hlen := congrArg List.length (readNat_eq_some hp)
    simp only [List.length_append, SATBounds.writeNat_length] at hlen
    have hm : m ≤ bound := by omega
    have hread := exec_readUnary_encoded input inner (by decide) m rest r (readNat_eq_some hp)
    let r₁ := StackMachine.set (StackMachine.set r input rest) inner (List.replicate m true)
    have hI₁ : LitInv bound (r outer) r₁ := hI.literals m rest (by omega)
    obtain ⟨t, b, mid, ht, he, hspec⟩ := literals_runs bound (r outer) m r₁ hI₁ (by simp [r₁])
    have hloopCost : m * (litCost bound + 1) ≤ bound * (litCost bound + 1) :=
      Nat.mul_le_mul_right _ hm
    cases hex : iterStep inner litStep m r₁ with
    | none =>
      have hfalse : b = false := by simpa [hex] using hspec
      subst b
      have hfull := exec_seq _ _ hread (exec_seq_failure _ (seq (push output false)
        (seq (transfer litCount output) (push clauseCount true))) he)
      refine ⟨_, false, mid, ?_, hfull, by simp [clauseStep, hp, r₁, hex]⟩
      unfold clauseCost
      omega
    | some q =>
      have hs : b = true ∧ mid = q := by simpa [hex] using hspec
      obtain ⟨rfl, rfl⟩ := hs
      obtain ⟨hIq, _⟩ := literals_invariant bound (r outer) m r₁ hI₁ (by simp [r₁]) mid hex
      have h₁ := exec_push output false mid
      let q₁ := StackMachine.set mid output (false :: mid output)
      have h₂ := exec_transfer litCount output (by decide) q₁
      let q₂ := StackMachine.set (StackMachine.set q₁ litCount []) output
        ((q₁ litCount).reverse ++ q₁ output)
      have h₃ := exec_push clauseCount true q₂
      have hfull := exec_seq _ _ hread (exec_seq _ _ he (exec_seq _ _ h₁ (exec_seq _ _ h₂ h₃)))
      have hout : StackMachine.set q₂ clauseCount (true :: q₂ clauseCount) =
          clauseFinish mid := by
        apply regs_ext <;> simp [q₂, q₁, clauseFinish]
      rw [hout] at hfull
      refine ⟨_, true, _, ?_, hfull, by simp [clauseStep, hp, r₁, hex]⟩
      have hlc : (q₁ litCount).length ≤ bound := by
        have := hIq.size
        simp only [q₁, StackMachine.set_other _ (by decide : litCount ≠ output)]
        omega
      unfold clauseCost
      omega

theorem ClauseInv.set_outer {bound : Nat} {q : Registers 10} (h : ClauseInv bound q)
    (xs : Word) : ClauseInv bound (StackMachine.set q outer xs) := by
  constructor
  · exact h.clean.set outer (by decide) (by decide) (by decide) (by decide) (by decide) xs
  · simpa using h.lit_eq
  · simpa using h.size
  · simpa using h.inner_le

theorem ClauseInv.step {bound : Nat} {q out : Registers 10} (h : ClauseInv bound q)
    (hs : clauseStep q = some out) : ClauseInv bound out ∧ out outer = q outer := by
  unfold clauseStep at hs
  cases hp : readNat (q input) with
  | none => simp [hp] at hs
  | some pair =>
    obtain ⟨m, rest⟩ := pair
    simp only [hp] at hs
    have hlen := congrArg List.length (readNat_eq_some hp)
    simp only [List.length_append, SATBounds.writeNat_length] at hlen
    have hsize := h.size
    let r₁ := StackMachine.set (StackMachine.set q input rest) inner (List.replicate m true)
    have hI₁ : LitInv bound (q outer) r₁ := h.literals m rest (by omega)
    cases hex : iterStep inner litStep m r₁ with
    | none =>
      have hex' : iterStep inner litStep m (StackMachine.set (StackMachine.set q input rest)
          inner (List.replicate m true)) = none := hex
      simp [hex'] at hs
    | some mid =>
      have hex' : iterStep inner litStep m (StackMachine.set (StackMachine.set q input rest)
          inner (List.replicate m true)) = some mid := hex
      simp only [hex', Option.map_some, Option.some.injEq] at hs
      subst hs
      obtain ⟨hIm, hinner⟩ := literals_invariant _ _ m r₁ hI₁ (by simp [r₁]) mid hex
      have hmsize := hIm.size
      refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
      · exact ((hIm.clean.set output (by decide) (by decide) (by decide) (by decide) (by decide)
          _).set litCount (by decide) (by decide) (by decide) (by decide) (by decide) _).set
          clauseCount (by decide) (by decide) (by decide) (by decide) (by decide) _
      · simp [clauseFinish]
      · simp [clauseFinish] at hmsize ⊢; omega
      · simp [clauseFinish, hinner]
      · simpa [clauseFinish] using hIm.outer_eq

theorem clauses_runs (bound n : Nat) (r : Registers 10) (hI : ClauseInv bound r)
    (hr : r outer = List.replicate n true) :
    ∃ t b out, t ≤ n * (clauseCost bound + 1) + 2 ∧
      Exec (whileCounter outer clauseProg) (.inl false) r t (b, out) ∧
      Realizes (iterStep outer clauseStep n r) b out :=
  whileCounter_iter clauseProg outer clauseStep (ClauseInv bound) (clauseCost bound)
    (fun _ tail hq _ => hq.set_outer tail) (fun q hq => clause_runs bound q hq)
    (fun _ _ hq hs => hq.step hs) n r hr hI

theorem clauses_invariant (bound n : Nat) (r : Registers 10) (hI : ClauseInv bound r)
    (hr : r outer = List.replicate n true) (out : Registers 10)
    (h : iterStep outer clauseStep n r = some out) : ClauseInv bound out ∧ out outer = [] :=
  iterStep_invariant outer clauseStep (ClauseInv bound) (fun _ tail hq _ => hq.set_outer tail)
    (fun _ _ hq hs => hq.step hs) n r hr hI out h

/-! ## The formula -/

/-- Read the clause count, emit all clauses, and require the input to be used up. -/
def parse :=
  seq (readUnary input outer) (seq (whileCounter outer clauseProg) (testEmpty input true false))

def parseEncoding :=
  readUnaryEncoding.sum ((Encoding.bool.sum clauseEncoding).sum (Encoding.fin 2))

/-- The partial register semantics of `parse`. -/
def parseStep (r : Registers 10) : Option (Registers 10) :=
  match readNat (r input) with
  | none => none
  | some (n, rest) =>
    match iterStep outer clauseStep n (StackMachine.set (StackMachine.set r input rest) outer
        (List.replicate n true)) with
    | none => none
    | some q => if (q input).isEmpty then some q else none

def parseCost (bound : Nat) : Nat := bound * (clauseCost bound + 1) + 3 * bound + 8

theorem parse_runs (bound : Nat) (r : Registers 10) (hI : ClauseInv bound r)
    (ho : (r outer).length ≤ bound) :
    ∃ t b out, t ≤ parseCost bound ∧ Exec parse parse.start r t (b, out) ∧
      Realizes (parseStep r) b out ∧ (b = true → Clean out ∧ out input = []) := by
  have hb := hI.size
  cases hp : readNat (r input) with
  | none =>
    have he := exec_readUnary_malformed input outer (by decide) (r input).length r
      (readNat_none_eq hp)
    have hf := exec_seq_failure _ (seq (whileCounter outer clauseProg)
      (testEmpty input true false)) he
    refine ⟨_, false, _, ?_, hf, by simp [parseStep, hp], by simp⟩
    unfold parseCost
    omega
  | some pair =>
    obtain ⟨n, rest⟩ := pair
    have hlen := congrArg List.length (readNat_eq_some hp)
    simp only [List.length_append, SATBounds.writeNat_length] at hlen
    have hn : n ≤ bound := by omega
    have hread := exec_readUnary_encoded input outer (by decide) n rest r (readNat_eq_some hp)
    let r₁ := StackMachine.set (StackMachine.set r input rest) outer (List.replicate n true)
    have hI₁ : ClauseInv bound r₁ := by
      constructor
      · exact (hI.clean.set input (by decide) (by decide) (by decide) (by decide) (by decide)
          _).set outer (by decide) (by decide) (by decide) (by decide) (by decide) _
      · simpa [r₁] using hI.lit_eq
      · simp [r₁]; omega
      · simpa [r₁] using hI.inner_le
    obtain ⟨t, b, mid, ht, he, hspec⟩ := clauses_runs bound n r₁ hI₁ (by simp [r₁])
    have hloopCost : n * (clauseCost bound + 1) ≤ bound * (clauseCost bound + 1) :=
      Nat.mul_le_mul_right _ hn
    cases hex : iterStep outer clauseStep n r₁ with
    | none =>
      have hfalse : b = false := by simpa [hex] using hspec
      subst b
      have hfull := exec_seq _ _ hread (exec_seq_failure _ (testEmpty input true false) he)
      refine ⟨_, false, mid, ?_, hfull, by simp [parseStep, hp, r₁, hex], by simp⟩
      unfold parseCost
      omega
    | some q =>
      have hs : b = true ∧ mid = q := by simpa [hex] using hspec
      obtain ⟨rfl, rfl⟩ := hs
      obtain ⟨hIq, _⟩ := clauses_invariant bound n r₁ hI₁ (by simp [r₁]) mid hex
      have htest := exec_testEmpty input true false mid
      have hfull := exec_seq _ _ hread (exec_seq _ _ he htest)
      refine ⟨_, _, mid, ?_, hfull, ?_, ?_⟩
      · unfold parseCost
        omega
      · have hex' : iterStep outer clauseStep n (StackMachine.set (StackMachine.set r input rest)
            outer (List.replicate n true)) = some mid := hex
        simp only [parseStep, hp, hex']
        cases hh : (mid input).isEmpty <;> simp
      · intro htrue
        refine ⟨hIq.clean, ?_⟩
        cases hh : (mid input).isEmpty
        · simp [hh] at htrue
        · exact List.isEmpty_iff.mp hh

/-! ## Output and malformed inputs -/

/-- Prepend the clause count, then move the output into register 0. -/
def success :=
  seq (push output false) (seq (transfer clauseCount output)
    (seq (transfer output temp) (transfer temp input)))

def successEncoding :=
  Encoding.bool.sum ((Encoding.fin 3).sum ((Encoding.fin 3).sum (Encoding.fin 3)))

theorem success_runs (q : Registers 10) (ht : q temp = []) (hi : q input = []) :
    ∃ t out, t ≤ 6 * (q clauseCount).length + 4 * (q output).length + 12 ∧
      Exec success success.start q t (true, out) ∧
      out input = (q clauseCount).reverse ++ false :: q output := by
  have h₁ := exec_push output false q
  let q₁ := StackMachine.set q output (false :: q output)
  have h₂ := exec_transfer clauseCount output (by decide) q₁
  let q₂ := StackMachine.set (StackMachine.set q₁ clauseCount []) output
    ((q₁ clauseCount).reverse ++ q₁ output)
  have h₃ := exec_transfer output temp (by decide) q₂
  let q₃ := StackMachine.set (StackMachine.set q₂ output []) temp
    ((q₂ output).reverse ++ q₂ temp)
  have h₄ := exec_transfer temp input (by decide) q₃
  have hfull := exec_seq _ _ h₁ (exec_seq _ _ h₂ (exec_seq _ _ h₃ h₄))
  refine ⟨_, _, ?_, hfull, ?_⟩
  · simp [q₃, q₂, q₁, ht]
    omega
  · simp [q₃, q₂, q₁, ht, hi]

/-- On a malformed word, output one empty clause. -/
def failure :=
  seq (clear input) (Complexity.StackThreeSAT.prependWord input (encodeBinary [[]]))

def failureEncoding :=
  Encoding.bool.sum (Complexity.StackThreeSAT.prependWordEncoding (encodeBinary [[]]))

theorem failure_runs (q : Registers 10) :
    Exec failure failure.start q ((q input).length + 6)
      (true, StackMachine.set q input (encodeBinary [[]])) := by
  have he := exec_seq _ _ (exec_clear input q)
    (Complexity.StackThreeSAT.exec_prependWord input (encodeBinary [[]])
      (StackMachine.set q input []))
  have ho : StackMachine.set (StackMachine.set q input []) input
      (encodeBinary [[]] ++ (StackMachine.set q input []) input) =
      StackMachine.set q input (encodeBinary [[]]) := by simp
  rw [ho] at he
  exact he

/-- The complete transducer. -/
def transform := Complexity.StackThreeSAT.branchResult parse success failure

def transformEncoding := parseEncoding.sum (successEncoding.sum failureEncoding)

def transformedWord (r : Registers 10) : Word :=
  match parseStep r with
  | none => encodeBinary [[]]
  | some q => (q clauseCount).reverse ++ false :: q output

def transformCost (bound : Nat) : Nat := parseCost bound + 10 * (bound + parseCost bound) + 20

theorem transform_runs (bound : Nat) (r : Registers 10) (hI : ClauseInv bound r)
    (hall : ∀ j, (r j).length ≤ bound) :
    ∃ t out, t ≤ transformCost bound ∧ Exec transform transform.start r t (true, out) ∧
      out input = transformedWord r := by
  obtain ⟨t, b, mid, ht, he, hspec, hgood⟩ := parse_runs bound r hI (hall outer)
  have hsize := Complexity.StackThreeSAT.exec_length_le parse parseEncoding he bound hall
  cases hp : parseStep r with
  | none =>
    have hfalse : b = false := by simpa [hp] using hspec
    subst b
    have hfull := Complexity.StackThreeSAT.exec_branchResult_false parse success failure he
      (failure_runs mid)
    refine ⟨_, _, ?_, hfull, by simp [transformedWord, hp]⟩
    have hi := hsize input
    simp only at hi
    unfold transformCost
    omega
  | some q =>
    have hs : b = true ∧ mid = q := by simpa [hp] using hspec
    obtain ⟨rfl, rfl⟩ := hs
    obtain ⟨hclean, hin⟩ := hgood rfl
    obtain ⟨s, out, hs, hsucc, hout⟩ := success_runs mid hclean.temp_eq hin
    have hfull := Complexity.StackThreeSAT.exec_branchResult_true parse success failure he hsucc
    refine ⟨_, out, ?_, hfull, by simp [transformedWord, hp, hout]⟩
    have hc := hsize clauseCount
    have ho := hsize output
    simp only at hc ho
    unfold transformCost
    omega

/-! ## The machine -/

def initialRegisters (word : Word) : Registers 10 := fun j => if j = 0 then word else []

def machine : StackMachine.Machine := compile transform transformEncoding

theorem polynomialBound_transformCost : PolynomialBound transformCost := by
  have hlit : PolynomialBound litCost :=
    (((PolynomialBound.identity.mul (((PolynomialBound.constant 4).mul
      PolynomialBound.identity).add (PolynomialBound.constant 5))).add
      ((PolynomialBound.constant 11).mul PolynomialBound.identity)).add
      (PolynomialBound.constant 21)).weaken (fun _ => Nat.le_refl _)
  have hclause : PolynomialBound clauseCost :=
    (((PolynomialBound.identity.mul (hlit.add (PolynomialBound.constant 1))).add
      ((PolynomialBound.constant 5).mul PolynomialBound.identity)).add
      (PolynomialBound.constant 12)).weaken (fun _ => Nat.le_refl _)
  have hparse : PolynomialBound parseCost :=
    (((PolynomialBound.identity.mul (hclause.add (PolynomialBound.constant 1))).add
      ((PolynomialBound.constant 3).mul PolynomialBound.identity)).add
      (PolynomialBound.constant 8)).weaken (fun _ => Nat.le_refl _)
  exact ((hparse.add ((PolynomialBound.constant 10).mul
    (PolynomialBound.identity.add hparse))).add (PolynomialBound.constant 20)).weaken
    (fun _ => Nat.le_refl _)

theorem machine_runs (word : Word) :
    ∃ out, StackMachine.runInput machine (transformCost word.length) word = some (true, out) ∧
      out 0 = transformedWord (initialRegisters word) := by
  have hI : ClauseInv word.length (initialRegisters word) := by
    constructor
    · constructor <;> rfl
    · rfl
    · simp [initialRegisters]
    · simp [initialRegisters]
  have hall : ∀ j, (initialRegisters word j).length ≤ word.length := by
    intro j
    unfold initialRegisters
    split <;> simp
  obtain ⟨t, out, ht, he, ho⟩ := transform_runs word.length (initialRegisters word) hI hall
  refine ⟨out, ?_, ho⟩
  have hr := compile_exec transformEncoding he
  exact StackMachine.run_mono machine ht _ _ hr

end Complexity.Binary.Reduce
