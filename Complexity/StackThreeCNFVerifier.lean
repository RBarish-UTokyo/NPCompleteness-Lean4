module

public import Complexity.StackCNFVerifier
import Lean.Elab.Tactic.Omega

/-! A concrete polynomial-time stack verifier for the 3-CNF restriction. -/

@[expose] public section

namespace Complexity.StackThreeCNFVerifier

open Complexity.StackProgram Complexity.StackWords Complexity.StackParse
open Complexity.StackMachine (Registers branch)
open Complexity.StackCNFVerifier
open Complexity.SAT

def headerPrefix : Nat → Word → Option Word
  | _, [] => none
  | _, false :: rest => some rest
  | 0, true :: _ => none
  | n + 1, true :: rest => headerPrefix n rest

theorem headerPrefix_eq (cap : Nat) (w : Word) :
    headerPrefix cap w = (do
      let (n, rest) ← readNat w
      if n ≤ cap then some rest else none) := by
  induction w generalizing cap with
  | nil => simp [headerPrefix, readNat]
  | cons b w ih =>
    cases b with
    | false => simp [headerPrefix, readNat]
    | true =>
      cases cap with
      | zero =>
        cases hp : readNat w with
        | none => simp [headerPrefix, readNat, hp]
        | some result => obtain ⟨n, rest⟩ := result; simp [headerPrefix, readNat, hp]
      | succ cap =>
        rw [headerPrefix, ih]
        cases hp : readNat w with
        | none => simp [readNat, hp]
        | some result => obtain ⟨n, rest⟩ := result; simp [readNat, hp]

/-- Four pop states and two halts test a unary header of at most three. -/
def headerCheck : Program 6 (Fin 6) where
  start := 0
  code := fun q => if q.val < 4 then .pop work 5 4
      (if h : q.val < 3 then ⟨q.val + 1, by omega⟩ else 5)
    else if q = 4 then .halt true else .halt false

theorem headerCheck_at (cap : Nat) (hcap : cap ≤ 3) (r : Registers 6) :
    ∃ t b rest, t ≤ cap + 2 ∧ rest.length ≤ (r work).length ∧
      Exec headerCheck ⟨3 - cap, by omega⟩ r t (b, StackMachine.set r work rest) ∧
      (match headerPrefix cap (r work) with
        | none => b = false
        | some tail => b = true ∧ rest = tail) := by
  induction cap generalizing r with
  | zero =>
    cases hw : r work with
    | nil =>
      refine ⟨2, false, [], by omega, by simp, ?_, by simp [headerPrefix]⟩
      exact .next (q' := 5) (r' := StackMachine.set r work []) (by
          change Sum.inr (branch (r work) (5 : Fin 6) 4 5, StackMachine.set r work (r work).tail) = _
          simp [hw, branch])
        (.halt rfl)
    | cons b rest =>
      cases b with
      | false =>
        refine ⟨2, true, rest, by omega, by simp, ?_, by simp [headerPrefix]⟩
        exact .next (q' := 4) (r' := StackMachine.set r work rest) (by
          change Sum.inr (branch (r work) (5 : Fin 6) 4 5, StackMachine.set r work (r work).tail) = _
          simp [hw, branch])
          (.halt rfl)
      | true =>
        refine ⟨2, false, rest, by omega, by simp, ?_, by simp [headerPrefix]⟩
        exact .next (q' := 5) (r' := StackMachine.set r work rest) (by
          change Sum.inr (branch (r work) (5 : Fin 6) 4 5, StackMachine.set r work (r work).tail) = _
          simp [hw, branch])
          (.halt rfl)
  | succ cap ih =>
    have hcap' : cap ≤ 3 := by omega
    have hlt : 2 - cap < 3 := by omega
    have hlt4 : 2 - cap < 4 := by omega
    cases hw : r work with
    | nil =>
      refine ⟨2, false, [], by omega, by simp, ?_, by simp [headerPrefix]⟩
      exact .next (q' := 5) (r' := StackMachine.set r work []) (by simp [StackProgram.step, headerCheck, hw, branch, hlt4])
        (.halt rfl)
    | cons b rest =>
      cases b with
      | false =>
        refine ⟨2, true, rest, by omega, by simp, ?_, by simp [headerPrefix]⟩
        exact .next (q' := 4) (r' := StackMachine.set r work rest) (by simp [StackProgram.step, headerCheck, hw, branch, hlt4])
          (.halt rfl)
      | true =>
        let r' := StackMachine.set r work rest
        obtain ⟨t, b, tail, ht, hlen, he, hs⟩ := ih hcap' r'
        refine ⟨t + 1, b, tail, by omega, ?_, ?_, ?_⟩
        · simp only [r', StackMachine.set_same] at hlen
          simp only [List.length_cons]
          omega
        · have hstep : StackProgram.step headerCheck ⟨3 - (cap + 1), by omega⟩ r =
              .inr (⟨3 - cap, by omega⟩, r') := by
            simp [StackProgram.step, headerCheck, hw, branch, hlt4, hlt, r']
            omega
          have hh := Exec.next hstep he
          simpa [r'] using hh
        · simpa [hw, headerPrefix, r'] using hs

def precheck := seq (copy input work scratch) headerCheck
def precheckEncoding := copyMapEncoding.sum (Encoding.fin 5)

def precheckParser (w : Word) : Option Word := do
  let _ ← headerPrefix 3 w
  pure w

theorem precheck_runs (bound : Nat) (cert : Word) (r : Registers 6) (h : Bounded bound cert r) :
    ∃ t b out, t ≤ 6 * bound + 11 ∧ Exec precheck precheck.start r t (b, out) ∧
      ParserResult (fun q => q input) precheckParser r b out ∧
      (b = true → Bounded bound cert out ∧ out outer = r outer) := by
  let r₀ := StackMachine.set r work (r input)
  have hcopy : Exec (copy input work scratch) (copy input work scratch).start r
      ((r work).length + 5 * (r input).length + 6) (true, r₀) :=
    exec_copy input work scratch (by decide) (by decide) (by decide) r h.scratch_eq
  obtain ⟨t, b, tail, ht, htail, he, hs⟩ := headerCheck_at 3 (by decide) r₀
  have h₀work : r₀ work = r input := by simp [r₀]
  have hout : StackMachine.set r₀ work tail = StackMachine.set r work tail := by simp [r₀]
  have hseq := exec_seq (copy input work scratch) headerCheck hcopy he
  rw [hout] at hseq
  refine ⟨(r work).length + 5 * (r input).length + 6 + t, b, StackMachine.set r work tail,
    ?_, hseq, ?_, ?_⟩
  · have hi := h.stack_le input
    have hw := h.stack_le work
    omega
  · rw [h₀work] at hs
    cases hp : headerPrefix 3 (r input) with
    | none => simpa [ParserResult, precheckParser, hp] using hs
    | some rest =>
      have hb : b = true := (by simpa [hp] using hs : b = true ∧ tail = rest).1
      have hp0 : headerPrefix 3 (r 0) = some rest := hp
      simp [ParserResult, precheckParser, hp0, hb, input, work]
  · intro _
    constructor
    · apply h.set_counter work (by decide) (by decide) (by decide) (by decide)
      rw [h₀work] at htail
      exact Nat.le_trans htail (h.stack_le input)
    · simp [outer, work]

def threeClause := seq precheck (clause literalProgram)
def threeClauseEncoding := precheckEncoding.sum (clauseEncoding literalProgramEncoding)

def threeClauseParser (cert : Word) (w : Word) : Option Word := do
  let rest ← precheckParser w
  clauseParser cert rest

def threeClauseCost (bound : Nat) : Nat := 6 * bound + 11 + clauseCost bound

theorem threeClause_runs (bound : Nat) (cert : Word) (r : Registers 6) (h : Bounded bound cert r) :
    ∃ t b out, t ≤ threeClauseCost bound ∧ Exec threeClause threeClause.start r t (b, out) ∧
      ParserResult (fun q => q input) (threeClauseParser cert) r b out ∧
      (b = true → Bounded bound cert out ∧ out outer = r outer) := by
  obtain ⟨t, b, middle, ht, he, hs, hmid⟩ := precheck_runs bound cert r h
  cases hp : precheckParser (r input) with
  | none =>
    have hb : b = false := by simpa [ParserResult, hp] using hs
    subst b
    refine ⟨t, false, middle, by unfold threeClauseCost; omega,
      exec_seq_failure precheck (clause literalProgram) he, ?_, by simp⟩
    simp [ParserResult, threeClauseParser, hp]
  | some rest =>
    have hh : b = true ∧ middle input = rest := by simpa [ParserResult, hp] using hs
    obtain ⟨rfl, hinput⟩ := hh
    obtain ⟨hmBound, hmOuter⟩ := hmid rfl
    obtain ⟨s, b, out, hst, hse, hss, hso⟩ := clause_runs bound cert middle hmBound
    refine ⟨t + s, b, out, by unfold threeClauseCost; omega,
      exec_seq precheck (clause literalProgram) he hse, ?_, ?_⟩
    · simpa [ParserResult, threeClauseParser, hp, hinput] using hss
    · intro hb
      obtain ⟨hbnd, hout⟩ := hso hb
      exact ⟨hbnd, hout.trans hmOuter⟩

def clausePredicate (cert : Word) (c : Clause) : Bool :=
  decide (c.length ≤ 3) && evalClause (SATVerifier.assignment cert) c

theorem threeClauseParser_eq (cert : Word) (w : Word) :
    threeClauseParser cert w = (do
      let (c, rest) ← readClause w
      if clausePredicate cert c then some rest else none) := by
  cases hp : readNat w with
  | none => simp [threeClauseParser, precheckParser, headerPrefix_eq, clauseParser, readClause, readList, hp]
  | some pair =>
    obtain ⟨n, rest⟩ := pair
    cases hm : readMany readLiteral n rest with
    | none =>
      by_cases hn : n ≤ 3 <;>
        simp [threeClauseParser, precheckParser, headerPrefix_eq, clauseParser, readClause, readList, hp, hm, hn]
    | some result =>
      obtain ⟨c, tail⟩ := result
      have hlen : c.length = n :=
        (SATBounds.readMany_eq_some readLiteral encodeLiteral SATBounds.readLiteral_eq_some hm).1
      by_cases hn : n ≤ 3 <;>
        simp [threeClauseParser, precheckParser, headerPrefix_eq, clauseParser,
          readClause, readList, hp, hm, clausePredicate, hlen, hn]

theorem repeat_threeClauseParser (cert : Word) (n : Nat) (w : Word) :
    repeatParser (threeClauseParser cert) n w = (do
      let (clauses, rest) ← readMany readClause n w
      if clauses.all (clausePredicate cert) then some rest else none) := by
  induction n generalizing w with
  | zero => simp [repeatParser, readMany]
  | succ n ih =>
    cases hp : readClause w with
    | none => simp [repeatParser, threeClauseParser_eq, readMany, hp]
    | some result =>
      obtain ⟨c, tail⟩ := result
      cases hc : clausePredicate cert c with
      | false =>
        cases htail : readMany readClause n tail with
        | none => simp [repeatParser, threeClauseParser_eq, readMany, hp, hc, htail]
        | some result =>
          obtain ⟨clauses, rest⟩ := result
          simp [repeatParser, threeClauseParser_eq, readMany, hp, hc, htail]
      | true =>
        simp only [repeatParser, threeClauseParser_eq, hp, ih, readMany]
        cases htail : readMany readClause n tail with
        | none => simp [htail]
        | some result => obtain ⟨clauses, rest⟩ := result; simp [hc, htail]

theorem all_clausePredicate (cert : Word) (f : CNF) :
    f.all (clausePredicate cert) =
      (f.all (fun c => decide (c.length ≤ 3)) && evalCNF (SATVerifier.assignment cert) f) := by
  induction f with
  | nil => rfl
  | cons c f ih =>
    simp [List.all_cons, clausePredicate, ih, Bool.and_assoc, Bool.and_comm, Bool.and_left_comm]

def threeFormulaParser (cert : Word) (w : Word) : Option Word := do
  let (n, rest) ← readNat w
  repeatParser (threeClauseParser cert) n rest

theorem threeFormulaParser_eq (cert : Word) (w : Word) :
    threeFormulaParser cert w = (do
      let (f, rest) ← readCNF w
      if f.all (clausePredicate cert) then some rest else none) := by
  unfold threeFormulaParser readCNF readList
  cases hp : readNat w with
  | none => simp
  | some result =>
    obtain ⟨n, rest⟩ := result
    simp only [repeat_threeClauseParser]
    cases hr : readMany readClause n rest with
    | none => simp [hr]
    | some result => obtain ⟨f, tail⟩ := result; simp [hr]

theorem threeFormulaParser_verify (cert : Word) (w : Word) :
    (match threeFormulaParser cert w with | some rest => rest.isEmpty | none => false) =
      SATVerifier.verifyThree w cert := by
  rw [threeFormulaParser_eq]
  unfold SATVerifier.verifyThree decode
  cases hp : readCNF w with
  | none => simp
  | some result =>
    obtain ⟨f, rest⟩ := result
    cases hc : f.all (clausePredicate cert) <;> cases rest <;>
      simp only [Option.bind_eq_bind, Option.bind_some, ← all_clausePredicate, hc] <;> rfl


def threeVerifier := seq (readUnary input outer)
  (seq (whileCounter outer threeClause) (testEmpty input true false))

def threeVerifierEncoding :=
  readUnaryEncoding.sum ((Encoding.bool.sum threeClauseEncoding).sum (Encoding.fin 2))

theorem threeClauses_runs (bound : Nat) (cert : Word) (n : Nat) (r : Registers 6)
    (hcounter : r outer = List.replicate n true) (h : Bounded bound cert r) :
    ∃ t b out, t ≤ n * (threeClauseCost bound + 1) + 2 ∧
      Exec (whileCounter outer threeClause) (.inl false) r t (b, out) ∧
      ParserResult (fun q => q input) (repeatParser (threeClauseParser cert) n) r b out ∧
      (b = true → Bounded bound cert out ∧ out outer = []) := by
  apply whileCounter_parser threeClause outer (fun q => q input)
    (threeClauseParser cert) (by intro q tail; simp [input, outer]) (Bounded bound cert) (threeClauseCost bound)
    ?_ (threeClause_runs bound cert) n r hcounter h
  intro q tail hq htail
  apply hq.set_counter outer (by decide) (by decide) (by decide) (by decide)
  have hh := hq.stack_le outer
  rw [htail] at hh
  simp only [List.length_cons] at hh
  omega


def threeVerifierCost (bound : Nat) : Nat := bound * (threeClauseCost bound + 1) + 3 * bound + 8

theorem threeVerifierCost_le_cubic (bound : Nat) : threeVerifierCost bound ≤ 64 * (bound + 1) ^ 3 := by
  have hsat := verifierCost_le_cubic bound
  have hlinear : 6 * bound + 11 ≤ 17 * (bound + 1) := by omega
  have hmul := Nat.mul_le_mul (Nat.le_succ bound) hlinear
  have hmul' : bound * (6 * bound + 11) ≤ 17 * (bound + 1) ^ 2 := by
    simpa [Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hmul
  have hpow : (bound + 1) ^ 2 ≤ (bound + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by decide)
  have hmore := Nat.mul_le_mul_left 17 hpow
  have heq : threeVerifierCost bound = verifierCost bound + bound * (6 * bound + 11) := by
    simp [threeVerifierCost, verifierCost, threeClauseCost, Nat.mul_add]
    omega
  rw [heq]
  omega

theorem threeVerifier_runs (bound : Nat) (cert : Word) (r : Registers 6) (h : Bounded bound cert r) :
    ∃ t out, t ≤ threeVerifierCost bound ∧
      Exec threeVerifier threeVerifier.start r t
        (SATVerifier.verifyThree (r input) cert, out) := by
  have hi := h.stack_le input
  have ho := h.stack_le outer
  cases hp : readNat (r input) with
  | none =>
    let out := (readUnaryResult input outer r).2
    have heparse : Exec (readUnary input outer) (readUnary input outer).start r
        (readUnaryTime input outer r) (false, out) := by
      have hh := exec_readUnary input outer (by decide) r
      simpa [readUnaryResult, hp, out] using hh
    have hdecision : SATVerifier.verifyThree (r input) cert = false := by
      have hv := threeFormulaParser_verify cert (r input)
      simpa [threeFormulaParser, hp] using hv.symm
    refine ⟨readUnaryTime input outer r, out, ?_, ?_⟩
    · have ht := readUnaryTime_le input outer r
      unfold threeVerifierCost
      omega
    · rw [hdecision]
      exact exec_seq_failure (readUnary input outer) _ heparse
  | some result =>
    obtain ⟨n, rest⟩ := result
    let r₁ := StackMachine.set (StackMachine.set r input rest) outer (List.replicate n true)
    have h₁ : Bounded bound cert r₁ :=
      h.unary outer (by decide) (by decide) (by decide) (by decide) n rest hp
    have hparse : Exec (readUnary input outer) (readUnary input outer).start r
        ((r outer).length + 2 * n + 4) (true, r₁) :=
      exec_readUnary_encoded input outer (by decide) n rest r (SATBounds.readNat_eq_some hp)
    have hn : n ≤ bound := by
      have hl := congrArg List.length (SATBounds.readNat_eq_some hp)
      simp only [List.length_append, SATBounds.writeNat_length] at hl
      omega
    have hprod : n * (threeClauseCost bound + 1) ≤ bound * (threeClauseCost bound + 1) :=
      Nat.mul_le_mul_right (threeClauseCost bound + 1) hn
    have h₁in : r₁ input = rest := by simp [r₁, input, outer]
    obtain ⟨t, b, out, ht, heloop, hspec, _⟩ := threeClauses_runs bound cert n r₁ (by simp [r₁]) h₁
    cases hr : repeatParser (threeClauseParser cert) n rest with
    | none =>
      have hb : b = false := by simpa [ParserResult, h₁in, hr] using hspec
      subst b
      have hdecision : SATVerifier.verifyThree (r input) cert = false := by
        have hv := threeFormulaParser_verify cert (r input)
        simpa [threeFormulaParser, hp, hr] using hv.symm
      refine ⟨(r outer).length + 2 * n + 4 + t, out, ?_, ?_⟩
      · unfold threeVerifierCost
        omega
      · rw [hdecision]
        exact exec_seq (readUnary input outer) _ hparse
          (exec_seq_failure (whileCounter outer threeClause) (testEmpty input true false) heloop)
    | some tail =>
      have hh : b = true ∧ out input = tail := by
        simpa [ParserResult, h₁in, hr] using hspec
      obtain ⟨rfl, hout⟩ := hh
      have hdecision : SATVerifier.verifyThree (r input) cert = tail.isEmpty := by
        have hv := threeFormulaParser_verify cert (r input)
        simpa [threeFormulaParser, hp, hr] using hv.symm
      have htest : Exec (testEmpty input true false) (testEmpty input true false).start out 2
          (tail.isEmpty, out) := by
        change Exec (testEmpty input true false) 0 out 2 _
        have he := exec_testEmpty input true false out
        cases ht : tail.isEmpty <;> simpa [hout, ht] using he
      refine ⟨(r outer).length + 2 * n + 4 + (t + 2), out, ?_, ?_⟩
      · unfold threeVerifierCost
        omega
      · rw [hdecision]
        exact exec_seq (readUnary input outer) _ hparse
          (exec_seq (whileCounter outer threeClause) (testEmpty input true false) heloop htest)


def threeVerifierMachine : StackMachine.Machine := compile threeVerifier threeVerifierEncoding

theorem compiled_threeVerifier_runs (bound : Nat) (cert : Word) (r : Registers 6)
    (h : Bounded bound cert r) :
    ∃ out, StackMachine.run threeVerifierMachine (threeVerifierCost bound) ⟨threeVerifierMachine.start, r⟩ =
      some (SATVerifier.verifyThree (r input) cert, out) := by
  obtain ⟨t, out, ht, he⟩ := threeVerifier_runs bound cert r h
  refine ⟨out, ?_⟩
  apply StackMachine.run_mono _ ht
  exact compile_exec threeVerifierEncoding he

/-- The concrete seven-stack verifier returns the 3-SAT certificate checker's
answer on all words, including malformed encodings and clauses wider than three. -/
theorem compiled_threeVerifier_correct (w cert : Word) :
    ∃ out, StackMachine.run threeVerifierMachine (threeVerifierCost (w.length + cert.length))
      ⟨threeVerifierMachine.start, initialRegisters w cert⟩ = some (SATVerifier.verifyThree w cert, out) := by
  have hh := compiled_threeVerifier_runs (w.length + cert.length) cert (initialRegisters w cert)
    (initialRegisters_bounded w cert)
  simpa [initialRegisters] using hh

end Complexity.StackThreeCNFVerifier
