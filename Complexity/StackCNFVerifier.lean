module

public import Complexity.StackParse
public import Complexity.StackLiteral
public import Complexity.SATVerifier
import Lean.Elab.Tactic.Omega

/-! Finite-control CNF verification and counted parser-loop composition. -/

@[expose] public section

namespace Complexity.StackCNFVerifier

open Complexity.StackProgram Complexity.StackWords Complexity.StackParse
open Complexity.StackMachine (Registers branch)
open Complexity.SAT

abbrev Reg := Fin 7
def input : Reg := 0
def certificate : Reg := 1
def outer : Reg := 2
def inner : Reg := 3
def work : Reg := 4
def scratch : Reg := 5
def flag : Reg := 6

structure Bounded (bound : Nat) (cert : Word) (r : Registers 6) : Prop where
  certificate_eq : r certificate = cert
  stack_le : ∀ a, (r a).length ≤ bound
  source_flag : (r input).length + (r flag).length ≤ bound
  scratch_eq : r scratch = []

theorem Bounded.set_counter {bound : Nat} {cert : Word} {r : Registers 6}
    (h : Bounded bound cert r) (j : Reg) (hi : j ≠ input) (hc : j ≠ certificate)
    (hf : j ≠ flag) (hs : j ≠ scratch) (xs : Word) (hlen : xs.length ≤ bound) :
    Bounded bound cert (StackMachine.set r j xs) := by
  constructor
  · simpa [Ne.symm hc] using h.certificate_eq
  · intro a
    by_cases ha : a = j
    · subst a; simpa using hlen
    · simpa [ha] using h.stack_le a
  · simpa [Ne.symm hi, Ne.symm hf] using h.source_flag
  · simpa [Ne.symm hs] using h.scratch_eq

theorem Bounded.clear_flag {bound : Nat} {cert : Word} {r : Registers 6}
    (h : Bounded bound cert r) : Bounded bound cert (StackMachine.set r flag []) := by
  constructor
  · simpa [certificate, flag] using h.certificate_eq
  · intro a
    by_cases ha : a = flag
    · subst a; simp
    · simpa [ha] using h.stack_le a
  · simpa [input, flag] using h.stack_le input
  · simpa [scratch, flag] using h.scratch_eq

theorem Bounded.unary {bound : Nat} {cert : Word} {r : Registers 6}
    (h : Bounded bound cert r) (j : Reg) (hi : j ≠ input) (hc : j ≠ certificate)
    (hf : j ≠ flag) (hs : j ≠ scratch) (n : Nat) (rest : Word)
    (hp : readNat (r input) = some (n, rest)) :
    Bounded bound cert (StackMachine.set (StackMachine.set r input rest) j (List.replicate n true)) := by
  have hlen := congrArg List.length (SATBounds.readNat_eq_some hp)
  simp only [List.length_append, SATBounds.writeNat_length] at hlen
  have hsource := h.source_flag
  have hin := h.stack_le input
  have hb : Bounded bound cert (StackMachine.set r input rest) := by
    constructor
    · simpa [certificate, input] using h.certificate_eq
    · intro a
      by_cases ha : a = input
      · subst a; simp only [StackMachine.set_same]; omega
      · simpa [ha] using h.stack_le a
    · simp only [StackMachine.set_same, StackMachine.set_other _ (by decide : flag ≠ input)]
      omega
    · simpa [scratch, input] using h.scratch_eq
  apply hb.set_counter j hi hc hf hs
  simp only [List.length_replicate]
  omega

def literalProgram := StackLiteral.literalBody input certificate work scratch flag
def literalProgramEncoding := StackLiteral.literalEncoding

theorem literal_valid : StackLiteral.Valid input certificate work scratch flag := by
  constructor <;> decide

theorem Bounded.literal {bound : Nat} {cert : Word} {r : Registers 6}
    (h : Bounded bound cert r) (l : Literal) (rest : Word)
    (hp : readLiteral (r input) = some (l, rest)) :
    Bounded bound cert (StackLiteral.bodyFinish input certificate work flag r l rest) := by
  have hlen := congrArg List.length (SATBounds.readLiteral_eq_some hp)
  simp only [List.length_append, SATBounds.encodeLiteral_length] at hlen
  have hsource := h.source_flag
  have hc := h.stack_le certificate
  constructor
  · simpa [StackLiteral.bodyFinish, certificate, input, work, flag] using h.certificate_eq
  · intro a
    by_cases hf : a = flag
    · subst a
      simp only [StackLiteral.bodyFinish, StackMachine.set_same]
      split <;> (try simp only [List.length_cons]) <;> omega
    · by_cases hw : a = work
      · subst a
        simp only [StackLiteral.bodyFinish, StackMachine.set_other _ hf, StackMachine.set_same,
          List.length_drop]
        omega
      · by_cases hi : a = input
        · subst a
          simp only [StackLiteral.bodyFinish, StackMachine.set_other _ hf,
            StackMachine.set_other _ hw, StackMachine.set_same]
          omega
        · simpa [StackLiteral.bodyFinish, hf, hw, hi] using h.stack_le a
  · simp only [StackLiteral.bodyFinish, StackMachine.set_same,
      StackMachine.set_other _ (by decide : input ≠ flag),
      StackMachine.set_other _ (by decide : input ≠ work)]
    split <;> (try simp only [List.length_cons]) <;> omega
  · simpa [StackLiteral.bodyFinish, scratch, input, work, flag] using h.scratch_eq

/-- A predicate on the current top-level input and a terminating run's result. -/
def ParserResult {S : Type} (view : Registers 6 → S) (parse : S → Option S) (r : Registers 6)
    (b : Bool) (out : Registers 6) : Prop :=
  match parse (view r) with
  | none => b = false
  | some rest => b = true ∧ view out = rest

def repeatParser {S : Type} (parse : S → Option S) : Nat → S → Option S
  | 0, w => some w
  | n + 1, w => do
      let rest ← parse w
      repeatParser parse n rest

/-- Counted loops implement parser iteration, including early failure.

`I` is an explicitly supplied loop invariant.  The body must preserve its
counter on successful parsing; all decrement instructions belong to the loop.
-/
theorem whileCounter_parser {L S : Type} (body : Program 6 L)
    (j : Reg) (view : Registers 6 → S) (parse : S → Option S)
    (hview : ∀ r tail, view (StackMachine.set r j tail) = view r)
    (I : Registers 6 → Prop) (cost : Nat)
    (hpop : ∀ r tail, I r → r j = true :: tail → I (StackMachine.set r j tail))
    (hbody : ∀ r, I r → ∃ t b out,
      t ≤ cost ∧ Exec body body.start r t (b, out) ∧
      ParserResult view parse r b out ∧ (b = true → I out ∧ out j = r j))
    (n : Nat) (r : Registers 6) (hr : r j = List.replicate n true) (hI : I r) :
    ∃ t b out, t ≤ n * (cost + 1) + 2 ∧
      Exec (whileCounter j body) (.inl false) r t (b, out) ∧
      ParserResult view (repeatParser parse n) r b out ∧
      (b = true → I out ∧ out j = []) := by
  induction n generalizing r with
  | zero =>
    refine ⟨2, true, r, by simp, exec_whileCounter_done j body r (by simpa using hr), ?_, ?_⟩
    · simp [ParserResult, repeatParser]
    · intro _; exact ⟨hI, by simpa using hr⟩
  | succ n ih =>
    let r' := StackMachine.set r j (List.replicate n true)
    have hrcons : r j = true :: List.replicate n true := by simpa [List.replicate_succ] using hr
    have hI' : I r' := hpop r _ hI hrcons
    have hin : view r' = view r := hview r _
    obtain ⟨t, b, middle, ht, he, hspec, hmid⟩ := hbody r' hI'
    cases hp : parse (view r) with
    | none =>
      have hb : b = false := by simpa [ParserResult, hin, hp] using hspec
      subst b
      refine ⟨t + 1, false, middle, ?_, ?_, ?_, by simp⟩
      · have hn : cost + 1 ≤ (n + 1) * (cost + 1) := by
          simp [Nat.succ_mul]
        omega
      · exact exec_whileCounter_failure j body hrcons he
      · simp [ParserResult, repeatParser, hp]
    | some rest =>
      have hspec' : b = true ∧ view middle = rest := by
        simpa [ParserResult, hin, hp] using hspec
      obtain ⟨rfl, hmIn⟩ := hspec'
      obtain ⟨hmI, hmJ⟩ := hmid rfl
      have hmCounter : middle j = List.replicate n true := by simpa [r'] using hmJ
      obtain ⟨s, b, out, hs, herest, hsSpec, hsI⟩ := ih middle hmCounter hmI
      refine ⟨t + s + 1, b, out, ?_, ?_, ?_, hsI⟩
      · simp only [Nat.succ_mul]
        omega
      · exact exec_whileCounter_next j body hrcons he herest
      · simpa [ParserResult, repeatParser, hp, hmIn] using hsSpec

/-- A two-instruction test for an empty register. -/
def testEmpty (j : Reg) (emptyResult nonemptyResult : Bool) : Program 6 (Fin 3) where
  start := 0
  code := fun q => if q = 0 then .peek j 1 2 2
    else if q = 1 then .halt emptyResult else .halt nonemptyResult

theorem exec_testEmpty (j : Reg) (emptyResult nonemptyResult : Bool) (r : Registers 6) :
    Exec (testEmpty j emptyResult nonemptyResult) 0 r 2
      ((if (r j).isEmpty then emptyResult else nonemptyResult), r) := by
  cases hr : r j with
  | nil =>
    apply Exec.next (q' := 1) (r' := r)
    · simp [StackProgram.step, testEmpty, hr, branch]
    · exact .halt (by simp [StackProgram.step, testEmpty])
  | cons b tail =>
    apply Exec.next (q' := 2) (r' := r)
    · cases b <;> simp [StackProgram.step, testEmpty, hr, branch]
    · exact .halt (by simp [StackProgram.step, testEmpty])

abbrev ClauseLabel (L : Type) := Sum Bool (Sum (Sum Bool (Fin 4)) (Sum (Sum Bool L) (Fin 3)))

/-- Read a clause length, scan its literals, and require a nonempty satisfaction flag. -/
def clause {L : Type} (literal : Program 6 L) : Program 6 (ClauseLabel L) :=
  seq (clear flag) (seq (readUnary input inner)
    (seq (whileCounter inner literal) (testEmpty flag false true)))

abbrev VerifierLabel (L : Type) := Sum (Sum Bool (Fin 4)) (Sum (Sum Bool (ClauseLabel L)) (Fin 3))

/-- Read the number of clauses, check every clause, and reject trailing input. -/
def verifier {L : Type} (literal : Program 6 L) : Program 6 (VerifierLabel L) :=
  seq (readUnary input outer)
    (seq (whileCounter outer (clause literal)) (testEmpty input true false))

def clauseEncoding {L : Type} (e : Encoding L) : Encoding (ClauseLabel L) :=
  Encoding.bool.sum (readUnaryEncoding.sum ((Encoding.bool.sum e).sum (Encoding.fin 2)))

def verifierEncoding {L : Type} (e : Encoding L) : Encoding (VerifierLabel L) :=
  readUnaryEncoding.sum ((Encoding.bool.sum (clauseEncoding e)).sum (Encoding.fin 2))

def literalView (r : Registers 6) : Word × Bool := (r input, !(r flag).isEmpty)

def literalParser (cert : Word) (state : Word × Bool) : Option (Word × Bool) := do
  let (lit, rest) ← readLiteral state.1
  pure (rest, state.2 || evalLiteral (SATVerifier.assignment cert) lit)

theorem literal_runs (bound : Nat) (cert : Word) (r : Registers 6) (h : Bounded bound cert r) :
    ∃ t b out, t ≤ 8 * bound + 12 ∧ Exec literalProgram literalProgram.start r t (b, out) ∧
      ParserResult literalView (literalParser cert) r b out ∧
      (b = true → Bounded bound cert out ∧ out outer = r outer ∧ out inner = r inner) := by
  cases hp : readLiteral (r input) with
  | none =>
    obtain ⟨t, out, ht, he⟩ := StackLiteral.literalBody_failure input certificate work scratch flag
      literal_valid r h.scratch_eq bound (h.stack_le input) (h.stack_le certificate) (h.stack_le work) hp
    refine ⟨t, false, out, ht, he, ?_, by simp⟩
    simp [ParserResult, literalParser, literalView, hp]
  | some result =>
    obtain ⟨l, rest⟩ := result
    obtain ⟨t, ht, he⟩ := StackLiteral.literalBody_success_bound input certificate work scratch flag
      literal_valid r h.scratch_eq bound (h.stack_le input) (h.stack_le certificate) (h.stack_le work) l rest hp
    refine ⟨t, true, StackLiteral.bodyFinish input certificate work flag r l rest, ht, he, ?_, ?_⟩
    · have hp0 : readLiteral (r 0) = some (l, rest) := hp
      cases hv : evalLiteral (SATVerifier.assignment cert) l <;>
        simp [ParserResult, literalParser, literalView, hp0, StackLiteral.bodyFinish,
          h.certificate_eq, hv, input, flag, work]
    · intro _
      exact ⟨h.literal l rest hp,
        by simp [StackLiteral.bodyFinish, outer, input, work, flag],
        by simp [StackLiteral.bodyFinish, inner, input, work, flag]⟩

theorem literals_runs (bound : Nat) (cert : Word) (n : Nat) (r : Registers 6)
    (hcounter : r inner = List.replicate n true) (h : Bounded bound cert r) :
    ∃ t b out, t ≤ n * (8 * bound + 13) + 2 ∧
      Exec (whileCounter inner literalProgram) (.inl false) r t (b, out) ∧
      ParserResult literalView (repeatParser (literalParser cert) n) r b out ∧
      (b = true → Bounded bound cert out ∧ out outer = r outer ∧ out inner = []) := by
  let I := fun q : Registers 6 => Bounded bound cert q ∧ q outer = r outer
  have hpop : ∀ q tail, I q → q inner = true :: tail → I (StackMachine.set q inner tail) := by
    intro q tail hq htail
    constructor
    · apply hq.1.set_counter inner (by decide) (by decide) (by decide) (by decide)
      have hh := hq.1.stack_le inner
      rw [htail] at hh
      simp only [List.length_cons] at hh
      omega
    · simpa [outer, inner] using hq.2
  have hb : ∀ q, I q → ∃ t b out,
      t ≤ 8 * bound + 12 ∧ Exec literalProgram literalProgram.start q t (b, out) ∧
      ParserResult literalView (literalParser cert) q b out ∧
      (b = true → I out ∧ out inner = q inner) := by
    intro q hq
    obtain ⟨t, b, out, ht, he, hs, hi⟩ := literal_runs bound cert q hq.1
    refine ⟨t, b, out, ht, he, hs, ?_⟩
    intro htrue
    obtain ⟨hout, ho, hi⟩ := hi htrue
    exact ⟨⟨hout, ho.trans hq.2⟩, hi⟩
  obtain ⟨t, b, out, ht, he, hs, hi⟩ := whileCounter_parser literalProgram inner literalView
    (literalParser cert) (by intro q tail; simp [literalView, input, inner, flag]) I
    (8 * bound + 12) hpop hb n r hcounter ⟨h, rfl⟩
  refine ⟨t, b, out, by simpa [Nat.add_assoc] using ht, he, hs, ?_⟩
  intro htrue
  obtain ⟨⟨hout, ho⟩, hi⟩ := hi htrue
  exact ⟨hout, ho, hi⟩

theorem repeat_literalParser (cert : Word) (n : Nat) (w : Word) (sat : Bool) :
    repeatParser (literalParser cert) n (w, sat) =
      (do let (lits, rest) ← readMany readLiteral n w
          pure (rest, sat || evalClause (SATVerifier.assignment cert) lits)) := by
  induction n generalizing w sat with
  | zero => simp [repeatParser, readMany]
  | succ n ih =>
    cases hp : readLiteral w with
    | none => simp [repeatParser, literalParser, readMany, hp]
    | some result =>
      obtain ⟨lit, tail⟩ := result
      simp only [repeatParser, literalParser, hp, ih, readMany]
      cases htail : readMany readLiteral n tail with
      | none => simp [htail]
      | some result =>
        obtain ⟨lits, rest⟩ := result
        simp [htail, Bool.or_assoc]

def clauseParser (cert : Word) (w : Word) : Option Word := do
  let (c, rest) ← readClause w
  if evalClause (SATVerifier.assignment cert) c then some rest else none

theorem repeat_clauseParser (cert : Word) (n : Nat) (w : Word) :
    repeatParser (clauseParser cert) n w =
      (do let (clauses, rest) ← readMany readClause n w
          if evalCNF (SATVerifier.assignment cert) clauses then some rest else none) := by
  induction n generalizing w with
  | zero => simp [repeatParser, readMany]
  | succ n ih =>
    cases hp : readClause w with
    | none => simp [repeatParser, clauseParser, readMany, hp]
    | some result =>
      obtain ⟨c, tail⟩ := result
      cases hc : evalClause (SATVerifier.assignment cert) c with
      | false =>
        cases htail : readMany readClause n tail with
        | none => simp [repeatParser, clauseParser, readMany, hp, hc, htail]
        | some result =>
          obtain ⟨clauses, rest⟩ := result
          simp [repeatParser, clauseParser, readMany, hp, hc, htail]
      | true =>
        simp only [repeatParser, clauseParser, hp, ih, readMany]
        cases htail : readMany readClause n tail with
        | none => simp [htail]
        | some result =>
          obtain ⟨clauses, rest⟩ := result
          simp [hc, htail]

def formulaParser (cert : Word) (w : Word) : Option Word := do
  let (n, rest) ← readNat w
  repeatParser (clauseParser cert) n rest

theorem formulaParser_eq (cert : Word) (w : Word) :
    formulaParser cert w =
      (do let (f, rest) ← readCNF w
          if evalCNF (SATVerifier.assignment cert) f then some rest else none) := by
  unfold formulaParser readCNF readList
  cases hp : readNat w with
  | none => simp
  | some result =>
    obtain ⟨n, rest⟩ := result
    simp only [repeat_clauseParser]
    cases hr : readMany readClause n rest with
    | none => simp [hr]
    | some result => obtain ⟨f, tail⟩ := result; simp [hr]

theorem formulaParser_verify (cert : Word) (w : Word) :
    (match formulaParser cert w with | some rest => rest.isEmpty | none => false) =
      SATVerifier.verify w cert := by
  rw [formulaParser_eq]
  unfold SATVerifier.verify decode
  cases hp : readCNF w with
  | none => simp
  | some result =>
    obtain ⟨f, rest⟩ := result
    cases hc : evalCNF (SATVerifier.assignment cert) f <;> cases rest <;> simp [hc]

def clauseCost (bound : Nat) : Nat := bound * (8 * bound + 13) + 4 * bound + 10

theorem clause_runs (bound : Nat) (cert : Word) (r : Registers 6) (h : Bounded bound cert r) :
    ∃ t b out, t ≤ clauseCost bound ∧
      Exec (clause literalProgram) (clause literalProgram).start r t (b, out) ∧
      ParserResult (fun q => q input) (clauseParser cert) r b out ∧
      (b = true → Bounded bound cert out ∧ out outer = r outer) := by
  let r₀ := StackMachine.set r flag []
  have h₀ : Bounded bound cert r₀ := h.clear_flag
  have hclear : Exec (clear flag) (clear flag).start r ((r flag).length + 2) (true, r₀) := exec_clear flag r
  have h₀in : r₀ input = r input := by simp [r₀, input, flag]
  have h₀inner : r₀ inner = r inner := by simp [r₀, inner, flag]
  have hflagBound := h.stack_le flag
  have hinputBound := h.stack_le input
  have hinnerBound := h.stack_le inner
  cases hp : readNat (r input) with
  | none =>
    let out := (readUnaryResult input inner r₀).2
    have heparse : Exec (readUnary input inner) (readUnary input inner).start r₀
        (readUnaryTime input inner r₀) (false, out) := by
      have hh := exec_readUnary input inner (by decide) r₀
      simpa [readUnaryResult, h₀in, hp, out] using hh
    have he := exec_seq (clear flag)
      (seq (readUnary input inner) (seq (whileCounter inner literalProgram) (testEmpty flag false true))) hclear
      (exec_seq_failure (readUnary input inner) _ heparse)
    refine ⟨(r flag).length + 2 + readUnaryTime input inner r₀, false, out, ?_, he, ?_, by simp⟩
    · have ht := readUnaryTime_le input inner r₀
      rw [h₀in, h₀inner] at ht
      unfold clauseCost
      omega
    · simp [ParserResult, clauseParser, readClause, readList, hp]
  | some pair =>
    obtain ⟨n, rest⟩ := pair
    let r₁ := StackMachine.set (StackMachine.set r₀ input rest) inner (List.replicate n true)
    have hp₀ : readNat (r₀ input) = some (n, rest) := by simpa [h₀in] using hp
    have h₁ : Bounded bound cert r₁ := h₀.unary inner (by decide) (by decide) (by decide) (by decide) n rest hp₀
    have hparse : Exec (readUnary input inner) (readUnary input inner).start r₀
        ((r₀ inner).length + 2 * n + 4) (true, r₁) :=
      exec_readUnary_encoded input inner (by decide) n rest r₀ (SATBounds.readNat_eq_some hp₀)
    have hn : n ≤ bound := by
      have hl := congrArg List.length (SATBounds.readNat_eq_some hp)
      simp only [List.length_append, SATBounds.writeNat_length] at hl
      omega
    have hprod : n * (8 * bound + 13) ≤ bound * (8 * bound + 13) :=
      Nat.mul_le_mul_right (8 * bound + 13) hn
    have hv : literalView r₁ = (rest, false) := by simp [literalView, r₁, r₀, input, inner, flag]
    have h₁outer : r₁ outer = r outer := by simp [r₁, r₀, outer, inner, input, flag]
    obtain ⟨t, b, out, ht, heloop, hspec, hout⟩ := literals_runs bound cert n r₁ (by simp [r₁]) h₁
    cases hpMany : readMany readLiteral n rest with
    | none =>
      have hb : b = false := by
        simpa [ParserResult, hv, repeat_literalParser, hpMany] using hspec
      subst b
      have he := exec_seq (clear flag) _ hclear
        (exec_seq (readUnary input inner) _ hparse
          (exec_seq_failure (whileCounter inner literalProgram) (testEmpty flag false true) heloop))
      refine ⟨(r flag).length + 2 + ((r₀ inner).length + 2 * n + 4 + t), false, out, ?_, he, ?_, by simp⟩
      · rw [h₀inner]
        unfold clauseCost
        omega
      · simp [ParserResult, clauseParser, readClause, readList, hp, hpMany]
    | some result =>
      obtain ⟨lits, tail⟩ := result
      have hh : b = true ∧ literalView out = (tail, evalClause (SATVerifier.assignment cert) lits) := by
        simpa [ParserResult, hv, repeat_literalParser, hpMany] using hspec
      obtain ⟨rfl, hvout⟩ := hh
      have houtInput : out input = tail := congrArg Prod.fst hvout
      have houtFlag : (!(out flag).isEmpty) = evalClause (SATVerifier.assignment cert) lits :=
        congrArg Prod.snd hvout
      have htest : Exec (testEmpty flag false true) (testEmpty flag false true).start out 2
          (evalClause (SATVerifier.assignment cert) lits, out) := by
        have heq : (if (out flag).isEmpty then false else true) = evalClause (SATVerifier.assignment cert) lits := by
          cases he : (out flag).isEmpty <;> simpa [he] using houtFlag
        change Exec (testEmpty flag false true) 0 out 2 _
        simpa only [heq] using exec_testEmpty flag false true out
      have he := exec_seq (clear flag) _ hclear
        (exec_seq (readUnary input inner) _ hparse
          (exec_seq (whileCounter inner literalProgram) (testEmpty flag false true) heloop htest))
      refine ⟨(r flag).length + 2 + ((r₀ inner).length + 2 * n + 4 + (t + 2)),
        evalClause (SATVerifier.assignment cert) lits, out, ?_, he, ?_, ?_⟩
      · rw [h₀inner]
        unfold clauseCost
        omega
      · cases hc : evalClause (SATVerifier.assignment cert) lits <;>
          simp [ParserResult, clauseParser, readClause, readList, hp, hpMany, hc, houtInput]
      · intro _
        obtain ⟨hgood, houter, _⟩ := hout rfl
        exact ⟨hgood, houter.trans h₁outer⟩

theorem clauses_runs (bound : Nat) (cert : Word) (n : Nat) (r : Registers 6)
    (hcounter : r outer = List.replicate n true) (h : Bounded bound cert r) :
    ∃ t b out, t ≤ n * (clauseCost bound + 1) + 2 ∧
      Exec (whileCounter outer (clause literalProgram)) (.inl false) r t (b, out) ∧
      ParserResult (fun q => q input) (repeatParser (clauseParser cert) n) r b out ∧
      (b = true → Bounded bound cert out ∧ out outer = []) := by
  apply whileCounter_parser (clause literalProgram) outer (fun q => q input)
    (clauseParser cert) (by intro q tail; simp [input, outer]) (Bounded bound cert) (clauseCost bound)
    ?_ (clause_runs bound cert) n r hcounter h
  intro q tail hq htail
  apply hq.set_counter outer (by decide) (by decide) (by decide) (by decide)
  have hh := hq.stack_le outer
  rw [htail] at hh
  simp only [List.length_cons] at hh
  omega

/-- A cubic bound counts every instruction in the finite verification graph. -/
def verifierCost (bound : Nat) : Nat := bound * (clauseCost bound + 1) + 3 * bound + 8

theorem verifierCost_le_cubic (bound : Nat) : verifierCost bound ≤ 47 * (bound + 1) ^ 3 := by
  have hsquare : bound + 1 ≤ (bound + 1) ^ 2 := Nat.le_pow (by decide)
  have hcube : bound + 1 ≤ (bound + 1) ^ 3 := Nat.le_pow (by decide)
  have hlinear : 8 * bound + 13 ≤ 21 * (bound + 1) := by omega
  have hfirst := Nat.mul_le_mul (Nat.le_succ bound) hlinear
  have hfirst' : bound * (8 * bound + 13) ≤ 21 * (bound + 1) ^ 2 := by
    simpa [Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hfirst
  have hclause : clauseCost bound + 1 ≤ 36 * (bound + 1) ^ 2 := by
    unfold clauseCost
    omega
  have hsecond := Nat.mul_le_mul (Nat.le_succ bound) hclause
  have hsecond' : bound * (clauseCost bound + 1) ≤ 36 * (bound + 1) ^ 3 := by
    simpa [Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hsecond
  unfold verifierCost
  omega

theorem verifier_runs (bound : Nat) (cert : Word) (r : Registers 6) (h : Bounded bound cert r) :
    ∃ t out, t ≤ verifierCost bound ∧
      Exec (verifier literalProgram) (verifier literalProgram).start r t
        (SATVerifier.verify (r input) cert, out) := by
  have hi := h.stack_le input
  have ho := h.stack_le outer
  cases hp : readNat (r input) with
  | none =>
    let out := (readUnaryResult input outer r).2
    have heparse : Exec (readUnary input outer) (readUnary input outer).start r
        (readUnaryTime input outer r) (false, out) := by
      have hh := exec_readUnary input outer (by decide) r
      simpa [readUnaryResult, hp, out] using hh
    have hdecision : SATVerifier.verify (r input) cert = false := by
      have hv := formulaParser_verify cert (r input)
      simpa [formulaParser, hp] using hv.symm
    refine ⟨readUnaryTime input outer r, out, ?_, ?_⟩
    · have ht := readUnaryTime_le input outer r
      unfold verifierCost
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
    have hprod : n * (clauseCost bound + 1) ≤ bound * (clauseCost bound + 1) :=
      Nat.mul_le_mul_right (clauseCost bound + 1) hn
    have h₁in : r₁ input = rest := by simp [r₁, input, outer]
    obtain ⟨t, b, out, ht, heloop, hspec, _⟩ := clauses_runs bound cert n r₁ (by simp [r₁]) h₁
    cases hr : repeatParser (clauseParser cert) n rest with
    | none =>
      have hb : b = false := by simpa [ParserResult, h₁in, hr] using hspec
      subst b
      have hdecision : SATVerifier.verify (r input) cert = false := by
        have hv := formulaParser_verify cert (r input)
        simpa [formulaParser, hp, hr] using hv.symm
      refine ⟨(r outer).length + 2 * n + 4 + t, out, ?_, ?_⟩
      · unfold verifierCost
        omega
      · rw [hdecision]
        exact exec_seq (readUnary input outer) _ hparse
          (exec_seq_failure (whileCounter outer (clause literalProgram)) (testEmpty input true false) heloop)
    | some tail =>
      have hh : b = true ∧ out input = tail := by
        simpa [ParserResult, h₁in, hr] using hspec
      obtain ⟨rfl, hout⟩ := hh
      have hdecision : SATVerifier.verify (r input) cert = tail.isEmpty := by
        have hv := formulaParser_verify cert (r input)
        simpa [formulaParser, hp, hr] using hv.symm
      have htest : Exec (testEmpty input true false) (testEmpty input true false).start out 2
          (tail.isEmpty, out) := by
        change Exec (testEmpty input true false) 0 out 2 _
        have he := exec_testEmpty input true false out
        cases ht : tail.isEmpty <;> simpa [hout, ht] using he
      refine ⟨(r outer).length + 2 * n + 4 + (t + 2), out, ?_, ?_⟩
      · unfold verifierCost
        omega
      · rw [hdecision]
        exact exec_seq (readUnary input outer) _ hparse
          (exec_seq (whileCounter outer (clause literalProgram)) (testEmpty input true false) heloop htest)

def verifierMachine : StackMachine.Machine :=
  compile (verifier literalProgram) (verifierEncoding literalProgramEncoding)

theorem compiled_verifier_runs (bound : Nat) (cert : Word) (r : Registers 6)
    (h : Bounded bound cert r) :
    ∃ out, StackMachine.run verifierMachine (verifierCost bound) ⟨verifierMachine.start, r⟩ =
      some (SATVerifier.verify (r input) cert, out) := by
  obtain ⟨t, out, ht, he⟩ := verifier_runs bound cert r h
  refine ⟨out, ?_⟩
  apply StackMachine.run_mono _ ht
  exact compile_exec (verifierEncoding literalProgramEncoding) he

def initialRegisters (w cert : Word) : Registers 6 :=
  fun a => if a = input then w else if a = certificate then cert else []

theorem initialRegisters_bounded (w cert : Word) :
    Bounded (w.length + cert.length) cert (initialRegisters w cert) := by
  constructor
  · simp [initialRegisters, input, certificate]
  · intro a
    unfold initialRegisters
    split
    · omega
    · split
      · omega
      · simp
  · simp [initialRegisters, input, flag, certificate]
  · simp [initialRegisters, input, scratch, certificate]

/-- On every input/certificate pair the concrete finite stack machine returns
the previously proved SAT verifier's answer within a cubic instruction bound. -/
theorem compiled_verifier_correct (w cert : Word) :
    ∃ out, StackMachine.run verifierMachine (verifierCost (w.length + cert.length))
      ⟨verifierMachine.start, initialRegisters w cert⟩ = some (SATVerifier.verify w cert, out) := by
  have hh := compiled_verifier_runs (w.length + cert.length) cert (initialRegisters w cert)
    (initialRegisters_bounded w cert)
  simpa [initialRegisters] using hh

end Complexity.StackCNFVerifier
