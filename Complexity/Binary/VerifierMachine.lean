module

public import Complexity.Binary.VerifierSemantics
public import Complexity.StackPair
public import Complexity.StackCompile
import Lean.Elab.Tactic.Omega

/-!
# The binary SAT verifier as a polynomial-time machine

The verifier unpacks the paired input (`StackPair.unpack`, run on the first seven
registers), runs the parsing phase and then the consistency check. On every word it halts
within `programCost` instructions with the decision of the pure verifier `Binary.verify`
on the unpacked pair. Hence binary SAT is in NP.
-/

@[expose] public section

namespace Complexity.Binary.Verify

open Complexity.StackMachine (Registers set)
open Complexity.StackProgram
open Complexity.SAT (Word)
open Complexity.Binary

theorem six_le : 6 ≤ 17 := by decide

/-- `StackPair.unpack` on the first seven registers. -/
def unpack := embed six_le StackPair.unpack

def program := seq unpack (seq parse check)

def programEncoding := StackPair.unpackEncoding.sum (parseEncoding.sum checkEncoding)

def machine : StackMachine.Machine := compile program programEncoding

/-- The decision of the verifier on a paired word. -/
def decision (word : Word) : Bool :=
  match StackPair.decodePair word with
  | none => false
  | some (x, w) => verify x w

def initialRegisters (word : Word) : Registers 17 := fun j => if j = 0 then word else []

def pairRegisters (x w : Word) : Registers 17 :=
  fun j => if j = 0 then x else if j = 1 then w else []

theorem restrict_initial (word : Word) :
    restrict six_le (initialRegisters word) = StackPair.initial word := by
  funext j
  simp only [restrict, initialRegisters, StackPair.initial, StackPair.input]
  congr 1
  apply propext
  constructor
  · intro h; exact Fin.ext (by simpa [liftReg] using congrArg Fin.val h)
  · intro h; subst h; rfl

theorem extend_unpacked (x w : Word) :
    extend six_le (initialRegisters (pairWords x w)) (StackPair.unpacked x w) =
      pairRegisters x w := by
  funext j
  obtain ⟨n, hn⟩ := j
  by_cases h : n < 7
  · simp only [extend, h, dite_true, StackPair.unpacked, StackPair.input, StackPair.certificate,
      pairRegisters]
    by_cases h0 : n = 0
    · subst h0; rfl
    · by_cases h1 : n = 1
      · subst h1; rfl
      · have e0 : (⟨n, hn⟩ : Fin 18) ≠ 0 := by intro he; exact h0 (congrArg Fin.val he)
        have e1 : (⟨n, hn⟩ : Fin 18) ≠ 1 := by intro he; exact h1 (congrArg Fin.val he)
        have f0 : (⟨n, h⟩ : Fin 7) ≠ 0 := by intro he; exact h0 (congrArg Fin.val he)
        have f1 : (⟨n, h⟩ : Fin 7) ≠ 1 := by intro he; exact h1 (congrArg Fin.val he)
        simp [e0, e1, f0, f1]
  · have e0 : (⟨n, hn⟩ : Fin 18) ≠ 0 := by intro he; have := congrArg Fin.val he; simp at this; omega
    have e1 : (⟨n, hn⟩ : Fin 18) ≠ 1 := by intro he; have := congrArg Fin.val he; simp at this; omega
    simp [extend, h, initialRegisters, pairRegisters, e0, e1]

theorem pair_clauseInv (x w : Word) (bound : Nat) (hb : x.length ≤ bound) :
    ClauseInv bound (pairRegisters x w) := by
  constructor
  · constructor <;> rfl
  · rfl
  · simpa [pairRegisters] using hb
  · simpa [pairRegisters] using hb
  · simp [pairRegisters]

theorem consistent_reverse (es : List (Bool × List Bool)) :
    consistent es.reverse = consistent es := by
  simp [consistent]

def programCost (n : Nat) : Nat := 4 * n + 8 + parseCost n + checkCost n

theorem program_runs (word : Word) :
    ∃ t out, t ≤ programCost word.length ∧
      Exec program program.start (initialRegisters word) t (decision word, out) := by
  cases hp : StackPair.decodePair word with
  | none =>
    obtain ⟨t, out, ht, he⟩ := StackPair.unpack_failure word hp
    rw [← restrict_initial] at he
    have he' := exec_embedded six_le StackPair.unpack he
    have hf := exec_seq_failure _ (seq parse check) he'
    refine ⟨t, extend six_le (initialRegisters word) out, ?_, ?_⟩
    · unfold programCost; omega
    · have hdec : decision word = false := by simp [decision, hp]
      rw [hdec]
      exact hf
  | some pair =>
    obtain ⟨x, w⟩ := pair
    have hword := (StackPair.decodePair_eq_some_iff word x w).mp hp
    subst hword
    have hu := StackPair.exec_unpack_pair x w
    rw [← restrict_initial] at hu
    have hu' := exec_embedded six_le StackPair.unpack hu
    rw [extend_unpacked] at hu'
    let B := (pairWords x w).length
    have hlenB : B = 2 * x.length + 1 + w.length := by simp [B]
    have hI := pair_clauseInv x w B (by omega)
    obtain ⟨t₁, b₁, mid, ht₁, he₁, hspec₁⟩ := parse_runs B (pairRegisters x w) hI
      (by simp [pairRegisters])
    have hparse := parseStep_eq (pairRegisters x w) rfl rfl
    have hin : pairRegisters x w input = x := rfl
    have hcert : pairRegisters x w cert = w := rfl
    rw [hin, hcert] at hparse
    cases hstep : parseStep (pairRegisters x w) with
    | none =>
      have hb : b₁ = false := by simpa [hstep] using hspec₁
      subst hb
      have hver : verify x w = false := by
        cases hv : verify x w with
        | false => rfl
        | true =>
          exfalso
          unfold verify at hv
          cases hd : decodeBinary x with
          | none => simp [hd] at hv
          | some f =>
            cases hl : labelCNF f w with
            | none => simp [hd, hl] at hv
            | some pair =>
              obtain ⟨g, w'⟩ := pair
              have hok : g.all clauseOK = true := by
                simp only [hd, hl, Bool.and_eq_true] at hv
                exact hv.1
              simp [hd, hl, hok, hstep] at hparse
      have hf := exec_seq _ _ hu' (exec_seq_failure _ check he₁)
      refine ⟨8 * x.length + 4 * w.length + 12 + t₁, mid, ?_, ?_⟩
      · unfold programCost; simp only [B] at ht₁; simp at ht₁ ⊢; omega
      · have hdec : decision (pairWords x w) = false := by simp [decision, hver]
        rw [hdec]
        exact hf
    | some q =>
      have hs : b₁ = true ∧ mid = q := by simpa [hstep] using hspec₁
      obtain ⟨rfl, rfl⟩ := hs
      -- the decoded formula and labelling
      cases hd : decodeBinary x with
      | none => simp [hd, hstep] at hparse
      | some f =>
        cases hl : labelCNF f w with
        | none => simp [hd, hl, hstep] at hparse
        | some pair =>
          obtain ⟨g, w'⟩ := pair
          cases hok : g.all clauseOK with
          | false => simp [hd, hl, hok, hstep] at hparse
          | true =>
            have hq : mid = clausesOut (pairRegisters x w) g [] w' := by
              simpa [hd, hl, hok, hstep] using hparse
            have hIq := parseStep_invariant B (pairRegisters x w) hI mid hstep
            let es := (g.flatten.map entry).reverse
            have hent : mid entries = writeEntries es := by
              rw [hq]; simp [clausesOut, pairRegisters, es]
            have hes : es.length = g.flatten.length := by
              simp only [es, List.length_reverse, List.length_map]
            have hcnt : mid count = List.replicate es.length true := by
              rw [hq, hes]; simp [clausesOut, pairRegisters]
            have hz : ∀ j : Fin 18, j ≠ 0 → j ≠ 1 → j ≠ 2 → j ≠ 7 → j ≠ 8 → mid j = [] := by
              intro j h0 h1 h2 h7 h8
              rw [hq]
              simp [clausesOut, pairRegisters, StackMachine.set, h0, h1, h2, h7, h8]
            have hC : CheckInv B mid := by
              have h7 := hIq.entries_le
              have h8 := hIq.count_le
              simp only [input, entries, count] at h7 h8
              refine ⟨hz 17 (by decide) (by decide) (by decide) (by decide) (by decide),
                hz 13 (by decide) (by decide) (by decide) (by decide) (by decide),
                hz 14 (by decide) (by decide) (by decide) (by decide) (by decide),
                hz 16 (by decide) (by decide) (by decide) (by decide) (by decide),
                hz 15 (by decide) (by decide) (by decide) (by decide) (by decide),
                hz 9 (by decide) (by decide) (by decide) (by decide) (by decide),
                hz 10 (by decide) (by decide) (by decide) (by decide) (by decide),
                hz 11 (by decide) (by decide) (by decide) (by decide) (by decide),
                hz 12 (by decide) (by decide) (by decide) (by decide) (by decide), ?_, ?_, ?_⟩
              · have : mid 8 = List.replicate es.length true := hcnt
                rw [this]; simp
              · omega
              · omega
            obtain ⟨t₂, b₂, out, ht₂, he₂, hspec₂⟩ := check_runs B mid hC
            have hsome := check_isSome mid es hent hcnt
              (by rw [hq]; simp [clausesOut, pairRegisters])
              (by rw [hq]; simp [clausesOut, pairRegisters])
              (by rw [hq]; simp [clausesOut, pairRegisters])
              (by rw [hq]; simp [clausesOut, pairRegisters])
              (by rw [hq]; simp [clausesOut, pairRegisters])
            have hb₂ : b₂ = consistent es := by
              cases hit : iterStep count₁ outerStep (mid count).length (checkLoad mid) with
              | none =>
                rw [hit] at hsome hspec₂
                simp at hspec₂
                simp at hsome
                rw [hspec₂, ← hsome]
              | some r' =>
                rw [hit] at hsome hspec₂
                simp at hspec₂ hsome
                rw [hspec₂.1, ← hsome]
            have hver : verify x w = consistent es := by
              simp [verify, hd, hl, hok, es, consistent_reverse]
            have hf := exec_seq _ _ hu' (exec_seq _ _ he₁ he₂)
            refine ⟨8 * x.length + 4 * w.length + 12 + (t₁ + t₂), out, ?_, ?_⟩
            · unfold programCost
              simp only [B] at ht₁ ht₂
              simp at ht₁ ht₂ ⊢
              omega
            · have hdec : decision (pairWords x w) = b₂ := by simp [decision, hver, hb₂]
              rw [hdec]
              exact hf

theorem polynomialBound_programCost : PolynomialBound programCost := by
  have hlit : PolynomialBound litCost :=
    (((PolynomialBound.constant 11).mul PolynomialBound.identity).add
      (PolynomialBound.constant 18)).weaken (fun _ => Nat.le_refl _)
  have hclause : PolynomialBound clauseCost :=
    (((PolynomialBound.identity.mul (hlit.add (PolynomialBound.constant 1))).add
      ((PolynomialBound.constant 4).mul PolynomialBound.identity)).add
      (PolynomialBound.constant 10)).weaken (fun _ => Nat.le_refl _)
  have hparse : PolynomialBound parseCost :=
    (((PolynomialBound.identity.mul (hclause.add (PolynomialBound.constant 1))).add
      ((PolynomialBound.constant 3).mul PolynomialBound.identity)).add
      (PolynomialBound.constant 8)).weaken (fun _ => Nat.le_refl _)
  have hinner : PolynomialBound innerCost :=
    (((PolynomialBound.constant 9).mul PolynomialBound.identity).add
      (PolynomialBound.constant 14)).weaken (fun _ => Nat.le_refl _)
  have houter : PolynomialBound outerCost :=
    (((PolynomialBound.identity.mul (hinner.add (PolynomialBound.constant 1))).add
      ((PolynomialBound.constant 20).mul PolynomialBound.identity)).add
      (PolynomialBound.constant 30)).weaken (fun _ => Nat.le_refl _)
  have hcheck : PolynomialBound checkCost :=
    (((PolynomialBound.identity.mul (houter.add (PolynomialBound.constant 1))).add
      ((PolynomialBound.constant 12).mul PolynomialBound.identity)).add
      (PolynomialBound.constant 14)).weaken (fun _ => Nat.le_refl _)
  exact ((((((PolynomialBound.constant 4).mul PolynomialBound.identity).add
    (PolynomialBound.constant 8)).add hparse).add hcheck)).weaken (fun _ => Nat.le_refl _)

theorem machine_runs (word : Word) :
    ∃ out, StackMachine.runInput machine (programCost word.length) word =
      some (decision word, out) := by
  obtain ⟨t, out, ht, he⟩ := program_runs word
  refine ⟨out, ?_⟩
  exact StackMachine.run_mono machine ht _ _ (compile_exec programEncoding he)

theorem paired_accepts_iff (x w : Word) :
    (∃ t out, StackMachine.runInput machine t (pairWords x w) = some (true, out)) ↔
      verify x w = true := by
  obtain ⟨out₀, hcorrect⟩ := machine_runs (pairWords x w)
  have hdec : decision (pairWords x w) = verify x w := by simp [decision]
  rw [hdec] at hcorrect
  constructor
  · rintro ⟨t, out, h⟩
    have heq := StackMachine.run_deterministic machine
      (StackMachine.initial machine (pairWords x w)) h hcorrect
    exact (congrArg Prod.fst heq).symm
  · intro h
    rw [h] at hcorrect
    exact ⟨_, out₀, hcorrect⟩

end Complexity.Binary.Verify

namespace Complexity.Binary

/-- The verifier as a single-tape machine. -/
def verifierMachine : Machine := StackCompile.compile Verify.machine

theorem verifier_polynomial : PolynomialTimeMachine verifierMachine := by
  apply StackCompile.polynomialTimeMachine_of_stack Verify.machine Verify.programCost
    Verify.polynomialBound_programCost
  intro input
  obtain ⟨out, h⟩ := Verify.machine_runs input
  exact ⟨_, _, out, Nat.le_refl _, h⟩

theorem verifier_accepts_iff (x w : Word) :
    Accepts verifierMachine (pairWords x w) ↔ verify x w = true := by
  have htotal : ∃ time decision registers, StackMachine.runInput Verify.machine time
      (pairWords x w) = some (decision, registers) := by
    obtain ⟨out, h⟩ := Verify.machine_runs (pairWords x w)
    exact ⟨_, _, out, h⟩
  exact (StackCompile.accepts_iff Verify.machine (pairWords x w) htotal).trans
    (Verify.paired_accepts_iff x w)

/-- Binary SAT has a polynomial-time verifier with certificates no longer than the input. -/
theorem binarySAT_inNP : InNP SAT.BinarySAT := by
  refine ⟨verifierMachine, 1, 1, verifier_polynomial, ?_⟩
  intro input
  constructor
  · intro h
    obtain ⟨certificate, hlen, hverify⟩ := verify_complete h
    refine ⟨certificate, ?_, (verifier_accepts_iff input certificate).mpr hverify⟩
    simpa [powerBound_eq] using Nat.le_trans hlen (Nat.le_succ input.length)
  · rintro ⟨certificate, _, haccept⟩
    exact verify_sound ((verifier_accepts_iff input certificate).mp haccept)

end Complexity.Binary
