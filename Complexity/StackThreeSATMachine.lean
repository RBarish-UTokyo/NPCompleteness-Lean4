module

public import Complexity.StackPair
public import Complexity.StackThreeCNFVerifier
import Lean.Elab.Tactic.Omega

/-!
# A total finite stack-machine verifier for 3-SAT

The input uses the existing `pairWords` encoding.  The concrete machine first
unpacks the pair and then executes the checked literal/clause/formula loops.
The machine halts on every word within a uniform cubic number of primitive
stack instructions.  Transfer to the original tape-machine complexity class
uses the separate verified stack-machine simulation.
-/

@[expose] public section

namespace Complexity.StackThreeSATMachine

open Complexity.StackProgram

def program := seq StackPair.unpack (StackThreeCNFVerifier.threeVerifier)
def encoding := StackPair.unpackEncoding.sum
  (StackThreeCNFVerifier.threeVerifierEncoding)
def machine : StackMachine.Machine := compile program encoding

def decision (word : Word) : Bool :=
  match StackPair.decodePair word with
  | none => false
  | some (input, certificate) => SATVerifier.verifyThree input certificate

@[simp] theorem decision_pairWords (input certificate : Word) :
    decision (pairWords input certificate) = SATVerifier.verifyThree input certificate := by simp [decision]

theorem program_runs (word : Word) :
    ∃ t out, t ≤ 72 * (word.length + 1) ^ 3 ∧
      Exec program program.start (StackPair.initial word) t (decision word, out) := by
  cases hp : StackPair.decodePair word with
  | none =>
    obtain ⟨t, out, ht, he⟩ := StackPair.unpack_failure word hp
    have hh := exec_seq_failure StackPair.unpack (StackThreeCNFVerifier.threeVerifier) he
    refine ⟨t, out, ?_, ?_⟩
    · have hpow : word.length + 1 ≤ (word.length + 1) ^ 3 := Nat.le_pow (by decide)
      omega
    · simpa [program, seq, decision, hp] using hh
  | some result =>
    obtain ⟨input, certificate⟩ := result
    have hword := (StackPair.decodePair_eq_some_iff word input certificate).mp hp
    have hbounded := StackCNFVerifier.initialRegisters_bounded input certificate
    obtain ⟨t, out, ht, he⟩ := StackThreeCNFVerifier.threeVerifier_runs
      (input.length + certificate.length) certificate
      (StackCNFVerifier.initialRegisters input certificate) hbounded
    have hregs : StackPair.unpacked input certificate =
        StackCNFVerifier.initialRegisters input certificate := rfl
    have hu := StackPair.exec_unpack_pair input certificate
    rw [hregs] at hu
    have hh := exec_seq StackPair.unpack (StackThreeCNFVerifier.threeVerifier) hu he
    have hin : StackCNFVerifier.initialRegisters input certificate StackCNFVerifier.input = input := by
      simp [StackCNFVerifier.initialRegisters]
    rw [hin] at hh
    refine ⟨8 * input.length + 4 * certificate.length + 12 + t, out, ?_, ?_⟩
    · have hlength : word.length = 2 * input.length + certificate.length + 1 := by
        simp [hword, pairWords]
        omega
      have hb : input.length + certificate.length + 1 ≤ word.length + 1 := by omega
      have hpower := Nat.pow_le_pow_left hb 3
      have htime := StackThreeCNFVerifier.threeVerifierCost_le_cubic (input.length + certificate.length)
      have hmul := Nat.mul_le_mul_left 64 hpower
      have hlinear : word.length + 1 ≤ (word.length + 1) ^ 3 := Nat.le_pow (by decide)
      omega
    · simpa [program, seq, hword] using hh

/-- A fixed cubic fuel budget suffices on every input, including malformed pairs. -/
theorem machine_runs (word : Word) :
    ∃ out, StackMachine.runInput machine (72 * (word.length + 1) ^ 3) word =
      some (decision word, out) := by
  obtain ⟨t, out, ht, he⟩ := program_runs word
  refine ⟨out, ?_⟩
  exact StackMachine.run_mono _ ht _ _ (compile_exec encoding he)

theorem paired_accepts_iff (input certificate : Word) :
    (∃ t out, StackMachine.runInput machine t (pairWords input certificate) = some (true, out)) ↔
      SATVerifier.verifyThree input certificate = true := by
  obtain ⟨out₀, hcorrect⟩ := machine_runs (pairWords input certificate)
  rw [decision_pairWords] at hcorrect
  constructor
  · rintro ⟨t, out, h⟩
    have heq := StackMachine.run_deterministic machine (StackMachine.initial machine (pairWords input certificate)) h hcorrect
    exact (congrArg Prod.fst heq).symm
  · intro h
    rw [h] at hcorrect
    exact ⟨_, out₀, hcorrect⟩

/-- 3-SAT's linear certificate bound is realized by this concrete, total machine. -/
theorem ThreeSAT_iff_certificates (input : Word) :
    SAT.ThreeSAT input ↔ ∃ certificate : Word, certificate.length ≤ input.length ∧
      ∃ t out, StackMachine.runInput machine t (pairWords input certificate) = some (true, out) := by
  rw [SATVerifier.ThreeSAT_iff_exists_certificate]
  constructor
  · rintro ⟨certificate, hlen, h⟩
    exact ⟨certificate, hlen, (paired_accepts_iff input certificate).mpr h⟩
  · rintro ⟨certificate, hlen, h⟩
    exact ⟨certificate, hlen, (paired_accepts_iff input certificate).mp h⟩

end Complexity.StackThreeSATMachine
