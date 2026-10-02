module

public import Complexity.StackCompile
public import Complexity.StackSATMachine
public import Complexity.StackThreeSATMachine

/-!
# Membership in machine-based NP

The verifier below is an actual finite one-tape machine. Its polynomial runtime
comes from the proved finite stack programs and the counted tape simulation.
Certificates are finite bit lists whose lengths are linear in the input size.
-/

@[expose] public section

namespace Complexity

def satVerifierMachine : Machine := StackCompile.compile StackSATMachine.machine

theorem satVerifier_polynomial : PolynomialTimeMachine satVerifierMachine := by
  apply StackCompile.polynomialTimeMachine_of_stack StackSATMachine.machine
    (powerBound 55 3) (PolynomialBound.power 55 3)
  intro input
  obtain ⟨out, h⟩ := StackSATMachine.machine_runs input
  exact ⟨55 * (input.length + 1) ^ 3, StackSATMachine.decision input, out, Nat.le_refl _, h⟩

theorem satVerifier_accepts_iff (input certificate : Word) :
    Accepts satVerifierMachine (pairWords input certificate) ↔
      SATVerifier.verify input certificate = true := by
  have htotal : ∃ time decision registers, StackMachine.runInput StackSATMachine.machine time
      (pairWords input certificate) = some (decision, registers) := by
    obtain ⟨out, h⟩ := StackSATMachine.machine_runs (pairWords input certificate)
    exact ⟨_, _, out, h⟩
  exact (StackCompile.accepts_iff StackSATMachine.machine (pairWords input certificate) htotal).trans
    (StackSATMachine.paired_accepts_iff input certificate)

/-- SAT has a uniform polynomial-time one-tape verifier and linear certificates. -/
theorem sat_inNP : InNP SAT.SAT := by
  refine ⟨satVerifierMachine, 1, 1, satVerifier_polynomial, ?_⟩
  intro input
  constructor
  · intro h
    obtain ⟨certificate, hlen, hverify⟩ := SATVerifier.verify_complete h
    refine ⟨certificate, ?_, (satVerifier_accepts_iff input certificate).mpr hverify⟩
    simpa [powerBound] using Nat.le_trans hlen (Nat.le_succ input.length)
  · rintro ⟨certificate, _, haccept⟩
    exact SATVerifier.verify_sound ((satVerifier_accepts_iff input certificate).mp haccept)

def threeSATVerifierMachine : Machine := StackCompile.compile StackThreeSATMachine.machine

theorem threeSATVerifier_polynomial : PolynomialTimeMachine threeSATVerifierMachine := by
  apply StackCompile.polynomialTimeMachine_of_stack StackThreeSATMachine.machine
    (powerBound 72 3) (PolynomialBound.power 72 3)
  intro input
  obtain ⟨out, h⟩ := StackThreeSATMachine.machine_runs input
  exact ⟨72 * (input.length + 1) ^ 3, StackThreeSATMachine.decision input, out, Nat.le_refl _, h⟩

theorem threeSATVerifier_accepts_iff (input certificate : Word) :
    Accepts threeSATVerifierMachine (pairWords input certificate) ↔
      SATVerifier.verifyThree input certificate = true := by
  have htotal : ∃ time decision registers, StackMachine.runInput StackThreeSATMachine.machine time
      (pairWords input certificate) = some (decision, registers) := by
    obtain ⟨out, h⟩ := StackThreeSATMachine.machine_runs (pairWords input certificate)
    exact ⟨_, _, out, h⟩
  exact (StackCompile.accepts_iff StackThreeSATMachine.machine (pairWords input certificate) htotal).trans
    (StackThreeSATMachine.paired_accepts_iff input certificate)

/-- 3-SAT has a uniform polynomial-time one-tape verifier and linear certificates. -/
theorem threeSAT_inNP : InNP SAT.ThreeSAT := by
  refine ⟨threeSATVerifierMachine, 1, 1, threeSATVerifier_polynomial, ?_⟩
  intro input
  constructor
  · intro h
    obtain ⟨certificate, hlen, hverify⟩ := SATVerifier.verifyThree_complete h
    refine ⟨certificate, ?_, (threeSATVerifier_accepts_iff input certificate).mpr hverify⟩
    simpa [powerBound] using Nat.le_trans hlen (Nat.le_succ input.length)
  · rintro ⟨certificate, _, haccept⟩
    exact SATVerifier.verifyThree_sound ((threeSATVerifier_accepts_iff input certificate).mp haccept)

end Complexity
