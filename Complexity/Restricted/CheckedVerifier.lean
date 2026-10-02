module

public import Complexity.Restricted.ExactCheck
public import Complexity.Restricted.Embed
public import Complexity.StackPair
public import Complexity.StackThreeCNFVerifier
public import Complexity.StackCompile
import Lean.Elab.Tactic.Omega

/-!
# The 3-SAT verifier with an extra syntactic check

`checkedVerifier check` unpacks the verifier input `pairWords x w`, runs the command `check`
on `x` (in registers `7, …, 23`, leaving registers `0, …, 6` unchanged) and, if it accepts,
runs the 3-SAT verifier of `Complexity.StackThreeCNFVerifier` on `x` and `w`. A check that
halts within a cubic bound gives an NP verifier for every language between "3-SAT words
accepted by the check" and 3-SAT (`inNP_of_check`).
-/

@[expose] public section

namespace Complexity.Restricted

open StackProgram
open StackTableauProgram (Command)
open StackMachine (Registers set)

theorem h6 : 6 ≤ 23 := by decide

def checkedVerifier (check : Command 23) :=
  StackProgram.seq (embed h6 StackPair.unpack)
    (StackProgram.seq (StackTableauProgram.compile check)
      (embed h6 StackThreeCNFVerifier.threeVerifier))

def checkedEncoding (check : Command 23) :=
  StackPair.unpackEncoding.sum
    ((StackTableauProgram.encoding check).sum StackThreeCNFVerifier.threeVerifierEncoding)

def checkedMachine (check : Command 23) : StackMachine.Machine :=
  StackProgram.compile (checkedVerifier check) (checkedEncoding check)

def checkedDecision (model : Word → Bool) (word : Word) : Bool :=
  match StackPair.decodePair word with
  | none => false
  | some (x, w) => model x && SATVerifier.verifyThree x w

/-- A correct check of the input word with a cubic instruction bound. -/
structure CheckSpec (check : Command 23) (model : Word → Bool) (cc : Nat) : Prop where
  writes_low : ∀ j : Fin 24, j.val < 7 → writes check j = false
  runs : ∀ r : Regs, HighEmpty r →
    ∃ t r', StackTableauProgram.Exec check r t (model (r rIn), r') ∧
      t ≤ cc * ((r rIn).length + 1) ^ 3

theorem low_initial (word : Word) :
    low h6 (fun j : Fin 24 => if j = 0 then word else []) = StackPair.initial word := by
  funext j
  simp only [low, liftReg, StackPair.initial, StackPair.input]
  congr 1
  apply propext
  constructor
  · intro h; apply Fin.ext; have := congrArg Fin.val h; simpa using this
  · intro h; subst h; rfl

theorem checkedVerifier_runs {check : Command 23} {model : Word → Bool} {cc : Nat}
    (hc : CheckSpec check model cc) (word : Word) :
    ∃ t out, t ≤ (cc + 80) * (word.length + 1) ^ 3 ∧
      Exec (checkedVerifier check) (checkedVerifier check).start
        (fun j : Fin 24 => if j = 0 then word else []) t (checkedDecision model word, out) := by
  let R0 : Regs := fun j => if j = 0 then word else []
  obtain ⟨t1, out1, ht1, e1, hout1⟩ := StackPair.unpack_runs word
  have E1 := exec_embed h6 e1 R0 (low_initial word)
  have hpow1 : word.length + 1 ≤ (word.length + 1) ^ 3 := Nat.le_self_pow (by decide) _
  cases hd : StackPair.decodePair word with
  | none =>
    rw [hd] at E1
    refine ⟨t1, merge h6 R0 out1, ?_, ?_⟩
    · have : 0 ≤ cc * (word.length + 1) ^ 3 := Nat.zero_le _
      rw [Nat.add_mul]; omega
    · have h := exec_seq_failure (embed h6 StackPair.unpack) (StackProgram.seq
        (StackTableauProgram.compile check) (embed h6 StackThreeCNFVerifier.threeVerifier)) E1
      have hdec : checkedDecision model word = false := by simp [checkedDecision, hd]
      rw [hdec]
      exact h
  | some val =>
    obtain ⟨x, w⟩ := val
    rw [hd] at E1
    have hw := (StackPair.decodePair_eq_some_iff word x w).mp hd
    have hlen : word.length = 2 * x.length + w.length + 1 := by simp [hw, pairWords]; omega
    rw [hout1 x w hd] at E1
    let R1 := merge h6 R0 (StackPair.unpacked x w)
    have hR1high : HighEmpty R1 := by
      intro j hj
      have : R1 j = R0 j := merge_high h6 R0 _ j (by omega)
      rw [this]
      simp only [R0]
      split
      · rename_i h; subst h; simp at hj
      · rfl
    have hR1in : R1 rIn = x := by simp [R1, merge, StackPair.unpacked, StackPair.input]
    have E1' : Exec (embed h6 StackPair.unpack) StackPair.unpack.start R0 t1 (true, R1) := E1
    obtain ⟨t2, r2, e2, ht2⟩ := hc.runs R1 hR1high
    rw [hR1in] at e2 ht2
    have E2 := e2.compile
    have hframe : ∀ j : Fin 24, j.val < 7 → r2 j = R1 j :=
      fun j hj => exec_frame e2 j (hc.writes_low j hj)
    have hx1 : x.length + 1 ≤ word.length + 1 := by omega
    have hsq : (x.length + 1) ^ 3 ≤ (word.length + 1) ^ 3 := Nat.pow_le_pow_left hx1 3
    have ht2' : t2 ≤ cc * (word.length + 1) ^ 3 :=
      Nat.le_trans ht2 (Nat.mul_le_mul_left cc hsq)
    cases hm : model x with
    | false =>
      rw [hm] at E2
      refine ⟨t1 + t2, r2, ?_, ?_⟩
      · rw [Nat.add_mul]; omega
      · have h := exec_seq _ _ E1' (exec_seq_failure (StackTableauProgram.compile check)
          (embed h6 StackThreeCNFVerifier.threeVerifier) E2)
        have hdec : checkedDecision model word = false := by simp [checkedDecision, hd, hm]
        rw [hdec]
        exact h
    | true =>
      rw [hm] at E2
      have hlow2 : low h6 r2 = StackCNFVerifier.initialRegisters x w := by
        funext j
        simp only [low]
        rw [hframe (liftReg h6 j) (by simp [liftReg])]
        show low h6 R1 j = _
        rw [low_merge]
        rfl
      obtain ⟨t3, out3, ht3, e3⟩ := StackThreeCNFVerifier.threeVerifier_runs
        (x.length + w.length) w (StackCNFVerifier.initialRegisters x w)
        (StackCNFVerifier.initialRegisters_bounded x w)
      have E3 := exec_embed h6 e3 r2 hlow2
      have hin : StackCNFVerifier.initialRegisters x w StackCNFVerifier.input = x := by
        simp [StackCNFVerifier.initialRegisters]
      rw [hin] at E3
      refine ⟨t1 + (t2 + t3), merge h6 r2 out3, ?_, ?_⟩
      · have hcube := StackThreeCNFVerifier.threeVerifierCost_le_cubic (x.length + w.length)
        have hb : x.length + w.length + 1 ≤ word.length + 1 := by omega
        have := Nat.mul_le_mul_left 64 (Nat.pow_le_pow_left hb 3)
        rw [Nat.add_mul]; omega
      · have h := exec_seq _ _ E1' (exec_seq _ _ E2 E3)
        have hdec : checkedDecision model word = SATVerifier.verifyThree x w := by
          simp [checkedDecision, hd, hm]
        rw [hdec]
        exact h

theorem checkedMachine_runs {check : Command 23} {model : Word → Bool} {cc : Nat}
    (hc : CheckSpec check model cc) (word : Word) :
    ∃ out, StackMachine.runInput (checkedMachine check) ((cc + 80) * (word.length + 1) ^ 3) word =
      some (checkedDecision model word, out) := by
  obtain ⟨t, out, ht, he⟩ := checkedVerifier_runs hc word
  exact ⟨out, StackMachine.run_mono _ ht _ _ (compile_exec (checkedEncoding check) he)⟩

theorem checkedMachine_accepts_iff {check : Command 23} {model : Word → Bool} {cc : Nat}
    (hc : CheckSpec check model cc) (x w : Word) :
    Accepts (StackCompile.compile (checkedMachine check)) (pairWords x w) ↔
      (model x && SATVerifier.verifyThree x w) = true := by
  obtain ⟨out₀, hrun⟩ := checkedMachine_runs hc (pairWords x w)
  rw [StackCompile.accepts_iff _ _ ⟨_, _, _, hrun⟩]
  have hdec : checkedDecision model (pairWords x w) = (model x && SATVerifier.verifyThree x w) := by
    simp [checkedDecision]
  rw [hdec] at hrun
  constructor
  · rintro ⟨t, out, h⟩
    have heq := StackMachine.run_deterministic _ _ h hrun
    exact (congrArg Prod.fst heq).symm
  · intro h
    rw [h] at hrun
    exact ⟨_, _, hrun⟩

theorem checkedMachine_polynomial {check : Command 23} {model : Word → Bool} {cc : Nat}
    (hc : CheckSpec check model cc) :
    PolynomialTimeMachine (StackCompile.compile (checkedMachine check)) := by
  apply StackCompile.polynomialTimeMachine_of_stack (checkedMachine check)
    (powerBound (cc + 80) 3) (PolynomialBound.power (cc + 80) 3)
  intro input
  obtain ⟨out, h⟩ := checkedMachine_runs hc input
  exact ⟨_, _, out, by simp [powerBound_eq], h⟩

/-- A language of 3-SAT words cut out by a bounded check is in NP. -/
theorem inNP_of_check {L : Language} {check : Command 23} {model : Word → Bool} {cc : Nat}
    (hc : CheckSpec check model cc)
    (hsound : ∀ x, model x = true → SAT.ThreeSAT x → L x)
    (hcomplete : ∀ x, L x → model x = true ∧ SAT.ThreeSAT x) : InNP L := by
  refine ⟨StackCompile.compile (checkedMachine check), 1, 1, checkedMachine_polynomial hc, ?_⟩
  intro input
  constructor
  · intro hL
    obtain ⟨hm, h3⟩ := hcomplete input hL
    obtain ⟨w, hlen, hv⟩ := SATVerifier.verifyThree_complete h3
    refine ⟨w, ?_, (checkedMachine_accepts_iff hc input w).mpr (by simp [hm, hv])⟩
    simpa [powerBound_eq] using Nat.le_trans hlen (Nat.le_succ input.length)
  · rintro ⟨w, _, hacc⟩
    have h := (checkedMachine_accepts_iff hc input w).mp hacc
    simp only [Bool.and_eq_true] at h
    exact hsound input h.1 (SATVerifier.verifyThree_sound h.2)

end Complexity.Restricted
