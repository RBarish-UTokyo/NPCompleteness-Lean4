module

public import Complexity.StackTableauMachineBounds
public import Complexity.StackCompile
import Lean.Elab.Tactic.Omega

/-!
# Deciding with a formula emitter

A fixed emitter `program : ClauseProgram 1` is run by the verified emitter compiler of
`StackTableauEmitterCompile`; a three-instruction check then accepts exactly when the emitted
formula is `[[]]` (one empty clause), whose code is `[true, false, false]`.  The resulting
one-tape machine runs in polynomial time, so an NP verifier can be written as an emitter that
emits one empty clause for its bookkeeping and one more empty clause for each failed check.
-/

@[expose] public section

namespace Complexity.Planar

open StackMachine (Registers)
open StackProgram
open StackTableauEmitter

/-- Pop three bits from register zero, expecting `true, false, false`, then expect an empty
register. Label 4 accepts and label 5 rejects. -/
def matchCode {k : Nat} : Program k (Fin 6) where
  start := 0
  code q :=
    if q = 0 then .pop 0 5 5 1
    else if q = 1 then .pop 0 5 2 5
    else if q = 2 then .pop 0 5 3 5
    else if q = 3 then .peek 0 4 5 5
    else if q = 4 then .halt true
    else .halt false

/-- The three-bit code of the formula `[[]]`. -/
def emptyClauseCode : Word := [true, false, false]

theorem encode_eq_emptyClauseCode_iff (f : SAT.CNF) :
    SAT.encode f = emptyClauseCode ↔ f = [[]] := by
  constructor
  · intro h
    have h' : SAT.encode f = SAT.encode [[]] := by rw [h]; rfl
    exact SAT.encode_injective f [[]] h'
  · rintro rfl; rfl

theorem run_matchCode {k : Nat} (r : Registers k) :
    ∃ out, StackProgram.run (matchCode (k := k)) 5 0 r =
      some (decide (r 0 = emptyClauseCode), out) := by
  rcases h0 : r 0 with _ | ⟨_ | _, _ | ⟨_ | _, _ | ⟨_ | _, _ | ⟨_ | _, rest⟩⟩⟩⟩ <;>
    simp [StackProgram.run, StackProgram.step, matchCode, StackMachine.branch, h0,
      emptyClauseCode]

theorem exec_matchCode {k : Nat} (r : Registers k) :
    ∃ t out, t ≤ 5 ∧ Exec (matchCode (k := k)) 0 r t (decide (r 0 = emptyClauseCode), out) := by
  obtain ⟨out, h⟩ := run_matchCode r
  obtain ⟨t, ht, he⟩ := run_exists_exec _ _ _ _ _ h
  exact ⟨t, out, ht, he⟩

/-- The emitter followed by the check, as one structured stack program. -/
def decideProgram (program : ClauseProgram 1) :=
  seq (StackTableauProgram.compile (StackTableauEmitterCompile.command program))
    (matchCode (k := 6 + StackTableauEmitterCompile.programSpace program))

def decideEncoding (program : ClauseProgram 1) :=
  (StackTableauProgram.encoding (StackTableauEmitterCompile.command program)).sum
    (Encoding.fin 5)

/-- The finite stack machine deciding `program.emit input _ = [[]]`. -/
def decideStack (program : ClauseProgram 1) : StackMachine.Machine :=
  compile (decideProgram program) (decideEncoding program)

/-- The decision computed on `input`. -/
def emitDecision (program : ClauseProgram 1) (input : Word) : Bool :=
  decide (program.emit input (fun _ => input.length) = [[]])

theorem decideStack_runs (program : ClauseProgram 1) (input : Word) :
    ∃ time out, time ≤ StackTableauEmitterCompile.machineBudget program input.length + 5 ∧
      StackMachine.runInput (decideStack program) time input =
        some (emitDecision program input, out) := by
  obtain ⟨time, out, htime, hrun, hout⟩ :=
    StackTableauEmitterCompile.machine_bounded_correct program input
  -- reflect the machine run as a counted program execution
  have hc := compile_run (StackTableauProgram.compile (StackTableauEmitterCompile.command program))
    (StackTableauProgram.encoding (StackTableauEmitterCompile.command program)) time
    (StackTableauProgram.compile (StackTableauEmitterCompile.command program)).start
    (fun j => if j = 0 then input else [])
  have hrun' : StackProgram.run (StackTableauProgram.compile
      (StackTableauEmitterCompile.command program)) time
      (StackTableauProgram.compile (StackTableauEmitterCompile.command program)).start
      (fun j => if j = 0 then input else []) = some (true, out) := by
    rw [← hc]; exact hrun
  obtain ⟨t, ht, hexec⟩ := run_exists_exec _ _ _ _ _ hrun'
  obtain ⟨s, out', hs, hcheck⟩ := exec_matchCode (k := 6 + StackTableauEmitterCompile.programSpace
    program) out
  have hseq := exec_seq (StackTableauProgram.compile (StackTableauEmitterCompile.command program))
    (matchCode (k := 6 + StackTableauEmitterCompile.programSpace program)) hexec hcheck
  have hm := compile_exec (decideEncoding program) hseq
  refine ⟨t + s, out', by omega, ?_⟩
  have hdec : decide (out 0 = emptyClauseCode) = emitDecision program input := by
    rw [hout]
    unfold emitDecision
    exact decide_eq_decide.mpr (encode_eq_emptyClauseCode_iff _)
  rw [← hdec]
  exact hm

/-- The one-tape machine deciding the emitter's acceptance condition. -/
def decideMachine (program : ClauseProgram 1) : Machine :=
  StackCompile.compile (decideStack program)

theorem decideMachine_polynomial (program : ClauseProgram 1) :
    PolynomialTimeMachine (decideMachine program) := by
  apply StackCompile.polynomialTimeMachine_of_stack (decideStack program)
    (fun n => StackTableauEmitterCompile.machineBudget program n + 5)
    ((StackTableauEmitterCompile.machineBudget_polynomial program).add
      (PolynomialBound.constant 5))
  intro input
  obtain ⟨time, out, ht, hr⟩ := decideStack_runs program input
  exact ⟨time, _, out, ht, hr⟩

theorem decideMachine_accepts_iff (program : ClauseProgram 1) (input : Word) :
    Accepts (decideMachine program) input ↔
      program.emit input (fun _ => input.length) = [[]] := by
  obtain ⟨time, out, _, hr⟩ := decideStack_runs program input
  rw [decideMachine, StackCompile.accepts_iff (decideStack program) input ⟨time, _, out, hr⟩]
  constructor
  · rintro ⟨time', regs, h⟩
    have heq := StackMachine.run_deterministic (decideStack program)
      (StackMachine.initial (decideStack program) input) h hr
    have hb : emitDecision program input = true := (congrArg Prod.fst heq).symm
    simpa [emitDecision] using hb
  · intro h
    have hb : emitDecision program input = true := by simpa [emitDecision] using h
    rw [hb] at hr
    exact ⟨time, out, hr⟩

/-- An NP verifier written as an emitter: `L` is in NP when its members are exactly the words
having a polynomially bounded certificate on which the emitter emits exactly `[[]]`. -/
theorem inNP_of_emitter {L : Language} (program : ClauseProgram 1) (c e : Nat)
    (h : ∀ x, L x ↔ ∃ w : Word, w.length ≤ powerBound c e x.length ∧
      program.emit (pairWords x w) (fun _ => (pairWords x w).length) = [[]]) :
    InNP L := by
  refine ⟨decideMachine program, c, e, decideMachine_polynomial program, ?_⟩
  intro x
  rw [h x]
  constructor
  · rintro ⟨w, hw, he⟩
    exact ⟨w, hw, (decideMachine_accepts_iff program _).mpr he⟩
  · rintro ⟨w, hw, ha⟩
    exact ⟨w, hw, (decideMachine_accepts_iff program _).mp ha⟩

end Complexity.Planar
