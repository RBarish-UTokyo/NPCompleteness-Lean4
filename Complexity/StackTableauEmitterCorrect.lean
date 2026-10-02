module

public import Complexity.StackTableauLiteralCorrect
public import Complexity.StackTableauLoopCorrect
public import Complexity.StackTableauBranchCorrect
import Lean.Elab.Tactic.Omega

@[expose] public section

namespace Complexity.StackTableauEmitterCompile

open StackTableauEmitter
open StackTableauProgram (Command Exec)
open StackMachine (Registers)

/-- Structural soundness of every clause-emitter program. -/
theorem compileBody_correct {n : Nat} (program : ClauseProgram n) : BodyCorrect program := by
  induction program with
  | clause literals => exact compile_clause_correct literals
  | seq first second ihf ihs => exact compile_seq_correct first second ihf ihs
  | forDown bound body ih => exact compile_forDown_correct bound body ih
  | ifLe left right yes no ihy ihn => exact compile_ifLe_correct left right yes no ihy ihn
  | ifInput index empty zero one ihe ihz iho => exact compile_ifInput_correct index empty zero one ihe ihz iho

/-- Actual elementary-stack executions determine a unique result, even with
different successful fuel bounds. -/
theorem exec_result_unique {k : Nat} {p : Command k} {r : Registers k}
    {t s : Nat} {result result'} (h : Exec p r t result) (h' : Exec p r s result') :
    result = result' :=
  StackMachine.run_deterministic (StackTableauProgram.machine p)
    ⟨(StackTableauProgram.machine p).start, r⟩ h.machine_run h'.machine_run

/-- The concrete compiler terminates and serializes precisely the emitter's
CNF. This theorem establishes semantics; the later cost theorem bounds fuel. -/
theorem machine_correct (program : ClauseProgram 1) (input : SAT.Word) :
    ∃ time out, StackMachine.runInput (machine program) time input = some (true, out) ∧
      out 0 = SAT.encode (program.emit input (fun _ => input.length)) := by
  let k := 6 + programSpace program
  let r : Registers k := fun j => if j = 0 then input else []
  have hk : 6 ≤ k := by dsimp [k]; omega
  have h01 : register k 0 ≠ register k 1 := register_ne (by omega) (by omega) (by omega)
  have h03 : register k 0 ≠ register k 3 := register_ne (by omega) (by omega) (by omega)
  have h13 : register k 1 ≠ register k 3 := register_ne (by omega) (by omega) (by omega)
  have h15 : register k 1 ≠ register k 5 := register_ne (by omega) (by omega) (by omega)
  have h53 : register k 5 ≠ register k 3 := register_ne (by omega) (by omega) (by omega)
  have hz : register k 0 = 0 := by apply Fin.ext; exact register_val (by omega)
  have hval {a : Nat} (ha : a < k + 1) : (register k a).val = a := register_val ha
  have hr {a : Nat} (ha : a < k + 1) : r (register k a) = if a = 0 then input else [] := by
    simp only [r]
    congr 1
    apply propext
    constructor
    · intro h; have := congrArg Fin.val h; simpa [hval ha] using this
    · intro h; subst a; exact hz
  let copied := StackMachine.set r (register k 1) (r (register k 0))
  have hc : Exec (.copy (register k 0) (register k 1) (register k 3)) r _ (true, copied) :=
    Exec.copy h01 h03 h13 (by rw [hr (by omega)]; rfl)
  let cleared := StackMachine.set copied (register k 0) []
  have hclear : Exec (.clear (register k 0)) copied _ (true, cleared) := Exec.clear _ _
  have hsc : cleared (register k 3) = [] := by
    simp [cleared, copied, Ne.symm h03, Ne.symm h13, hr (a := 3) (by omega)]
  let ready := StackMachine.set cleared (register k 5) (List.replicate (cleared (register k 1)).length true)
  have hlen : Exec (.length (register k 1) (register k 5) (register k 3)) cleared _ (true, ready) :=
    Exec.length h15 h13 h53 hsc
  have hinput : ready (register k 1) = input := by
    simp [ready, cleared, copied, h15, Ne.symm h01, hr (a := 0) (by omega)]
  have henv : ∀ i : Fin 1, ready ((fun _ => register k 5) i) = List.replicate input.length true := by
    intro i
    simp [ready, cleared, copied, Ne.symm h01, hr (a := 0) (by omega)]
  have hsready : ready (register k 3) = [] := by simp [ready, Ne.symm h53, hsc]
  have houtready : ready (register k 0) = [] := by
    simp [ready, cleared, register_ne (k := k) (a := 0) (b := 5) (by omega) (by omega) (by omega)]
  have hcountready : ready (register k 2) = [] := by
    simp [ready, cleared, copied,
      register_ne (k := k) (a := 2) (b := 5) (by omega) (by omega) (by omega),
      register_ne (k := k) (a := 2) (b := 0) (by omega) (by omega) (by omega),
      register_ne (k := k) (a := 2) (b := 1) (by omega) (by omega) (by omega), hr (a := 2) (by omega)]
  obtain ⟨bt, bodyout, bex, bo, bc, bf⟩ := compileBody_correct program (fun _ => register k 5)
    (fun _ => input.length) 6 input ready (by omega)
    (by intro i; rw [register_val (by omega)]; omega) (by dsimp [k]; omega) henv hinput hsready
  have hbsc : bodyout (register k 3) = [] := (bf.scratch (by omega) (by omega)).trans hsready
  have header := Exec.prependNat
    (register_ne (k := k) (a := 2) (b := 0) (by omega) (by omega) (by omega))
    (register_ne (k := k) (a := 2) (b := 3) (by omega) (by omega) (by omega)) h03 hbsc
  have hex := Exec.seq hc (Exec.seq hclear (Exec.seq hlen (Exec.seq bex header)))
  refine ⟨_, _, hex.machine_run, ?_⟩
  change StackMachine.set bodyout (register k 0)
    (SAT.writeNat (bodyout (register k 2)).length ++ bodyout (register k 0)) (0 : Fin (k + 1)) = _
  rw [← hz]
  simp only [StackMachine.set_same]
  rw [bc, bo, hcountready, houtready]
  simp [SAT.encode, SAT.writeList]

end Complexity.StackTableauEmitterCompile
