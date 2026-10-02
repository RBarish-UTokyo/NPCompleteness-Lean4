module

public import Complexity.StackTableauBodyBounds
public import Complexity.StackTableauBounds
public import Complexity.StackCompile
import Lean.Elab.Tactic.Omega

@[expose] public section

namespace Complexity.StackTableauEmitterCompile

open StackTableauEmitter
open StackTableauProgram (Command Exec)
open StackMachine (Registers)

/-- Bound on all elementary instructions, including input preservation and the
serialized formula's clause-count header. -/
def machineBudget (program : ClauseProgram 1) (n : Nat) : Nat :=
  11 * n + 20 + bodyCost program (program.envelope n) + 5 * program.outputBound n

theorem machineBudget_polynomial (program : ClauseProgram 1) : PolynomialBound (machineBudget program) :=
  ((((PolynomialBound.constant 11).mul PolynomialBound.identity).add (PolynomialBound.constant 20)).add
    ((polynomialBound_bodyCost program).comp program.envelope_polynomial)).add
    ((PolynomialBound.constant 5).mul program.outputBound_polynomial)

/-- Total execution of the concrete finite compiler, with an actual polynomial
step bound on every binary input and exact serialized output. -/
theorem machine_bounded_correct (program : ClauseProgram 1) (input : SAT.Word) :
    ∃ time out, time ≤ machineBudget program input.length ∧
      StackMachine.runInput (machine program) time input = some (true, out) ∧
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
  let C := program.envelope input.length
  have hnC : input.length ≤ C := program.envelope_ge input.length
  have hwr : WorkBound r C := by
    intro j h0 h2
    have hj : j ≠ 0 := by intro h; subst j; simp at h0
    simp [r, hj]
  have hwcopied : WorkBound copied C := hwr.set _ _ (by rw [hr (by omega)]; simpa using hnC)
  have hwcleared : WorkBound cleared C := hwcopied.set _ _ (by simp)
  have hwready : WorkBound ready C := hwcleared.set _ _ (by
    simp [cleared, copied, Ne.symm h01, hr (a := 0) (by omega)]
    exact hnC)
  obtain ⟨bt, bodyout, bex, bo, bc, bf, hbt, _⟩ := compileBody_bounded_correct program (fun _ => register k 5)
    (fun _ => input.length) 6 input ready (by omega)
    (by intro i; rw [register_val (by omega)]; omega) (by dsimp [k]; omega) henv hinput hsready
    C (program.fits_envelope input (fun _ => input.length) input.length (fun _ => Nat.le_refl _)) hwready
  have hbsc : bodyout (register k 3) = [] := (bf.scratch (by omega) (by omega)).trans hsready
  have header := Exec.prependNat
    (register_ne (k := k) (a := 2) (b := 0) (by omega) (by omega) (by omega))
    (register_ne (k := k) (a := 2) (b := 3) (by omega) (by omega) (by omega)) h03 hbsc
  have hex := Exec.seq hc (Exec.seq hclear (Exec.seq hlen (Exec.seq bex header)))
  have hinit1 : (r (register k 1)).length + 5 * (r (register k 0)).length + 6 =
      5 * input.length + 6 := by rw [hr (by omega), hr (by omega)]; simp
  have hinit2 : (copied (register k 0)).length + 2 = input.length + 2 := by
    simp [copied, h01, hr (a := 0) (by omega)]
  have hinit3 : (cleared (register k 5)).length + 5 * (cleared (register k 1)).length + 6 =
      5 * input.length + 6 := by
    simp [cleared, copied, Ne.symm h01,
      register_ne (k := k) (a := 5) (b := 0) (by omega) (by omega) (by omega),
      register_ne (k := k) (a := 5) (b := 1) (by omega) (by omega) (by omega),
      hr (a := 5) (by omega), hr (a := 0) (by omega)]
  have hcount : (bodyout (register k 2)).length ≤ program.outputBound input.length := by
    rw [bc, hcountready]
    simp only [List.append_nil, List.length_replicate]
    exact program.length_emit_le input (fun _ => input.length) input.length (fun _ => Nat.le_refl _)
  refine ⟨_, _, ?_, hex.machine_run, ?_⟩
  · change (r (register k 1)).length + 5 * (r (register k 0)).length + 6 +
      ((copied (register k 0)).length + 2 +
      ((cleared (register k 5)).length + 5 * (cleared (register k 1)).length + 6 +
      (bt + (5 * (bodyout (register k 2)).length + 6)))) ≤ _
    rw [hinit1, hinit2, hinit3]
    dsimp [machineBudget]
    dsimp [C] at hbt
    omega
  · change StackMachine.set bodyout (register k 0)
      (SAT.writeNat (bodyout (register k 2)).length ++ bodyout (register k 0)) (0 : Fin (k + 1)) = _
    rw [← hz]
    simp only [StackMachine.set_same]
    rw [bc, bo, hcountready, houtready]
    simp [SAT.encode, SAT.writeList]

end Complexity.StackTableauEmitterCompile

namespace Complexity.StackTableauEmitter

/-- Every fixed emitter is polynomial-time on the original single-tape model.
This follows from counted execution, not merely a bound on output length. -/
theorem polyTime_emitter (program : ClauseProgram 1) :
    PolyTime (fun input => SAT.encode (program.emit input (fun _ => input.length))) :=
  StackCompile.polyTime_of_stack (StackTableauEmitterCompile.machine program)
    (StackTableauEmitterCompile.machineBudget program)
    (StackTableauEmitterCompile.machineBudget_polynomial program)
    (StackTableauEmitterCompile.machine_bounded_correct program)

end Complexity.StackTableauEmitter
