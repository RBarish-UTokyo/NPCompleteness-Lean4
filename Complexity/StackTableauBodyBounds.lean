module

public import Complexity.StackTableauBodyBoundedSpec
public import Complexity.StackTableauLoopBounds
public import Complexity.StackTableauBranchBounds
import Lean.Elab.Tactic.Omega

@[expose] public section

namespace Complexity.StackTableauEmitterCompile

open StackTableauEmitter
open StackTableauProgram (Exec)

theorem compile_clause_body_bounded {n : Nat} (literals : List (LiteralExpr n)) :
    BodyBounded (.clause literals) := by
  intro k er env base input r hb he hk hv hin hs C hfits hw
  obtain ⟨time, out, hex, _, _, hf, ht, hw'⟩ := compile_clause_bounded literals er env base input r
    hb he hk hv hin hs C hfits.2 hfits.1 hw
  exact ⟨time, out, hex, hf, ht, hw'⟩

theorem compile_seq_bounded {n : Nat} (first second : ClauseProgram n)
    (hf : BodyBounded first) (hs : BodyBounded second) : BodyBounded (.seq first second) := by
  intro k er env base input r hb he hk hv hin hscratch C hfits hw
  have hsize : base + max (programSpace first) (programSpace second) ≤ k + 1 := hk
  have hk5 : 5 ≤ k + 1 := by omega
  obtain ⟨st, middle, sex, sframe, stime, swork⟩ := hs er env base input r hb he
    (by have := Nat.le_max_right (programSpace first) (programSpace second); omega)
    hv hin hscratch C hfits.2 hw
  obtain ⟨ft, out, fex, fframe, ftime, fwork⟩ := hf er env base input middle hb he
    (by have := Nat.le_max_left (programSpace first) (programSpace second); omega)
    (by intro i; rw [sframe.env er he hk5 i]; exact hv i)
    ((sframe.input hb hk5).trans hin) ((sframe.scratch hb hk5).trans hscratch) C hfits.1 swork
  refine ⟨st + ft, out, Exec.seq sex fex, sframe.trans fframe, ?_, fwork⟩
  change st + ft ≤ bodyCost first C + bodyCost second C
  omega

theorem body_bounded_correct_of {n : Nat} (program : ClauseProgram n) (hp : BodyBounded program)
    {k : Nat} (envRegisters : Fin n → Fin (k + 1)) (env : Env n)
    (base : Nat) (input : SAT.Word) (r : StackMachine.Registers k)
    (hb : 5 ≤ base)
    (he : ∀ i, 5 ≤ (envRegisters i).val ∧ (envRegisters i).val < base)
    (hk : base + programSpace program ≤ k + 1)
    (hv : ∀ i, r (envRegisters i) = List.replicate (env i) true)
    (hin : r (register k 1) = input) (hs : r (register k 3) = [])
    (C : Nat) (hfits : program.Fits input env C) (hw : WorkBound r C) :
    ∃ time out, Exec (compileBody envRegisters base program) r time (true, out) ∧
      out (register k 0) = SAT.writeValues SAT.encodeClause (program.emit input env) ++ r (register k 0) ∧
      out (register k 2) = List.replicate (program.emit input env).length true ++ r (register k 2) ∧
      BodyFrame base r out ∧ time ≤ bodyCost program C ∧ WorkBound out C := by
  obtain ⟨time, out, hex, hf, ht, hw'⟩ := hp envRegisters env base input r hb he hk hv hin hs C hfits hw
  obtain ⟨semanticTime, semanticOut, semanticExec, ho, hc, _⟩ :=
    compileBody_correct program envRegisters env base input r hb he hk hv hin hs
  have unique : out = semanticOut := congrArg Prod.snd (exec_result_unique hex semanticExec)
  subst semanticOut
  exact ⟨time, out, hex, ho, hc, hf, ht, hw'⟩

/-- Every fixed clause-emitter syntax has a real stack execution bounded by
a polynomial in a single capacity encompassing all its lexical evaluations. -/
theorem compileBody_bounded {n : Nat} (program : ClauseProgram n) : BodyBounded program := by
  induction program with
  | clause literals => exact compile_clause_body_bounded literals
  | seq first second ihf ihs => exact compile_seq_bounded first second ihf ihs
  | forDown bound body ih => exact compile_forDown_bounded bound body ih
  | ifLe left right yes no ihy ihn => exact compile_ifLe_bounded left right yes no ihy ihn
  | ifInput index empty zero one ihe ihz iho => exact compile_ifInput_bounded index empty zero one ihe ihz iho

theorem compileBody_bounded_correct {n : Nat} (program : ClauseProgram n)
    {k : Nat} (envRegisters : Fin n → Fin (k + 1)) (env : Env n)
    (base : Nat) (input : SAT.Word) (r : StackMachine.Registers k)
    (hb : 5 ≤ base)
    (he : ∀ i, 5 ≤ (envRegisters i).val ∧ (envRegisters i).val < base)
    (hk : base + programSpace program ≤ k + 1)
    (hv : ∀ i, r (envRegisters i) = List.replicate (env i) true)
    (hin : r (register k 1) = input) (hs : r (register k 3) = [])
    (C : Nat) (hfits : program.Fits input env C) (hw : WorkBound r C) :
    ∃ time out, Exec (compileBody envRegisters base program) r time (true, out) ∧
      out (register k 0) = SAT.writeValues SAT.encodeClause (program.emit input env) ++ r (register k 0) ∧
      out (register k 2) = List.replicate (program.emit input env).length true ++ r (register k 2) ∧
      BodyFrame base r out ∧ time ≤ bodyCost program C ∧ WorkBound out C :=
  body_bounded_correct_of program (compileBody_bounded program) envRegisters env base input r
    hb he hk hv hin hs C hfits hw

end Complexity.StackTableauEmitterCompile
