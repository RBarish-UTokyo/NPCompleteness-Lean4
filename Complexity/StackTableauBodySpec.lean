module

public import Complexity.StackTableauNumCorrect
import Lean.Elab.Tactic.Omega

@[expose] public section

namespace Complexity.StackTableauEmitterCompile

open StackTableauEmitter
open StackTableauProgram (Command Exec)
open StackMachine (Registers)

/-- A clause emitter preserves lexical variables and input, while modifying
output (0), emitted-clause count (2), arithmetic counter (4), and its suffix. -/
def BodyFrame {k : Nat} (base : Nat) (before after : Registers k) : Prop :=
  ∀ j, j.val < base → j ≠ register k 0 → j ≠ register k 2 → j ≠ register k 4 → after j = before j

theorem BodyFrame.refl {k : Nat} (base : Nat) (r : Registers k) : BodyFrame base r r := by
  intro _ _ _ _ _; rfl

theorem BodyFrame.trans {k base : Nat} {r s t : Registers k}
    (hrs : BodyFrame base r s) (hst : BodyFrame base s t) : BodyFrame base r t := by
  intro j hj h0 h2 h4
  exact (hst j hj h0 h2 h4).trans (hrs j hj h0 h2 h4)

theorem BodyFrame.weaken {k base base' : Nat} {r s : Registers k}
    (h : BodyFrame base' r s) (hb : base ≤ base') : BodyFrame base r s := by
  intro j hj h0 h2 h4
  exact h j (by omega) h0 h2 h4

theorem BodyFrame.set {k base : Nat} {target : Fin (k + 1)} (r : Registers k)
    (value : List Bool)
    (h : target = register k 0 ∨ target = register k 2 ∨ target = register k 4 ∨ base ≤ target.val) :
    BodyFrame base r (StackMachine.set r target value) := by
  intro j hj h0 h2 h4
  apply StackMachine.set_other r _
  intro heq
  subst j
  rcases h with h | h | h | h
  · exact h0 h
  · exact h2 h
  · exact h4 h
  · omega

theorem Frame.toBody {k base base' : Nat} {dst : Fin (k + 1)} {r s : Registers k}
    (h : Frame base' dst r s) (hb : base ≤ base')
    (hd : dst = register k 0 ∨ dst = register k 2 ∨ base ≤ dst.val) : BodyFrame base r s := by
  intro j hj h0 h2 h4
  apply h j (by omega) _ h4
  intro heq
  rcases hd with hd | hd | hd
  · exact h0 (heq.trans hd)
  · exact h2 (heq.trans hd)
  · subst j; omega

theorem BodyFrame.input {k base : Nat} {r s : Registers k} (h : BodyFrame base r s)
    (hb : 5 ≤ base) (hk : 5 ≤ k + 1) : s (register k 1) = r (register k 1) := by
  exact h _ (by rw [register_val (by omega)]; omega)
    (register_ne (by omega) (by omega) (by omega))
    (register_ne (by omega) (by omega) (by omega))
    (register_ne (by omega) (by omega) (by omega))

theorem BodyFrame.scratch {k base : Nat} {r s : Registers k} (h : BodyFrame base r s)
    (hb : 5 ≤ base) (hk : 5 ≤ k + 1) : s (register k 3) = r (register k 3) := by
  exact h _ (by rw [register_val (by omega)]; omega)
    (register_ne (by omega) (by omega) (by omega))
    (register_ne (by omega) (by omega) (by omega))
    (register_ne (by omega) (by omega) (by omega))

theorem BodyFrame.env {k n base : Nat} {r s : Registers k} (h : BodyFrame base r s)
    (envRegisters : Fin n → Fin (k + 1))
    (he : ∀ i, 5 ≤ (envRegisters i).val ∧ (envRegisters i).val < base)
    (hk : 5 ≤ k + 1) (i : Fin n) : s (envRegisters i) = r (envRegisters i) := by
  have hi := he i
  exact h _ hi.2
    (Ne.symm (register_ne_fin (by omega) (by omega)))
    (Ne.symm (register_ne_fin (by omega) (by omega)))
    (Ne.symm (register_ne_fin (by omega) (by omega)))

/-- Exact streamed bytes and exact increment of the clause counter, with all
lexically bound variables and the original input preserved. -/
def BodyCorrect {n : Nat} (program : ClauseProgram n) : Prop :=
  ∀ {k : Nat} (envRegisters : Fin n → Fin (k + 1)) (env : Env n)
    (base : Nat) (input : SAT.Word) (r : Registers k),
    5 ≤ base →
    (∀ i, 5 ≤ (envRegisters i).val ∧ (envRegisters i).val < base) →
    base + programSpace program ≤ k + 1 →
    (∀ i, r (envRegisters i) = List.replicate (env i) true) →
    r (register k 1) = input → r (register k 3) = [] →
    ∃ time out, Exec (compileBody envRegisters base program) r time (true, out) ∧
      out (register k 0) = SAT.writeValues SAT.encodeClause (program.emit input env) ++ r (register k 0) ∧
      out (register k 2) = List.replicate (program.emit input env).length true ++ r (register k 2) ∧
      BodyFrame base r out

theorem writeValues_append {α : Type} (encode : α → SAT.Word) (a b : List α) :
    SAT.writeValues encode (a ++ b) = SAT.writeValues encode a ++ SAT.writeValues encode b := by
  induction a with
  | nil => rfl
  | cons head tail ih => simp [SAT.writeValues, ih, List.append_assoc]

abbrev WorkFrame {k : Nat} (base : Nat) (before after : Registers k) : Prop :=
  Frame base (register k 4) before after

theorem work_toBody {k base : Nat} {r s : Registers k} (h : WorkFrame base r s) :
    BodyFrame base r s := by
  intro j hj _ _ h4
  exact h j hj h4 h4

theorem work_output {k base : Nat} {r s : Registers k} (h : WorkFrame base r s)
    (hb : 5 ≤ base) (hk : 5 ≤ k + 1) : s (register k 0) = r (register k 0) := by
  exact h _ (by rw [register_val (by omega)]; omega)
    (register_ne (by omega) (by omega) (by omega))
    (register_ne (by omega) (by omega) (by omega))

theorem work_count {k base : Nat} {r s : Registers k} (h : WorkFrame base r s)
    (hb : 5 ≤ base) (hk : 5 ≤ k + 1) : s (register k 2) = r (register k 2) := by
  exact h _ (by rw [register_val (by omega)]; omega)
    (register_ne (by omega) (by omega) (by omega))
    (register_ne (by omega) (by omega) (by omega))

/-- Evaluate a number entirely in the work suffix, preserving output/count. -/
theorem eval_work_num {n k : Nat} (expression : NumExpr n)
    (envRegisters : Fin n → Fin (k + 1)) (env : Env n)
    (base dest next : Nat) (r : Registers k)
    (hb : 5 ≤ base) (hd : base ≤ dest) (hn : dest < next)
    (he : ∀ i, 5 ≤ (envRegisters i).val ∧ (envRegisters i).val < base)
    (hk : next + numSpace expression ≤ k + 1)
    (hv : ∀ i, r (envRegisters i) = List.replicate (env i) true)
    (hs : r (register k 3) = []) :
    ∃ time out, Exec (compileNum envRegisters (register k dest) next expression) r time (true, out) ∧
      out (register k dest) = List.replicate (expression.eval env) true ∧
      Frame next (register k dest) r out ∧ WorkFrame base r out := by
  have hdest : dest < k + 1 := by omega
  obtain ⟨time, out, hex, hval, hframe⟩ :=
    compileNum_correct expression envRegisters env (register k dest) next r
      (by rw [register_val hdest]; omega) (by rw [register_val hdest]; omega)
      (by intro i; refine ⟨(he i).1, by have := (he i).2; omega, ?_⟩
          apply Ne.symm (register_ne_fin hdest _)
          have := (he i).2
          omega) hk hv hs
  exact ⟨time, out, hex, hval, hframe,
    hframe.weaken (by omega) (Or.inr (by rw [register_val hdest]; omega))⟩

end Complexity.StackTableauEmitterCompile
