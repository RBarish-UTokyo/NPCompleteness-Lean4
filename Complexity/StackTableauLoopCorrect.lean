module

public import Complexity.StackTableauBodySpec
import Lean.Elab.Tactic.Omega

/-!
Execution correctness for bounded emitter loops.  The machine visits the loop
indices in ascending order and prepends each result, giving precisely the
descending order in the emitter's denotational semantics.
-/

@[expose] public section

namespace Complexity.StackTableauEmitterCompile

open StackTableauEmitter
open StackTableauProgram (Command Exec)
open StackMachine (Registers)

def loopClauses {n : Nat} (body : ClauseProgram (n + 1)) (input : SAT.Word)
    (env : Env n) (first count : Nat) : SAT.CNF :=
  (List.range count).reverse.flatMap (fun j => body.emit input (extend (first + j) env))

theorem loopClauses_zero {n : Nat} (body : ClauseProgram (n + 1)) (input : SAT.Word)
    (env : Env n) (first : Nat) : loopClauses body input env first 0 = [] := rfl

theorem loopClauses_succ {n : Nat} (body : ClauseProgram (n + 1)) (input : SAT.Word)
    (env : Env n) (first count : Nat) :
    loopClauses body input env first (count + 1) =
      loopClauses body input env (first + 1) count ++ body.emit input (extend first env) := by
  simp [loopClauses, List.range_succ_eq_map, List.reverse_cons, ← List.map_reverse,
    List.flatMap_append, List.flatMap_map, Nat.add_comm, Nat.add_left_comm]

theorem BodyFrame.local {k base : Nat} {r s : Registers k} (h : BodyFrame base r s)
    (j : Fin (k + 1)) (hj : 5 ≤ j.val) (hb : j.val < base) : s j = r j := by
  exact h j hb (Ne.symm (register_ne_fin (by omega) (by omega)))
    (Ne.symm (register_ne_fin (by omega) (by omega)))
    (Ne.symm (register_ne_fin (by omega) (by omega)))

theorem compile_loop_correct {n : Nat} (body : ClauseProgram (n + 1))
    (hbody : BodyCorrect body) {k : Nat}
    (envRegisters : Fin n → Fin (k + 1)) (env : Env n) (base : Nat)
    (input : SAT.Word) (first count : Nat) (r : Registers k)
    (hb : 5 ≤ base)
    (he : ∀ i, 5 ≤ (envRegisters i).val ∧ (envRegisters i).val < base)
    (hk : base + 2 + programSpace body ≤ k + 1)
    (hv : ∀ i, r (envRegisters i) = List.replicate (env i) true)
    (hin : r (register k 1) = input) (hs : r (register k 3) = [])
    (hc : r (register k base) = List.replicate count true)
    (hi : r (register k (base + 1)) = List.replicate first true) :
    ∃ time out,
      Exec (.repeat (register k base)
        (.seq (compileBody (Fin.cases (register k (base + 1)) envRegisters) (base + 2) body)
          (.push (register k (base + 1)) true))) r time (true, out) ∧
      out (register k 0) = SAT.writeValues SAT.encodeClause (loopClauses body input env first count) ++ r (register k 0) ∧
      out (register k 2) = List.replicate (loopClauses body input env first count).length true ++ r (register k 2) ∧
      BodyFrame base r out := by
  have hbase : base < k + 1 := by omega
  have hnext : base + 1 < k + 1 := by omega
  have hsmall : 5 ≤ k + 1 := by omega
  have hbn : register k base ≠ register k (base + 1) := register_ne hbase hnext (by omega)
  have hb0 : register k base ≠ register k 0 := register_ne hbase (by omega) (by omega)
  have hb1 : register k base ≠ register k 1 := register_ne hbase (by omega) (by omega)
  have hb2 : register k base ≠ register k 2 := register_ne hbase (by omega) (by omega)
  have hb3 : register k base ≠ register k 3 := register_ne hbase (by omega) (by omega)
  have hn0 : register k (base + 1) ≠ register k 0 := register_ne hnext (by omega) (by omega)
  have hn1 : register k (base + 1) ≠ register k 1 := register_ne hnext (by omega) (by omega)
  have hn2 : register k (base + 1) ≠ register k 2 := register_ne hnext (by omega) (by omega)
  have hn3 : register k (base + 1) ≠ register k 3 := register_ne hnext (by omega) (by omega)
  induction count generalizing first r with
  | zero =>
      refine ⟨2, r, Exec.repeatDone hc, ?_, ?_, BodyFrame.refl base r⟩ <;>
        simp [loopClauses, SAT.writeValues]
  | succ count ih =>
      let popped := StackMachine.set r (register k base) (List.replicate count true)
      have popped_frame : BodyFrame base r popped :=
        BodyFrame.set r _ (Or.inr (Or.inr (Or.inr (by rw [register_val hbase]; omega))))
      have henv : ∀ i : Fin (n + 1), 5 ≤ (Fin.cases (register k (base + 1)) envRegisters i : Fin (k + 1)).val ∧
          (Fin.cases (register k (base + 1)) envRegisters i : Fin (k + 1)).val < base + 2 := by
        intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · simp only [Fin.cases_zero, register_val hnext]
          omega
        · simpa only [Fin.cases_succ] using
            And.intro (he j).1 (show (envRegisters j).val < base + 2 by have := (he j).2; omega)
      have hvalue : ∀ i : Fin (n + 1), popped (Fin.cases (register k (base + 1)) envRegisters i) =
          List.replicate (extend first env i) true := by
        intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · simpa [extend, popped, Ne.symm hbn] using hi
        · simpa only [Fin.cases_succ, extend] using
            ((popped_frame.env envRegisters he hsmall j).trans (hv j))
      obtain ⟨t, middle, hex, hout, hcount, hframe⟩ :=
        hbody (Fin.cases (register k (base + 1)) envRegisters) (extend first env)
          (base + 2) input popped (by omega) henv hk hvalue
          ((popped_frame.input hb hsmall).trans hin)
          ((popped_frame.scratch hb hsmall).trans hs)
      let advanced := StackMachine.set middle (register k (base + 1))
        (true :: middle (register k (base + 1)))
      have advanced_frame : BodyFrame base middle advanced :=
        BodyFrame.set middle _ (Or.inr (Or.inr (Or.inr (by rw [register_val hnext]; omega))))
      have combined : BodyFrame base r advanced :=
        popped_frame.trans ((hframe.weaken (by omega)).trans advanced_frame)
      have hcounter : advanced (register k base) = List.replicate count true := by
        rw [show advanced (register k base) = middle (register k base) by simp [advanced, hbn]]
        rw [hframe.local (register k base) (by rw [register_val hbase]; omega)
          (by rw [register_val hbase]; omega)]
        simp [popped]
      have hindex : advanced (register k (base + 1)) = List.replicate (first + 1) true := by
        have hmid := hframe.local (register k (base + 1))
          (by rw [register_val hnext]; omega) (by rw [register_val hnext]; omega)
        simp [advanced, hmid, popped, Ne.symm hbn, hi, List.replicate_succ]
      obtain ⟨s, out, hrest, restout, restcount, restframe⟩ :=
        ih (first + 1) advanced
          (fun i => (combined.env envRegisters he hsmall i).trans (hv i))
          ((combined.input hb hsmall).trans hin)
          ((combined.scratch hb hsmall).trans hs) hcounter hindex
      refine ⟨t + 2 + s + 1, out,
        Exec.repeatNext (by simpa [List.replicate_succ] using hc)
          (Exec.seq hex (Exec.push (register k (base + 1)) true middle)) hrest,
        ?_, ?_, combined.trans restframe⟩
      · rw [restout, loopClauses_succ, writeValues_append]
        simp only [advanced, StackMachine.set_other _ (Ne.symm hn0), hout,
          popped, StackMachine.set_other _ (Ne.symm hb0), List.append_assoc]
      · rw [restcount, loopClauses_succ, List.length_append, ← List.replicate_append_replicate]
        simp only [advanced, StackMachine.set_other _ (Ne.symm hn2), hcount,
          popped, StackMachine.set_other _ (Ne.symm hb2), List.append_assoc]

theorem compile_forDown_correct {n : Nat} (bound : NumExpr n)
    (body : ClauseProgram (n + 1)) (hbody : BodyCorrect body) :
    BodyCorrect (.forDown bound body) := by
  intro k envRegisters env base input r hb he hk hv hin hs
  have hspace : base + (2 + max (numSpace bound) (programSpace body)) ≤ k + 1 := hk
  have hbase : base < k + 1 := by omega
  have hnext : base + 1 < k + 1 := by omega
  have hsmall : 5 ≤ k + 1 := by omega
  obtain ⟨t, middle, hnum, hval, _, hwork⟩ :=
    eval_work_num bound envRegisters env base base (base + 2) r hb (by omega) (by omega)
      he (by have := Nat.le_max_left (numSpace bound) (programSpace body); omega) hv hs
  let ready := StackMachine.set middle (register k (base + 1)) []
  have hready : WorkFrame base middle ready :=
    Frame.set middle [] (Or.inr (Or.inr (by rw [register_val hnext]; omega)))
  have hpre : WorkFrame base r ready := hwork.trans hready
  obtain ⟨s, out, hloop, hout, hcount, hframe⟩ :=
    compile_loop_correct body hbody envRegisters env base input 0 (bound.eval env) ready hb he
      (by have := Nat.le_max_right (numSpace bound) (programSpace body); omega)
      (fun i => ((work_toBody hpre).env envRegisters he hsmall i).trans (hv i))
      (((work_toBody hpre).input hb hsmall).trans hin)
      (((work_toBody hpre).scratch hb hsmall).trans hs)
      (by simpa [ready, register_ne hbase hnext (by omega)] using hval)
      (by simp [ready])
  refine ⟨t + ((middle (register k (base + 1))).length + 3 + s), out,
    Exec.seq hnum (Exec.seq (by
      simpa [ready] using exec_constant (register k (base + 1)) 0 middle) hloop), ?_, ?_,
    (work_toBody hpre).trans hframe⟩
  · simpa [ClauseProgram.emit, loopClauses, work_output hpre hb hsmall] using hout
  · simpa [ClauseProgram.emit, loopClauses, work_count hpre hb hsmall] using hcount

end Complexity.StackTableauEmitterCompile
