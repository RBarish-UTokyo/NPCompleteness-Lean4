module

public import Complexity.StackTableauLoopCorrect
public import Complexity.StackTableauBodyBoundedSpec
public import Complexity.StackTableauNumBounds
import Lean.Elab.Tactic.Omega

@[expose] public section

namespace Complexity.StackTableauEmitterCompile

open StackTableauEmitter
open StackTableauProgram (Command Exec)
open StackMachine (Registers)

/-- A bounded loop uses one counter-pop and one two-step index increment per
iteration in addition to the actual execution time of its compiled body. -/
theorem compile_loop_bounded {n : Nat} (body : ClauseProgram (n + 1))
    {k : Nat} (envRegisters : Fin n → Fin (k + 1)) (env : Env n) (base : Nat)
    (input : SAT.Word) (capacity budget limit : Nat)
    (hbody : ∀ index, index < limit → ∀ state : Registers k,
      (∀ j, state (Fin.cases (register k (base + 1)) envRegisters j) =
        List.replicate (extend index env j) true) →
      state (register k 1) = input → state (register k 3) = [] →
      WorkBound state capacity →
      ∃ time out,
        Exec (compileBody (Fin.cases (register k (base + 1)) envRegisters) (base + 2) body)
          state time (true, out) ∧
        BodyFrame (base + 2) state out ∧ time ≤ budget ∧ WorkBound out capacity)
    (first count : Nat) (r : Registers k)
    (hb : 5 ≤ base)
    (he : ∀ i, 5 ≤ (envRegisters i).val ∧ (envRegisters i).val < base)
    (hk : base + 2 + programSpace body ≤ k + 1)
    (hv : ∀ i, r (envRegisters i) = List.replicate (env i) true)
    (hin : r (register k 1) = input) (hs : r (register k 3) = [])
    (hc : r (register k base) = List.replicate count true)
    (hi : r (register k (base + 1)) = List.replicate first true)
    (hrange : first + count ≤ limit) (hcapacity : first + count ≤ capacity)
    (hwork : WorkBound r capacity) :
    ∃ time out,
      Exec (.repeat (register k base)
        (.seq (compileBody (Fin.cases (register k (base + 1)) envRegisters) (base + 2) body)
          (.push (register k (base + 1)) true))) r time (true, out) ∧
      BodyFrame base r out ∧ time ≤ count * (budget + 3) + 2 ∧ WorkBound out capacity := by
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
      exact ⟨2, r, Exec.repeatDone hc, BodyFrame.refl base r, by simp, hwork⟩
  | succ count ih =>
      let popped := StackMachine.set r (register k base) (List.replicate count true)
      have popped_frame : BodyFrame base r popped :=
        BodyFrame.set r _ (Or.inr (Or.inr (Or.inr (by rw [register_val hbase]; omega))))
      have hvalue : ∀ i : Fin (n + 1), popped (Fin.cases (register k (base + 1)) envRegisters i) =
          List.replicate (extend first env i) true := by
        intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · simpa [extend, popped, Ne.symm hbn] using hi
        · simpa only [Fin.cases_succ, extend] using
            ((popped_frame.env envRegisters he hsmall j).trans (hv j))
      have popped_work : WorkBound popped capacity :=
        hwork.set _ _ (by simp only [List.length_replicate]; omega)
      obtain ⟨t, middle, hex, hframe, ht, middle_work⟩ :=
        hbody first (by omega) popped hvalue
          ((popped_frame.input hb hsmall).trans hin)
          ((popped_frame.scratch hb hsmall).trans hs) popped_work
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
      have advanced_work : WorkBound advanced capacity :=
        middle_work.set _ _ (by
          have hh : (advanced (register k (base + 1))).length ≤ capacity := by
            rw [hindex, List.length_replicate]
            omega
          simpa [advanced] using hh)
      obtain ⟨s, out, hrest, restframe, htime, out_work⟩ :=
        ih (first + 1) advanced
          (fun i => (combined.env envRegisters he hsmall i).trans (hv i))
          ((combined.input hb hsmall).trans hin)
          ((combined.scratch hb hsmall).trans hs) hcounter hindex
          (by omega) (by omega) advanced_work
      refine ⟨t + 2 + s + 1, out,
        Exec.repeatNext (by simpa [List.replicate_succ] using hc)
          (Exec.seq hex (Exec.push (register k (base + 1)) true middle)) hrest,
        combined.trans restframe, ?_, out_work⟩
      rw [Nat.add_mul]
      omega

/-- Initialize the unary counter and binder, then execute the bounded loop.
The budget measures elementary stack instructions, including initialization. -/
theorem compile_forDown_bounded_core {n : Nat} (bound : NumExpr n)
    (body : ClauseProgram (n + 1)) {k : Nat}
    (envRegisters : Fin n → Fin (k + 1)) (env : Env n) (base : Nat)
    (input : SAT.Word) (r : Registers k) (capacity budget : Nat)
    (hb : 5 ≤ base)
    (he : ∀ i, 5 ≤ (envRegisters i).val ∧ (envRegisters i).val < base)
    (hk : base + programSpace (.forDown bound body) ≤ k + 1)
    (hv : ∀ i, r (envRegisters i) = List.replicate (env i) true)
    (hin : r (register k 1) = input) (hs : r (register k 3) = [])
    (hfit : NumFits bound env capacity) (hwork : WorkBound r capacity)
    (hbody : ∀ index, index < bound.eval env → ∀ state : Registers k,
      (∀ j, state (Fin.cases (register k (base + 1)) envRegisters j) =
        List.replicate (extend index env j) true) →
      state (register k 1) = input → state (register k 3) = [] →
      WorkBound state capacity →
      ∃ time out,
        Exec (compileBody (Fin.cases (register k (base + 1)) envRegisters) (base + 2) body)
          state time (true, out) ∧
        BodyFrame (base + 2) state out ∧ time ≤ budget ∧ WorkBound out capacity) :
    ∃ time out, Exec (compileBody envRegisters base (.forDown bound body)) r time (true, out) ∧
      BodyFrame base r out ∧
      time ≤ numCost bound capacity + (capacity + 3) + capacity * (budget + 3) + 2 ∧
      WorkBound out capacity := by
  have hspace : base + (2 + max (numSpace bound) (programSpace body)) ≤ k + 1 := hk
  have hbase : base < k + 1 := by omega
  have hnext : base + 1 < k + 1 := by omega
  have hsmall : 5 ≤ k + 1 := by omega
  obtain ⟨t, middle, hnum, hval, hframe, htime, middle_work⟩ :=
    compileNum_bounded bound envRegisters env (register k base) (base + 2) r
      (by rw [register_val hbase]; omega) (by rw [register_val hbase]; omega)
      (by intro i; refine ⟨(he i).1, by have := (he i).2; omega, ?_⟩
          exact Ne.symm (register_ne_fin hbase (by have := (he i).2; omega)))
      (by have := Nat.le_max_left (numSpace bound) (programSpace body); omega)
      hv hs capacity hfit hwork
  have hworkframe : WorkFrame base r middle :=
    hframe.weaken (by omega) (Or.inr (by rw [register_val hbase]; omega))
  let ready := StackMachine.set middle (register k (base + 1)) []
  have hready : WorkFrame base middle ready :=
    Frame.set middle [] (Or.inr (Or.inr (by rw [register_val hnext]; omega)))
  have hpre : WorkFrame base r ready := hworkframe.trans hready
  have ready_work : WorkBound ready capacity := middle_work.set _ _ (by simp)
  obtain ⟨s, out, hloop, out_frame, loop_time, out_work⟩ :=
    compile_loop_bounded body envRegisters env base input capacity budget (bound.eval env)
      hbody 0 (bound.eval env) ready hb he
      (by have := Nat.le_max_right (numSpace bound) (programSpace body); omega)
      (fun i => ((work_toBody hpre).env envRegisters he hsmall i).trans (hv i))
      (((work_toBody hpre).input hb hsmall).trans hin)
      (((work_toBody hpre).scratch hb hsmall).trans hs)
      (by simpa [ready, register_ne hbase hnext (by omega)] using hval)
      (by simp [ready]) (by omega) (by simpa using hfit.value) ready_work
  refine ⟨t + ((middle (register k (base + 1))).length + 3 + s), out,
    Exec.seq hnum (Exec.seq (by
      simpa [ready] using exec_constant (register k (base + 1)) 0 middle) hloop),
    (work_toBody hpre).trans out_frame, ?_, out_work⟩
  have hlen := middle_work.register hnext (show base + 1 ≠ 0 by omega)
    (show base + 1 ≠ 2 by omega)
  have hmul := Nat.mul_le_mul_right (budget + 3) hfit.value
  omega

theorem compile_forDown_bounded {n : Nat} (bound : NumExpr n)
    (body : ClauseProgram (n + 1)) (hbody : BodyBounded body) :
    BodyBounded (.forDown bound body) := by
  intro k envRegisters env base input r hb he hk hv hin hs C hfits hwork
  have hspace : base + (2 + max (numSpace bound) (programSpace body)) ≤ k + 1 := hk
  have hnext : base + 1 < k + 1 := by omega
  apply compile_forDown_bounded_core bound body envRegisters env base input r C
    (bodyCost body C) hb he hk hv hin hs hfits.1 hwork
  intro index hindex state hval hinput hscratch hbound
  apply hbody (Fin.cases (register k (base + 1)) envRegisters) (extend index env)
    (base + 2) input state (by omega) ?_ ?_ hval hinput hscratch C
    (hfits.2 index hindex) hbound
  · intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [Fin.cases_zero, register_val hnext]
      omega
    · simpa only [Fin.cases_succ] using
        And.intro (he j).1 (show (envRegisters j).val < base + 2 by have := (he j).2; omega)
  · have := Nat.le_max_right (numSpace bound) (programSpace body)
    omega

end Complexity.StackTableauEmitterCompile
