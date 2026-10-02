module

public import Complexity.StackTableauBodySpec
import Lean.Elab.Tactic.Omega

@[expose] public section

namespace Complexity.StackTableauEmitterCompile

open StackTableauEmitter
open StackTableauProgram (Command Exec)
open StackMachine (Registers)

theorem compile_seq_correct {n : Nat} (first second : ClauseProgram n)
    (hf : BodyCorrect first) (hs : BodyCorrect second) : BodyCorrect (.seq first second) := by
  intro k er env base input r hb he hk hv hin hscratch
  have hsize : base + max (programSpace first) (programSpace second) ≤ k + 1 := hk
  have hk5 : 5 ≤ k + 1 := by omega
  obtain ⟨st, middle, sex, sout, scount, sframe⟩ := hs er env base input r hb he
    (by have := Nat.le_max_right (programSpace first) (programSpace second); omega) hv hin hscratch
  obtain ⟨ft, out, fex, fout, fcount, fframe⟩ := hf er env base input middle hb he
    (by have := Nat.le_max_left (programSpace first) (programSpace second); omega)
    (by intro i; rw [sframe.env er he hk5 i]; exact hv i)
    ((sframe.input hb hk5).trans hin) ((sframe.scratch hb hk5).trans hscratch)
  refine ⟨st + ft, out, Exec.seq sex fex, ?_, ?_, sframe.trans fframe⟩
  · simp [ClauseProgram.emit, writeValues_append, fout, sout, List.append_assoc]
  · simp [ClauseProgram.emit, fcount, scount, ← List.append_assoc]

/-- Apply a body correctness theorem after a numeric-only work phase. -/
theorem body_after_work {n k : Nat} (program : ClauseProgram n) (hp : BodyCorrect program)
    (er : Fin n → Fin (k + 1)) (env : Env n) (base next : Nat) (input : SAT.Word)
    (r middle : Registers k) (hb : 5 ≤ base) (hn : base ≤ next)
    (he : ∀ i, 5 ≤ (er i).val ∧ (er i).val < base)
    (hk : next + programSpace program ≤ k + 1)
    (hv : ∀ i, r (er i) = List.replicate (env i) true)
    (hin : r (register k 1) = input) (hs : r (register k 3) = [])
    (hf : WorkFrame base r middle) :
    ∃ time out, Exec (compileBody er next program) middle time (true, out) ∧
      out (register k 0) = SAT.writeValues SAT.encodeClause (program.emit input env) ++ r (register k 0) ∧
      out (register k 2) = List.replicate (program.emit input env).length true ++ r (register k 2) ∧
      BodyFrame base r out := by
  have hk5 : 5 ≤ k + 1 := by omega
  have hfb := work_toBody hf
  obtain ⟨time, out, hex, ho, hc, hframe⟩ := hp er env next input middle (by omega)
    (by intro i; exact ⟨(he i).1, by have := (he i).2; omega⟩) hk
    (by intro i; rw [hfb.env er he hk5 i]; exact hv i)
    ((hfb.input hb hk5).trans hin) ((hfb.scratch hb hk5).trans hs)
  refine ⟨time, out, hex, ?_, ?_, hfb.trans (hframe.weaken hn)⟩
  · rw [ho, work_output hf hb hk5]
  · rw [hc, work_count hf hb hk5]

theorem eval_work_pair {n k : Nat} (left right : NumExpr n)
    (er : Fin n → Fin (k + 1)) (env : Env n) (base : Nat) (r : Registers k)
    (hb : 5 ≤ base) (he : ∀ i, 5 ≤ (er i).val ∧ (er i).val < base)
    (hk : base + 2 + max (numSpace left) (numSpace right) ≤ k + 1)
    (hv : ∀ i, r (er i) = List.replicate (env i) true) (hs : r (register k 3) = []) :
    ∃ time out,
      Exec (.seq (compileNum er (register k base) (base + 2) left)
        (compileNum er (register k (base + 1)) (base + 2) right)) r time (true, out) ∧
      out (register k base) = List.replicate (left.eval env) true ∧
      out (register k (base + 1)) = List.replicate (right.eval env) true ∧ WorkFrame base r out := by
  have hk5 : 5 ≤ k + 1 := by omega
  have hbase : base < k + 1 := by omega
  have hbase' : base + 1 < k + 1 := by omega
  obtain ⟨lt, middle, lex, lval, _, lf⟩ := eval_work_num left er env base base (base + 2) r
    hb (by omega) (by omega) he
    (by have := Nat.le_max_left (numSpace left) (numSpace right); omega) hv hs
  have lfb := work_toBody lf
  obtain ⟨rt, out, rex, rval, rnum, rf⟩ := eval_work_num right er env base (base + 1) (base + 2) middle
    hb (by omega) (by omega) he
    (by have := Nat.le_max_right (numSpace left) (numSpace right); omega)
    (by intro i; rw [lfb.env er he hk5 i]; exact hv i)
    ((lfb.scratch hb hk5).trans hs)
  refine ⟨lt + rt, out, Exec.seq lex rex, ?_, rval, lf.trans rf⟩
  rw [rnum (register k base) (by rw [register_val hbase]; omega)
    (register_ne hbase hbase' (by omega)) (register_ne hbase (by omega) (by omega))]
  exact lval

theorem compile_ifLe_correct {n : Nat} (left right : NumExpr n) (yes no : ClauseProgram n)
    (hy : BodyCorrect yes) (hn : BodyCorrect no) : BodyCorrect (.ifLe left right yes no) := by
  intro k er env base input r hb he hk hv hin hs
  have hsize : base + (2 + max (max (numSpace left) (numSpace right))
      (max (programSpace yes) (programSpace no))) ≤ k + 1 := hk
  have hspaceNum := Nat.le_max_left (max (numSpace left) (numSpace right))
    (max (programSpace yes) (programSpace no))
  have hspaceBody := Nat.le_max_right (max (numSpace left) (numSpace right))
    (max (programSpace yes) (programSpace no))
  have hyes : base + 2 + programSpace yes ≤ k + 1 := by
    have := Nat.le_max_left (programSpace yes) (programSpace no); omega
  have hno : base + 2 + programSpace no ≤ k + 1 := by
    have := Nat.le_max_right (programSpace yes) (programSpace no); omega
  have hbase : base < k + 1 := by omega
  have hbase' : base + 1 < k + 1 := by omega
  have hrightleft : register k (base + 1) ≠ register k base := register_ne hbase' hbase (by omega)
  obtain ⟨nt, nums, nex, lval, rval, nf⟩ := eval_work_pair left right er env base r hb he
    (by omega) hv hs
  let compared := StackMachine.set (StackMachine.set nums (register k (base + 1)) [])
    (register k base) ((nums (register k base)).drop (right.eval env))
  have compareExec : Exec (subtractCounter (register k (base + 1)) (register k base)) nums
      (3 * right.eval env + 2) (true, compared) :=
    exec_subtractCounter _ _ hrightleft _ nums rval
  have compareFrame : WorkFrame base nums compared :=
    (Frame.set nums [] (Or.inr (Or.inr (by rw [register_val hbase']; omega)))).trans
      (Frame.set _ _ (Or.inr (Or.inr (by rw [register_val hbase]; omega))))
  have fullFrame := nf.trans compareFrame
  have comparedValue : compared (register k base) =
      List.replicate (left.eval env - right.eval env) true := by
    simp [compared, lval]
  by_cases hle : left.eval env ≤ right.eval env
  · obtain ⟨bt, out, bex, bo, bc, bf⟩ := body_after_work yes hy er env base (base + 2) input
      r compared hb (by omega) he hyes hv hin hs fullFrame
    have hnil : compared (register k base) = [] := by rw [comparedValue]; simp [Nat.sub_eq_zero_of_le hle]
    have hbranch := Exec.branchEmpty (zero := compileBody er (base + 2) no)
      (one := compileBody er (base + 2) no) hnil bex
    refine ⟨_, out, exec_seq_assoc nex (Exec.seq compareExec hbranch), ?_, ?_, bf⟩
    · simpa [ClauseProgram.emit, hle] using bo
    · simpa [ClauseProgram.emit, hle] using bc
  · obtain ⟨bt, out, bex, bo, bc, bf⟩ := body_after_work no hn er env base (base + 2) input
      r compared hb (by omega) he hno hv hin hs fullFrame
    have hpos : 0 < left.eval env - right.eval env := by omega
    have hcons : compared (register k base) = true ::
        List.replicate (left.eval env - right.eval env - 1) true := by
      rw [comparedValue]
      have hsucc : left.eval env - right.eval env = (left.eval env - right.eval env - 1) + 1 := by omega
      rw [hsucc, List.replicate_succ]
      congr 1
    have hbranch := Exec.branchOne (empty := compileBody er (base + 2) yes)
      (zero := compileBody er (base + 2) no) hcons bex
    refine ⟨_, out, exec_seq_assoc nex (Exec.seq compareExec hbranch), ?_, ?_, bf⟩
    · simpa [ClauseProgram.emit, hle] using bo
    · simpa [ClauseProgram.emit, hle] using bc

theorem compile_ifInput_correct {n : Nat} (index : NumExpr n)
    (empty zero one : ClauseProgram n) (hemp : BodyCorrect empty)
    (hz : BodyCorrect zero) (ho : BodyCorrect one) : BodyCorrect (.ifInput index empty zero one) := by
  intro k er env base input r hb he hk hv hin hs
  have hsize : base + (2 + max (numSpace index)
      (max (programSpace empty) (max (programSpace zero) (programSpace one)))) ≤ k + 1 := hk
  have hspaceNum := Nat.le_max_left (numSpace index)
    (max (programSpace empty) (max (programSpace zero) (programSpace one)))
  have hspaceBody := Nat.le_max_right (numSpace index)
    (max (programSpace empty) (max (programSpace zero) (programSpace one)))
  have hempty : base + 2 + programSpace empty ≤ k + 1 := by
    have := Nat.le_max_left (programSpace empty) (max (programSpace zero) (programSpace one)); omega
  have hzero : base + 2 + programSpace zero ≤ k + 1 := by
    have := Nat.le_max_right (programSpace empty) (max (programSpace zero) (programSpace one))
    have := Nat.le_max_left (programSpace zero) (programSpace one); omega
  have hone : base + 2 + programSpace one ≤ k + 1 := by
    have := Nat.le_max_right (programSpace empty) (max (programSpace zero) (programSpace one))
    have := Nat.le_max_right (programSpace zero) (programSpace one); omega
  have hk5 : 5 ≤ k + 1 := by omega
  have hbase : base < k + 1 := by omega
  have hbase' : base + 1 < k + 1 := by omega
  have hnextbase : register k (base + 1) ≠ register k base := register_ne hbase' hbase (by omega)
  obtain ⟨nt, nums, nex, nval, _, nf⟩ := eval_work_num index er env base base (base + 2) r
    hb (by omega) (by omega) he (by omega) hv hs
  let copied := StackMachine.set nums (register k (base + 1)) (nums (register k 1))
  have copyExec : Exec (.copy (register k 1) (register k (base + 1)) (register k 3)) nums
      _ (true, copied) := Exec.copy
    (register_ne (by omega) hbase' (by omega))
    (register_ne (by omega) (by omega) (by omega))
    (register_ne hbase' (by omega) (by omega))
    (((work_toBody nf).scratch hb hk5).trans hs)
  have copyFrame : WorkFrame base nums copied :=
    Frame.set nums _ (Or.inr (Or.inr (by rw [register_val hbase']; omega)))
  have copyCount : copied (register k base) = List.replicate (index.eval env) true := by
    simp [copied, Ne.symm hnextbase, nval]
  let inspected := StackMachine.set (StackMachine.set copied (register k base) [])
    (register k (base + 1)) ((copied (register k (base + 1))).drop (index.eval env))
  have inspectExec : Exec (subtractCounter (register k base) (register k (base + 1))) copied
      (3 * index.eval env + 2) (true, inspected) :=
    exec_subtractCounter _ _ (Ne.symm hnextbase) _ copied copyCount
  have inspectFrame : WorkFrame base copied inspected :=
    (Frame.set copied [] (Or.inr (Or.inr (by rw [register_val hbase]; omega)))).trans
      (Frame.set _ _ (Or.inr (Or.inr (by rw [register_val hbase']; omega))))
  have fullFrame := nf.trans (copyFrame.trans inspectFrame)
  have inspectedValue : inspected (register k (base + 1)) = input.drop (index.eval env) := by
    simp [inspected, copied, (work_toBody nf).input hb hk5, hin]
  cases hdrop : input.drop (index.eval env) with
  | nil =>
      have hget : input[index.eval env]? = none := by
        rw [← List.head?_drop, hdrop]; rfl
      obtain ⟨bt, out, bex, bo, bc, bf⟩ := body_after_work empty hemp er env base (base + 2) input
        r inspected hb (by omega) he hempty hv hin hs fullFrame
      have hbranch := Exec.branchEmpty (zero := compileBody er (base + 2) zero)
        (one := compileBody er (base + 2) one) (inspectedValue.trans hdrop) bex
      refine ⟨_, out, Exec.seq nex (Exec.seq copyExec (Exec.seq inspectExec hbranch)), ?_, ?_, bf⟩
      · simpa [ClauseProgram.emit, hget] using bo
      · simpa [ClauseProgram.emit, hget] using bc
  | cons bit tail =>
      cases bit with
      | false =>
          have hget : input[index.eval env]? = some false := by
            rw [← List.head?_drop, hdrop]; rfl
          obtain ⟨bt, out, bex, bo, bc, bf⟩ := body_after_work zero hz er env base (base + 2) input
            r inspected hb (by omega) he hzero hv hin hs fullFrame
          have hbranch := Exec.branchZero (empty := compileBody er (base + 2) empty)
            (one := compileBody er (base + 2) one) (inspectedValue.trans hdrop) bex
          refine ⟨_, out, Exec.seq nex (Exec.seq copyExec (Exec.seq inspectExec hbranch)), ?_, ?_, bf⟩
          · simpa [ClauseProgram.emit, hget] using bo
          · simpa [ClauseProgram.emit, hget] using bc
      | true =>
          have hget : input[index.eval env]? = some true := by
            rw [← List.head?_drop, hdrop]; rfl
          obtain ⟨bt, out, bex, bo, bc, bf⟩ := body_after_work one ho er env base (base + 2) input
            r inspected hb (by omega) he hone hv hin hs fullFrame
          have hbranch := Exec.branchOne (empty := compileBody er (base + 2) empty)
            (zero := compileBody er (base + 2) zero) (inspectedValue.trans hdrop) bex
          refine ⟨_, out, Exec.seq nex (Exec.seq copyExec (Exec.seq inspectExec hbranch)), ?_, ?_, bf⟩
          · simpa [ClauseProgram.emit, hget] using bo
          · simpa [ClauseProgram.emit, hget] using bc

end Complexity.StackTableauEmitterCompile
