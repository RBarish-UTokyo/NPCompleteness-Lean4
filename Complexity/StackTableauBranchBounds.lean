module

public import Complexity.StackTableauBranchCorrect
public import Complexity.StackTableauBodyBoundedSpec
import Lean.Elab.Tactic.Omega

@[expose] public section

namespace Complexity.StackTableauEmitterCompile

open StackTableauEmitter
open StackTableauProgram (Command Exec)
open StackMachine (Registers)

theorem eval_work_num_bounded {n k : Nat} (expression : NumExpr n)
    (envRegisters : Fin n → Fin (k + 1)) (env : Env n)
    (base dest next : Nat) (r : Registers k)
    (hb : 5 ≤ base) (hd : base ≤ dest) (hn : dest < next)
    (he : ∀ i, 5 ≤ (envRegisters i).val ∧ (envRegisters i).val < base)
    (hk : next + numSpace expression ≤ k + 1)
    (hv : ∀ i, r (envRegisters i) = List.replicate (env i) true)
    (hs : r (register k 3) = []) (capacity : Nat)
    (hfits : NumFits expression env capacity) (hwork : WorkBound r capacity) :
    ∃ time out, Exec (compileNum envRegisters (register k dest) next expression) r time (true, out) ∧
      out (register k dest) = List.replicate (expression.eval env) true ∧
      Frame next (register k dest) r out ∧ WorkFrame base r out ∧
      time ≤ numCost expression capacity ∧ WorkBound out capacity := by
  have hdest : dest < k + 1 := by omega
  obtain ⟨time, out, hex, hval, hframe, htime, hout⟩ :=
    compileNum_bounded expression envRegisters env (register k dest) next r
      (by rw [register_val hdest]; omega) (by rw [register_val hdest]; omega)
      (by intro i; refine ⟨(he i).1, by have := (he i).2; omega, ?_⟩
          apply Ne.symm (register_ne_fin hdest _)
          have := (he i).2
          omega) hk hv hs capacity hfits hwork
  exact ⟨time, out, hex, hval, hframe,
    hframe.weaken (by omega) (Or.inr (by rw [register_val hdest]; omega)), htime, hout⟩

theorem eval_work_pair_bounded {n k : Nat} (left right : NumExpr n)
    (er : Fin n → Fin (k + 1)) (env : Env n) (base : Nat) (r : Registers k)
    (hb : 5 ≤ base) (he : ∀ i, 5 ≤ (er i).val ∧ (er i).val < base)
    (hk : base + 2 + max (numSpace left) (numSpace right) ≤ k + 1)
    (hv : ∀ i, r (er i) = List.replicate (env i) true) (hs : r (register k 3) = [])
    (capacity : Nat) (hfits : NumFits left env capacity ∧ NumFits right env capacity)
    (hwork : WorkBound r capacity) :
    ∃ time out,
      Exec (.seq (compileNum er (register k base) (base + 2) left)
        (compileNum er (register k (base + 1)) (base + 2) right)) r time (true, out) ∧
      out (register k base) = List.replicate (left.eval env) true ∧
      out (register k (base + 1)) = List.replicate (right.eval env) true ∧ WorkFrame base r out ∧
      time ≤ numCost left capacity + numCost right capacity ∧ WorkBound out capacity := by
  have hk5 : 5 ≤ k + 1 := by omega
  have hbase : base < k + 1 := by omega
  have hbase' : base + 1 < k + 1 := by omega
  obtain ⟨lt, middle, lex, lval, _, lf, ltime, lwork⟩ := eval_work_num_bounded left er env base base (base + 2) r
    hb (by omega) (by omega) he
    (by have := Nat.le_max_left (numSpace left) (numSpace right); omega) hv hs capacity hfits.1 hwork
  have lfb := work_toBody lf
  obtain ⟨rt, out, rex, rval, rnum, rf, rtime, rwork⟩ := eval_work_num_bounded right er env base (base + 1) (base + 2) middle
    hb (by omega) (by omega) he
    (by have := Nat.le_max_right (numSpace left) (numSpace right); omega)
    (by intro i; rw [lfb.env er he hk5 i]; exact hv i)
    ((lfb.scratch hb hk5).trans hs) capacity hfits.2 lwork
  refine ⟨lt + rt, out, Exec.seq lex rex, ?_, rval, lf.trans rf, Nat.add_le_add ltime rtime, rwork⟩
  rw [rnum (register k base) (by rw [register_val hbase]; omega)
    (register_ne hbase hbase' (by omega)) (register_ne hbase (by omega) (by omega))]
  exact lval

theorem body_after_work_bounded {n k : Nat} (program : ClauseProgram n) (hp : BodyBounded program)
    (er : Fin n → Fin (k + 1)) (env : Env n) (base next : Nat) (input : SAT.Word)
    (r middle : Registers k) (hb : 5 ≤ base) (hn : base ≤ next)
    (he : ∀ i, 5 ≤ (er i).val ∧ (er i).val < base)
    (hk : next + programSpace program ≤ k + 1)
    (hv : ∀ i, r (er i) = List.replicate (env i) true)
    (hin : r (register k 1) = input) (hs : r (register k 3) = [])
    (hf : WorkFrame base r middle) (capacity : Nat)
    (hfits : program.Fits input env capacity) (hwork : WorkBound middle capacity) :
    ∃ time out, Exec (compileBody er next program) middle time (true, out) ∧
      BodyFrame base r out ∧ time ≤ bodyCost program capacity ∧ WorkBound out capacity := by
  have hk5 : 5 ≤ k + 1 := by omega
  have hfb := work_toBody hf
  obtain ⟨time, out, hex, hframe, htime, hout⟩ := hp er env next input middle (by omega)
    (by intro i; exact ⟨(he i).1, by have := (he i).2; omega⟩) hk
    (by intro i; rw [hfb.env er he hk5 i]; exact hv i)
    ((hfb.input hb hk5).trans hin) ((hfb.scratch hb hk5).trans hs) capacity hfits hwork
  exact ⟨time, out, hex, hfb.trans (hframe.weaken hn), htime, hout⟩

theorem compile_ifLe_bounded {n : Nat} (left right : NumExpr n) (yes no : ClauseProgram n)
    (hy : BodyBounded yes) (hn : BodyBounded no) : BodyBounded (.ifLe left right yes no) := by
  intro k er env base input r hb he hk hv hin hs capacity hfits hwork
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
  obtain ⟨nt, nums, nex, lval, rval, nf, ntime, nwork⟩ := eval_work_pair_bounded left right er env base r hb he
    (by omega) hv hs capacity ⟨hfits.1, hfits.2.1⟩ hwork
  let compared := StackMachine.set (StackMachine.set nums (register k (base + 1)) [])
    (register k base) ((nums (register k base)).drop (right.eval env))
  have compareExec : Exec (subtractCounter (register k (base + 1)) (register k base)) nums
      (3 * right.eval env + 2) (true, compared) :=
    exec_subtractCounter _ _ hrightleft _ nums rval
  have compareFrame : WorkFrame base nums compared :=
    (Frame.set nums [] (Or.inr (Or.inr (by rw [register_val hbase']; omega)))).trans
      (Frame.set _ _ (Or.inr (Or.inr (by rw [register_val hbase]; omega))))
  have comparedWork : WorkBound compared capacity :=
    (nwork.set _ [] (by simp)).set _ _ (Nat.le_trans (by rw [List.length_drop]; exact Nat.sub_le _ _)
      (nwork.register hbase (by omega) (by omega)))
  have fullFrame := nf.trans compareFrame
  have comparedValue : compared (register k base) =
      List.replicate (left.eval env - right.eval env) true := by
    simp [compared, lval]
  by_cases hle : left.eval env ≤ right.eval env
  · obtain ⟨bt, out, bex, bf, btime, bwork⟩ := body_after_work_bounded yes hy er env base (base + 2) input
      r compared hb (by omega) he hyes hv hin hs fullFrame capacity hfits.2.2.1 comparedWork
    have hnil : compared (register k base) = [] := by rw [comparedValue]; simp [Nat.sub_eq_zero_of_le hle]
    have hbranch := Exec.branchEmpty (zero := compileBody er (base + 2) no)
      (one := compileBody er (base + 2) no) hnil bex
    refine ⟨_, out, exec_seq_assoc nex (Exec.seq compareExec hbranch), bf, ?_, bwork⟩
    have hright := hfits.2.1.value
    simp only [bodyCost]
    omega
  · obtain ⟨bt, out, bex, bf, btime, bwork⟩ := body_after_work_bounded no hn er env base (base + 2) input
      r compared hb (by omega) he hno hv hin hs fullFrame capacity hfits.2.2.2 comparedWork
    have hpos : 0 < left.eval env - right.eval env := by omega
    have hcons : compared (register k base) = true ::
        List.replicate (left.eval env - right.eval env - 1) true := by
      rw [comparedValue]
      have hsucc : left.eval env - right.eval env = (left.eval env - right.eval env - 1) + 1 := by omega
      rw [hsucc, List.replicate_succ]
      congr 1
    have hbranch := Exec.branchOne (empty := compileBody er (base + 2) yes)
      (zero := compileBody er (base + 2) no) hcons bex
    refine ⟨_, out, exec_seq_assoc nex (Exec.seq compareExec hbranch), bf, ?_, bwork⟩
    have hright := hfits.2.1.value
    simp only [bodyCost]
    omega

theorem compile_ifInput_bounded {n : Nat} (index : NumExpr n)
    (empty zero one : ClauseProgram n) (hemp : BodyBounded empty)
    (hz : BodyBounded zero) (ho : BodyBounded one) : BodyBounded (.ifInput index empty zero one) := by
  intro k er env base input r hb he hk hv hin hs capacity hfits hwork
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
  obtain ⟨nt, nums, nex, nval, _, nf, ntime, nwork⟩ := eval_work_num_bounded index er env base base (base + 2) r
    hb (by omega) (by omega) he (by omega) hv hs capacity hfits.1 hwork
  let copied := StackMachine.set nums (register k (base + 1)) (nums (register k 1))
  have copyExec : Exec (.copy (register k 1) (register k (base + 1)) (register k 3)) nums
      _ (true, copied) := Exec.copy
    (register_ne (by omega) hbase' (by omega))
    (register_ne (by omega) (by omega) (by omega))
    (register_ne hbase' (by omega) (by omega))
    (((work_toBody nf).scratch hb hk5).trans hs)
  have copiedWork : WorkBound copied capacity :=
    nwork.set _ _ (nwork.register (by omega : 1 < k + 1) (by decide) (by decide))
  have copyTime : (nums (register k (base + 1))).length + 5 * (nums (register k 1)).length + 6 ≤
      6 * capacity + 6 := by
    have hdst := nwork.register hbase' (by omega) (by omega)
    have hsrc := nwork.register (by omega : 1 < k + 1) (by decide) (by decide)
    omega
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
  have inspectedWork : WorkBound inspected capacity :=
    (copiedWork.set _ [] (by simp)).set _ _ (Nat.le_trans (by rw [List.length_drop]; exact Nat.sub_le _ _)
      (copiedWork.register hbase' (by omega) (by omega)))
  have fullFrame := nf.trans (copyFrame.trans inspectFrame)
  have inspectedValue : inspected (register k (base + 1)) = input.drop (index.eval env) := by
    simp [inspected, copied, (work_toBody nf).input hb hk5, hin]
  cases hdrop : input.drop (index.eval env) with
  | nil =>
      have hget : input[index.eval env]? = none := by
        rw [← List.head?_drop, hdrop]; rfl
      obtain ⟨bt, out, bex, bf, btime, bwork⟩ := body_after_work_bounded empty hemp er env base (base + 2) input
        r inspected hb (by omega) he hempty hv hin hs fullFrame capacity hfits.2.1 inspectedWork
      have hbranch := Exec.branchEmpty (zero := compileBody er (base + 2) zero)
        (one := compileBody er (base + 2) one) (inspectedValue.trans hdrop) bex
      refine ⟨_, out, Exec.seq nex (Exec.seq copyExec (Exec.seq inspectExec hbranch)), bf, ?_, bwork⟩
      have hindex := hfits.1.value
      simp only [bodyCost]
      omega
  | cons bit tail =>
      cases bit with
      | false =>
          have hget : input[index.eval env]? = some false := by
            rw [← List.head?_drop, hdrop]; rfl
          obtain ⟨bt, out, bex, bf, btime, bwork⟩ := body_after_work_bounded zero hz er env base (base + 2) input
            r inspected hb (by omega) he hzero hv hin hs fullFrame capacity hfits.2.2.1 inspectedWork
          have hbranch := Exec.branchZero (empty := compileBody er (base + 2) empty)
            (one := compileBody er (base + 2) one) (inspectedValue.trans hdrop) bex
          refine ⟨_, out, Exec.seq nex (Exec.seq copyExec (Exec.seq inspectExec hbranch)), bf, ?_, bwork⟩
          have hindex := hfits.1.value
          simp only [bodyCost]
          omega
      | true =>
          have hget : input[index.eval env]? = some true := by
            rw [← List.head?_drop, hdrop]; rfl
          obtain ⟨bt, out, bex, bf, btime, bwork⟩ := body_after_work_bounded one ho er env base (base + 2) input
            r inspected hb (by omega) he hone hv hin hs fullFrame capacity hfits.2.2.2 inspectedWork
          have hbranch := Exec.branchOne (empty := compileBody er (base + 2) empty)
            (zero := compileBody er (base + 2) zero) (inspectedValue.trans hdrop) bex
          refine ⟨_, out, Exec.seq nex (Exec.seq copyExec (Exec.seq inspectExec hbranch)), bf, ?_, bwork⟩
          have hindex := hfits.1.value
          simp only [bodyCost]
          omega

end Complexity.StackTableauEmitterCompile
