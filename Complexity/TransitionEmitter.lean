module

public import Complexity.MachineEmitter
public import Complexity.EmitterTableauTools

/-!
First-order programs emitting every local transition constraint of a bounded
computation tableau. Descending loops only change clause order.
-/

@[expose] public section

namespace Complexity.TransitionEmitter

open StackTableauEmitter

def rowProgram {n : Nat} (M : Machine) (width time : NumExpr n) : ClauseProgram n :=
  .seq (MachineEmitter.transitionProgram M width time .state)
    (.seq
      (.forDown width
        (MachineEmitter.transitionProgram M width.lift time.lift (.left (.var 0))))
      (.forDown width
        (MachineEmitter.transitionProgram M width.lift time.lift (.right (.var 0)))))

def program {n : Nat} (M : Machine) (width steps : NumExpr n) : ClauseProgram n :=
  .forDown steps (rowProgram M width.lift (.var 0))

theorem emit_rowProgram {n W T : Nat} (M : Machine) (width time : NumExpr n)
    (input : SAT.Word) (env : Env n) (hw : 0 < W) (hwidth : width.eval env = W)
    (t : Fin T) (htime : time.eval env = t.val) :
    Equivalent ((rowProgram M width time).emit input env)
      ((Tableau.transitionRow (FiniteRows.transitionTree M W hw) T t).map
        CSPSAT.forbiddenClause) := by
  let f : FiniteRows.Slot W → SAT.CNF := fun slot =>
    (((FiniteRows.transitionTree M W hw slot).mapVars (Tableau.cell t.castSucc)).encode
      (Tableau.cell t.succ slot)).map CSPSAT.forbiddenClause
  have hcell {m : Nat} (width time : NumExpr m) (env : Env m)
      (hwidth : width.eval env = W) (htime : time.eval env = t.val)
      (cell : MachineEmitter.Cell m) (actual : FiniteRows.Cell W)
      (h : cell.Realizes env actual) :
      (MachineEmitter.transitionProgram M width time cell).emit input env =
        f actual.slot := by
    simpa only [f, FiniteRows.transitionTree, FiniteRows.coordinate_slot] using
      MachineEmitter.emit_transitionProgram M width time input env hw hwidth t htime
        cell actual h
  have hstate : Equivalent
      ((MachineEmitter.transitionProgram M width time .state).emit input env)
      (f (FiniteRows.stateSlot W)) := by
    rw [hcell width time env hwidth htime .state .state trivial]
    exact Equivalent.refl _
  have hleft : Equivalent
      ((ClauseProgram.forDown width
        (MachineEmitter.transitionProgram M width.lift time.lift (.left (.var 0)))).emit
          input env)
      ((List.finRange W).flatMap (fun i => f (FiniteRows.leftSlot W i))) := by
    rw [ClauseProgram.emit_forDown, hwidth]
    apply equivalent_flatMap_finRange
    intro i
    rw [hcell width.lift time.lift (extend i.val env)
      ((NumExpr.eval_lift width i.val env).trans hwidth)
      ((NumExpr.eval_lift time i.val env).trans htime) (.left (.var 0)) (.left i) rfl]
    exact Equivalent.refl _
  have hright : Equivalent
      ((ClauseProgram.forDown width
        (MachineEmitter.transitionProgram M width.lift time.lift (.right (.var 0)))).emit
          input env)
      ((List.finRange W).flatMap (fun i => f (FiniteRows.rightSlot W i))) := by
    rw [ClauseProgram.emit_forDown, hwidth]
    apply equivalent_flatMap_finRange
    intro i
    rw [hcell width.lift time.lift (extend i.val env)
      ((NumExpr.eval_lift width i.val env).trans hwidth)
      ((NumExpr.eval_lift time i.val env).trans htime) (.right (.var 0)) (.right i) rfl]
    exact Equivalent.refl _
  have hrows := hstate.append (hleft.append hright)
  have hpartition := equivalent_cell_partition W f
  simp only [rowProgram, ClauseProgram.emit_seq]
  apply hrows.trans
  simpa only [Tableau.transitionRow, List.map_flatMap, List.append_assoc, f] using hpartition

theorem emit_program {n W T : Nat} (M : Machine) (width steps : NumExpr n)
    (input : SAT.Word) (env : Env n) (hw : 0 < W)
    (hwidth : width.eval env = W) (hsteps : steps.eval env = T) :
    Equivalent ((program M width steps).emit input env)
      ((Tableau.transitions (FiniteRows.transitionTree M W hw) T).map
        CSPSAT.forbiddenClause) := by
  simp only [program, ClauseProgram.emit_forDown, hsteps, Tableau.transitions,
    List.map_flatMap]
  apply equivalent_flatMap_finRange
  intro t
  exact emit_rowProgram M width.lift (.var 0) input (extend t.val env) hw
    ((NumExpr.eval_lift width t.val env).trans hwidth) t rfl

end Complexity.TransitionEmitter
