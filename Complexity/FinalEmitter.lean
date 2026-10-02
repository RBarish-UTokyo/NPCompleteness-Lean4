module

public import Complexity.MachineEmitter
public import Complexity.EmitterTableauTools
public import Complexity.CookLevin

/-!
First-order emission of the final accepting-control constraint.
-/

@[expose] public section

namespace Complexity.FinalEmitter

open StackTableauEmitter

def program {n : Nat} (M : Machine) (width steps : NumExpr n) : ClauseProgram n :=
  (ConstraintEmitter.Tree.value (FiniteRows.decisionValue M true)).program
    (MachineEmitter.rowIndex width steps (.const 0))

theorem program_correct {n : Nat} (M : Machine) (width steps : NumExpr n)
    (input : Word) (env : Env n) :
    (program M width steps).emit input env =
      (Tableau.mapInstance (Tableau.cell (Fin.last (steps.eval env)))
        (CookLevin.accepting M (width.eval env))).map CSPSAT.forbiddenClause := by
  rw [program, ConstraintEmitter.Tree.emit_program, CookLevin.accepting, mapInstance_pin]
  simp only [ConstraintEmitter.Tree.eval, MachineEmitter.eval_rowIndex, NumExpr.eval]
  exact RawConstraint.encode_ofTree_val
    (LocalConstraint.Tree.value (FiniteRows.decisionValue M true))
    (Tableau.cell (Fin.last (steps.eval env)) (FiniteRows.stateSlot (width.eval env)))

end Complexity.FinalEmitter
