module

public import Complexity.EmitterTools

/-!
# A first-order emitter for one-hot cell variables

Each cell has the fixed finite value domain `Fin (d + 1)`.  The descending
outer loop changes only the order of emitted cell constraints; within a cell
the emitter produces exactly the established `Constraints.exactlyOne` formula.
-/

@[expose] public section

namespace Complexity.OneHotEmitter

open StackTableauEmitter

/-- In the loop body variable zero denotes the current cell number. -/
def rowExpressions {n : Nat} (d : Nat) : List (NumExpr (n + 1)) :=
  (List.finRange (d + 1)).map (fun value =>
    .add (.mul (.var 0) (.const (d + 1))) (.const value.val))

/-- Explicit nested arithmetic and clause syntax; the finite domain is fixed. -/
def program {n : Nat} (d : Nat) (cells : NumExpr n) : ClauseProgram n :=
  .forDown cells (exactlyOne (rowExpressions d))

theorem eval_rowExpressions {n m : Nat} (d : Nat) (cell : Fin m) (env : Env n) :
    (rowExpressions (n := n) d).map (fun expr => expr.eval (extend cell.val env)) =
      CSPSAT.rowVariables d cell := by
  simp [rowExpressions, CSPSAT.rowVariables, CSPSAT.atomIndex, List.map_map, NumExpr.eval]

/-- Every loop body emits exactly the intended one-hot constraints for its cell. -/
theorem emit_row {n m : Nat} (d : Nat) (cell : Fin m) (input : SAT.Word) (env : Env n) :
    (exactlyOne (rowExpressions d)).emit input (extend cell.val env) =
      Constraints.exactlyOne (CSPSAT.rowVariables d cell) := by
  rw [emit_exactlyOne, eval_rowExpressions]

/-- Descending cell order is semantically equivalent to the canonical ascending order. -/
theorem program_correct {n : Nat} (d : Nat) (cells : NumExpr n) (input : SAT.Word) (env : Env n) :
    Equivalent ((program d cells).emit input env) (CSPSAT.oneHotCNF (cells.eval env) d) := by
  simp only [program, ClauseProgram.emit_forDown, CSPSAT.oneHotCNF]
  apply equivalent_flatMap_finRange
  intro cell
  rw [emit_row]
  exact Equivalent.refl _

theorem program_satisfiable_iff {n : Nat} (d : Nat) (cells : NumExpr n)
    (input : SAT.Word) (env : Env n) :
    SAT.Satisfiable ((program d cells).emit input env) ↔
      SAT.Satisfiable (CSPSAT.oneHotCNF (cells.eval env) d) :=
  (program_correct d cells input env).satisfiable_iff

end Complexity.OneHotEmitter
