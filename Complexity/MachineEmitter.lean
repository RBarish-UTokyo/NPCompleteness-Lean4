module

public import Complexity.ConstraintEmitter
public import Complexity.FiniteRows

/-!
Uniform, first-order arithmetic templates for the concrete machine's local
transition trees. The finite machine transition table is fixed at compile time;
only width, time and cell indices vary with the input.
-/

@[expose] public section

namespace Complexity.MachineEmitter

open StackTableauEmitter

abbrev Expr := NumExpr
abbrev CTree := ConstraintEmitter.Tree

instance {n : Nat} : Add (Expr n) := ⟨NumExpr.add⟩
instance {n : Nat} : Mul (Expr n) := ⟨NumExpr.mul⟩
instance {n : Nat} : Sub (Expr n) := ⟨NumExpr.sub⟩
instance {n k : Nat} : OfNat (Expr n) k := ⟨NumExpr.const k⟩

def rowIndex {n : Nat} (width time slot : Expr n) : Expr n :=
  time * (2 * width + 1) + slot

def leftIndex {n : Nat} (width time i : Expr n) : Expr n :=
  rowIndex width time (i + 1)

def rightIndex {n : Nat} (width time i : Expr n) : Expr n :=
  rowIndex width time (width + i + 1)

def constant {n : Nat} (M : Machine) (a : Symbol) : CTree n (M.states + 3) :=
  .value (FiniteRows.symbolValue M a)

def leftTree {n : Nat} (M : Machine) (width time i : Expr n) : CTree n (M.states + 3) :=
  .ifLe (i + 1) width (.query (leftIndex width time i) ConstraintEmitter.Tree.value) (constant M .blank)

def rightTree {n : Nat} (M : Machine) (width time i : Expr n) : CTree n (M.states + 3) :=
  .ifLe (i + 1) width (.query (rightIndex width time i) ConstraintEmitter.Tree.value) (constant M .blank)

def leftAfter {n : Nat} (M : Machine) (width time i : Expr n) (a : Symbol) :
    Move → CTree n (M.states + 3)
  | .left => leftTree M width time (i + 1)
  | .stay => leftTree M width time i
  | .right => .ifLe i 0 (constant M a) (leftTree M width time (.pred i))

def rightAfter {n : Nat} (M : Machine) (width time i : Expr n) (a : Symbol) :
    Move → CTree n (M.states + 3)
  | .left => .ifLe i 0 (leftTree M width time 0)
      (.ifLe i 1 (constant M a) (rightTree M width time (.pred i)))
  | .stay => .ifLe i 0 (constant M a) (rightTree M width time i)
  | .right => rightTree M width time (i + 1)

inductive Cell (n : Nat) where
  | state
  | left (index : Expr n)
  | right (index : Expr n)

def haltTree {n : Nat} (M : Machine) (width time : Expr n) (b : Bool) :
    Cell n → CTree n (M.states + 3)
  | .state => .value (FiniteRows.decisionValue M b)
  | .left i => leftTree M width time i
  | .right i => rightTree M width time i

def instructionTree {n : Nat} (M : Machine) (width time : Expr n) :
    Instruction (M.states + 1) → Cell n → CTree n (M.states + 3)
  | .halt b, c => haltTree M width time b c
  | .step _ _ q, .state => .value (FiniteRows.stateValue M q)
  | .step a d _, .left i => leftAfter M width time i a d
  | .step a d _, .right i => rightAfter M width time i a d

def transitionTree {n : Nat} (M : Machine) (width time : Expr n) (c : Cell n) :
    CTree n (M.states + 3) :=
  .query (rowIndex width time 0) fun v =>
    match FiniteRows.decodeControl M v with
    | .halted b => haltTree M width time b c
    | .running q => .query (rightIndex width time 0) fun scanned =>
      instructionTree M width time (M.code q (FiniteRows.decodeSymbol M scanned)) c

def Cell.Realizes {n width : Nat} (env : Env n) : Cell n → FiniteRows.Cell width → Prop
  | .state, .state => True
  | .left e, .left i => e.eval env = i.val
  | .right e, .right i => e.eval env = i.val
  | _, _ => False

def rowMap (width time : Nat) (slot : FiniteRows.Slot width) : Nat :=
  time * (2 * width + 1) + slot.val

@[simp] theorem eval_rowIndex {n : Nat} (width time slot : Expr n) (env : Env n) :
    (rowIndex width time slot).eval env =
      time.eval env * (2 * width.eval env + 1) + slot.eval env := rfl

@[simp] theorem eval_leftIndex {n : Nat} (width time i : Expr n) (env : Env n) :
    (leftIndex width time i).eval env =
      time.eval env * (2 * width.eval env + 1) + (i.eval env + 1) := rfl

@[simp] theorem eval_rightIndex {n : Nat} (width time i : Expr n) (env : Env n) :
    (rightIndex width time i).eval env =
      time.eval env * (2 * width.eval env + 1) + (width.eval env + i.eval env + 1) := rfl

theorem eval_leftTree {n : Nat} (M : Machine) (width time i : Expr n) (env : Env n) :
    (leftTree M width time i).eval env =
      RawConstraint.ofTree (rowMap (width.eval env) (time.eval env))
        (FiniteRows.sourceTree M (width.eval env) (.left (i.eval env))) := by
  by_cases hi : i.eval env < width.eval env
  · have hle : i.eval env + 1 ≤ width.eval env := by omega
    simp [leftTree, ConstraintEmitter.Tree.eval, NumExpr.eval, hle, FiniteRows.sourceTree,
      hi, RawConstraint.ofTree, rowMap, FiniteRows.leftSlot]
  · have hle : ¬ i.eval env + 1 ≤ width.eval env := by omega
    simp [leftTree, ConstraintEmitter.Tree.eval, NumExpr.eval, hle, FiniteRows.sourceTree,
      hi, RawConstraint.ofTree, constant]

theorem eval_rightTree {n : Nat} (M : Machine) (width time i : Expr n) (env : Env n) :
    (rightTree M width time i).eval env =
      RawConstraint.ofTree (rowMap (width.eval env) (time.eval env))
        (FiniteRows.sourceTree M (width.eval env) (.right (i.eval env))) := by
  by_cases hi : i.eval env < width.eval env
  · have hle : i.eval env + 1 ≤ width.eval env := by omega
    simp [rightTree, ConstraintEmitter.Tree.eval, NumExpr.eval, hle, FiniteRows.sourceTree,
      hi, RawConstraint.ofTree, rowMap, FiniteRows.rightSlot]
  · have hle : ¬ i.eval env + 1 ≤ width.eval env := by omega
    simp [rightTree, ConstraintEmitter.Tree.eval, NumExpr.eval, hle, FiniteRows.sourceTree,
      hi, RawConstraint.ofTree, constant]

theorem eval_leftAfter {n : Nat} (M : Machine) (width time i : Expr n)
    (a : Symbol) (d : Move) (env : Env n) :
    (leftAfter M width time i a d).eval env =
      RawConstraint.ofTree (rowMap (width.eval env) (time.eval env))
        (FiniteRows.sourceTree M (width.eval env) (FiniteRows.leftSource a d (i.eval env))) := by
  cases d with
  | stay => exact eval_leftTree M width time i env
  | left => simpa only [leftAfter, NumExpr.eval, FiniteRows.leftSource] using
      eval_leftTree M width time (i + 1) env
  | right =>
    cases he : i.eval env with
    | zero => simp [leftAfter, ConstraintEmitter.Tree.eval, NumExpr.eval, he,
        FiniteRows.leftSource, FiniteRows.sourceTree, constant, RawConstraint.ofTree]
    | succ j =>
      simp only [leftAfter, ConstraintEmitter.Tree.eval, NumExpr.eval, he]
      simpa [NumExpr.eval, he, FiniteRows.leftSource] using
        eval_leftTree M width time (.pred i) env

theorem eval_rightAfter {n : Nat} (M : Machine) (width time i : Expr n)
    (a : Symbol) (d : Move) (env : Env n) :
    (rightAfter M width time i a d).eval env =
      RawConstraint.ofTree (rowMap (width.eval env) (time.eval env))
        (FiniteRows.sourceTree M (width.eval env) (FiniteRows.rightSource a d (i.eval env))) := by
  cases d with
  | right => simpa only [rightAfter, NumExpr.eval, FiniteRows.rightSource] using
      eval_rightTree M width time (i + 1) env
  | stay =>
    cases he : i.eval env with
    | zero => simp [rightAfter, ConstraintEmitter.Tree.eval, NumExpr.eval, he,
        FiniteRows.rightSource, FiniteRows.sourceTree, constant, RawConstraint.ofTree]
    | succ j =>
      simp only [rightAfter, ConstraintEmitter.Tree.eval, NumExpr.eval, he]
      simpa [he, FiniteRows.rightSource] using eval_rightTree M width time i env
  | left =>
    cases he : i.eval env with
    | zero =>
      simp only [rightAfter, ConstraintEmitter.Tree.eval, NumExpr.eval, he,
        Nat.le_refl, ↓reduceIte, FiniteRows.rightSource]
      exact eval_leftTree M width time 0 env
    | succ j =>
      cases j with
      | zero => simp [rightAfter, ConstraintEmitter.Tree.eval, NumExpr.eval, he,
          FiniteRows.rightSource, FiniteRows.sourceTree, constant, RawConstraint.ofTree]
      | succ j =>
        have hn : ¬ j + 1 + 1 ≤ 1 := by omega
        simp only [rightAfter, ConstraintEmitter.Tree.eval, NumExpr.eval, he,
          hn, ↓reduceIte]
        simpa [NumExpr.eval, he, FiniteRows.rightSource] using
          eval_rightTree M width time (.pred i) env

theorem eval_haltTree {n : Nat} (M : Machine) (width time : Expr n) (env : Env n)
    (b : Bool) (cell : Cell n) (actual : FiniteRows.Cell (width.eval env))
    (h : cell.Realizes env actual) :
    (haltTree M width time b cell).eval env =
      RawConstraint.ofTree (rowMap (width.eval env) (time.eval env))
        (FiniteRows.haltTree M (width.eval env) b actual) := by
  cases cell <;> cases actual <;> simp only [Cell.Realizes] at h
  all_goals try contradiction
  · rfl
  · rename_i e i
    simpa only [haltTree, FiniteRows.haltTree, h] using eval_leftTree M width time e env
  · rename_i e i
    simpa only [haltTree, FiniteRows.haltTree, h] using eval_rightTree M width time e env

theorem eval_instructionTree {n : Nat} (M : Machine) (width time : Expr n)
    (env : Env n) (instruction : Instruction (M.states + 1))
    (cell : Cell n) (actual : FiniteRows.Cell (width.eval env))
    (h : cell.Realizes env actual) :
    (instructionTree M width time instruction cell).eval env =
      RawConstraint.ofTree (rowMap (width.eval env) (time.eval env))
        (FiniteRows.instructionTree M (width.eval env) instruction actual) := by
  cases instruction with
  | halt b => exact eval_haltTree M width time env b cell actual h
  | step a d q =>
    cases cell <;> cases actual <;> simp only [Cell.Realizes] at h
    all_goals try contradiction
    · rfl
    · rename_i e i
      simpa only [instructionTree, FiniteRows.instructionTree, h] using
        eval_leftAfter M width time e a d env
    · rename_i e i
      simpa only [instructionTree, FiniteRows.instructionTree, h] using
        eval_rightAfter M width time e a d env

theorem eval_transitionTree {n : Nat} (M : Machine) (width time : Expr n)
    (env : Env n) (hw : 0 < width.eval env)
    (cell : Cell n) (actual : FiniteRows.Cell (width.eval env))
    (h : cell.Realizes env actual) :
    (transitionTree M width time cell).eval env =
      RawConstraint.ofTree (rowMap (width.eval env) (time.eval env))
        (FiniteRows.transitionTreeCell M (width.eval env) hw actual) := by
  simp only [transitionTree, ConstraintEmitter.Tree.eval, FiniteRows.transitionTreeCell,
    RawConstraint.ofTree]
  congr 1
  funext v
  cases FiniteRows.decodeControl M v with
  | halted b => exact eval_haltTree M width time env b cell actual h
  | running q =>
    simp only [ConstraintEmitter.Tree.eval, RawConstraint.ofTree]
    congr 1
    funext scanned
    exact eval_instructionTree M width time env _ cell actual h

def Cell.index {n : Nat} (width : Expr n) : Cell n → Expr n
  | .state => 0
  | .left i => i + 1
  | .right i => width + i + 1

theorem Cell.eval_index {n W : Nat} (width : Expr n) (env : Env n)
    (hwidth : width.eval env = W) (cell : Cell n) (actual : FiniteRows.Cell W)
    (h : cell.Realizes env actual) :
    (cell.index width).eval env = actual.slot.val := by
  cases cell <;> cases actual <;> simp only [Cell.Realizes] at h
  all_goals try contradiction
  · rfl
  · simp [Cell.index, NumExpr.eval, FiniteRows.Cell.slot, FiniteRows.leftSlot, h]
  · simp [Cell.index, NumExpr.eval, FiniteRows.Cell.slot, FiniteRows.rightSlot, h, hwidth]

def transitionProgram {n : Nat} (M : Machine) (width time : Expr n) (cell : Cell n) :
    ClauseProgram n :=
  (transitionTree M width time cell).program
    (rowIndex width (time + 1) (cell.index width))

theorem emit_transitionProgram_raw {n : Nat} (M : Machine) (width time : Expr n)
    (input : SAT.Word) (env : Env n) (hw : 0 < width.eval env)
    (cell : Cell n) (actual : FiniteRows.Cell (width.eval env))
    (h : cell.Realizes env actual) :
    (transitionProgram M width time cell).emit input env =
      (RawConstraint.ofTree (rowMap (width.eval env) (time.eval env))
        (FiniteRows.transitionTreeCell M (width.eval env) hw actual)).encode
          ((time.eval env + 1) * (2 * width.eval env + 1) + actual.slot.val) := by
  rw [transitionProgram, ConstraintEmitter.Tree.emit_program,
    eval_transitionTree M width time env hw cell actual h, eval_rowIndex,
    Cell.eval_index width env rfl cell actual h]
  rfl

/-- Exact CNF emitted for one cell of one unrolled machine transition. -/
theorem emit_transitionProgram {n T W : Nat} (M : Machine) (width time : Expr n)
    (input : SAT.Word) (env : Env n) (hw : 0 < W) (hwidth : width.eval env = W)
    (t : Fin T) (htime : time.eval env = t.val)
    (cell : Cell n) (actual : FiniteRows.Cell W) (h : cell.Realizes env actual) :
    (transitionProgram M width time cell).emit input env =
      (((FiniteRows.transitionTreeCell M W hw actual).mapVars
          (Tableau.cell t.castSucc)).encode (Tableau.cell t.succ actual.slot)).map
        CSPSAT.forbiddenClause := by
  subst W
  rw [emit_transitionProgram_raw M width time input env hw cell actual h, htime]
  change (RawConstraint.ofTree
      (fun slot => (Tableau.cell t.castSucc slot).val)
      (FiniteRows.transitionTreeCell M (width.eval env) hw actual)).encode
        (Tableau.cell t.succ actual.slot).val = _
  rw [← RawConstraint.ofTree_mapVars]
  exact RawConstraint.encode_ofTree_val _ _

end Complexity.MachineEmitter
