module

public import Complexity.StackTableauEmitter
public import Complexity.RawConstraint

/-!
Compile a finite symbolic decision tree to explicit clause-emission syntax.
Every finite-domain branch is expanded at compile time; all run-time index
arithmetic belongs to the first-order numeric expression language.
-/

@[expose] public section

namespace Complexity.ConstraintEmitter

open StackTableauEmitter

inductive Tree (n d : Nat) where
  | value (v : Fin (d + 1))
  | query (slot : NumExpr n) (branches : Fin (d + 1) → Tree n d)
  | ifLe (left right : NumExpr n) (yes no : Tree n d)

def Tree.eval {n d : Nat} : Tree n d → Env n → RawConstraint.Tree d
  | .value v, _ => .value v
  | .query slot branches, env => .query (slot.eval env) (fun v => (branches v).eval env)
  | .ifLe left right yes no, env =>
    if left.eval env ≤ right.eval env then yes.eval env else no.eval env

/-- Concatenate a statically fixed list of clause programs. -/
def sequence {n : Nat} : List (ClauseProgram n) → ClauseProgram n
  | [] => .skip
  | program :: rest => .seq program (sequence rest)

theorem emit_sequence {n : Nat} (programs : List (ClauseProgram n))
    (input : SAT.Word) (env : Env n) :
    (sequence programs).emit input env = programs.flatMap (fun program => program.emit input env) := by
  induction programs with
  | nil => rfl
  | cons program programs ih => simp [sequence, ih]

def negative {n : Nat} (d : Nat) (slot : NumExpr n) (value : Nat) : LiteralExpr n :=
  ⟨.add (.mul slot (.const (d + 1))) (.const value), false⟩

@[simp] theorem eval_negative {n : Nat} (d : Nat) (slot : NumExpr n) (value : Nat)
    (env : Env n) :
    (negative d slot value).eval env = RawConstraint.literal d (slot.eval env) value := rfl

/-- Carry the negative literals of the branch path to every emitted leaf. -/
def Tree.programWith {n d : Nat} (target : NumExpr n) (path : List (LiteralExpr n)) :
    Tree n d → ClauseProgram n
  | .value v => sequence
    (((List.finRange (d + 1)).filter (fun other => other != v)).map
      (fun other => .clause (path ++ [negative d target other.val])))
  | .query slot branches => sequence
    ((List.finRange (d + 1)).map (fun v =>
      (branches v).programWith target (path ++ [negative d slot v.val])))
  | .ifLe left right yes no =>
    .ifLe left right (yes.programWith target path) (no.programWith target path)

def Tree.program {n d : Nat} (tree : Tree n d) (target : NumExpr n) : ClauseProgram n :=
  tree.programWith target []

theorem Tree.emit_programWith {n d : Nat} (tree : Tree n d) (target : NumExpr n)
    (path : List (LiteralExpr n)) (input : SAT.Word) (env : Env n) :
    (tree.programWith target path).emit input env =
      ((tree.eval env).encode (target.eval env)).map
        (fun clause => path.map (fun literal => literal.eval env) ++ clause) := by
  induction tree generalizing path with
  | value v =>
    simp [programWith, emit_sequence, eval, RawConstraint.Tree.encode,
      List.flatMap_map, List.map_append, ← List.map_eq_flatMap]
  | query slot branches ih =>
    simp only [programWith, emit_sequence, List.flatMap_map, eval,
      RawConstraint.Tree.encode, List.map_flatMap]
    congr 1
    funext v
    rw [ih]
    simp [List.map_map, List.map_append, List.append_assoc]
  | ifLe left right yes no ihYes ihNo =>
    simp only [programWith, ClauseProgram.emit, eval]
    split <;> simp_all

theorem Tree.emit_program {n d : Nat} (tree : Tree n d) (target : NumExpr n)
    (input : SAT.Word) (env : Env n) :
    (tree.program target).emit input env = (tree.eval env).encode (target.eval env) := by
  simpa [program] using tree.emit_programWith target [] input env

end Complexity.ConstraintEmitter
