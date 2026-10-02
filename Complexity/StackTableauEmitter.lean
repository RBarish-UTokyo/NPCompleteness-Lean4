module

public import Complexity.SAT
import Lean.Elab.Tactic.Omega

/-!
A finite, first-order syntax for constructing CNF formulas. Numeric expressions
contain only elementary unary arithmetic. Counted loops bind their descending
index, and input inspection has explicit branches for end-of-input and both
Boolean symbols. These semantics make no unit-cost computational assertion;
compilation to elementary finite stack machines is a separate theorem.
-/

@[expose] public section

namespace Complexity.StackTableauEmitter

abbrev Env (n : Nat) := Fin n → Nat

def extend {n : Nat} (value : Nat) (env : Env n) : Env (n + 1) :=
  Fin.cases value env

@[simp] theorem extend_zero {n : Nat} (value : Nat) (env : Env n) :
    extend value env 0 = value := rfl

@[simp] theorem extend_succ {n : Nat} (value : Nat) (env : Env n) (i : Fin n) :
    extend value env i.succ = env i := rfl

inductive NumExpr (n : Nat) where
  | var (index : Fin n)
  | const (value : Nat)
  | add (left right : NumExpr n)
  | mul (left right : NumExpr n)
  | sub (left right : NumExpr n)
  | pred (value : NumExpr n)

def NumExpr.eval {n : Nat} : NumExpr n → Env n → Nat
  | .var index, env => env index
  | .const value, _ => value
  | .add left right, env => left.eval env + right.eval env
  | .mul left right, env => left.eval env * right.eval env
  | .sub left right, env => left.eval env - right.eval env
  | .pred value, env => value.eval env - 1

structure LiteralExpr (n : Nat) where
  index : NumExpr n
  positive : Bool

def LiteralExpr.eval {n : Nat} (literal : LiteralExpr n) (env : Env n) : SAT.Literal :=
  ⟨literal.index.eval env, literal.positive⟩

inductive ClauseProgram : Nat → Type where
  | clause {n : Nat} (literals : List (LiteralExpr n)) : ClauseProgram n
  | seq {n : Nat} (first second : ClauseProgram n) : ClauseProgram n
  | forDown {n : Nat} (bound : NumExpr n) (body : ClauseProgram (n + 1)) : ClauseProgram n
  | ifLe {n : Nat} (left right : NumExpr n) (yes no : ClauseProgram n) : ClauseProgram n
  | ifInput {n : Nat} (index : NumExpr n) (empty zero one : ClauseProgram n) : ClauseProgram n

def ClauseProgram.emit {n : Nat} (program : ClauseProgram n)
    (input : SAT.Word) (env : Env n) : SAT.CNF :=
  match program with
  | .clause literals => [literals.map (fun literal => literal.eval env)]
  | .seq first second => first.emit input env ++ second.emit input env
  | .forDown bound body =>
      (List.range (bound.eval env)).reverse.flatMap (fun i => body.emit input (extend i env))
  | .ifLe left right yes no =>
      if left.eval env ≤ right.eval env then yes.emit input env else no.emit input env
  | .ifInput index empty zero one =>
      match input[index.eval env]? with
      | none => empty.emit input env
      | some false => zero.emit input env
      | some true => one.emit input env

/-- An empty clause sequence, built without adding a special instruction. -/
def ClauseProgram.skip {n : Nat} : ClauseProgram n :=
  .forDown (.const 0) (.clause [])

@[simp] theorem ClauseProgram.emit_skip {n : Nat} (input : SAT.Word) (env : Env n) :
    (ClauseProgram.skip (n := n)).emit input env = [] := rfl

@[simp] theorem ClauseProgram.emit_clause {n : Nat} (literals : List (LiteralExpr n))
    (input : SAT.Word) (env : Env n) :
    (ClauseProgram.clause literals).emit input env =
      [literals.map (fun literal => literal.eval env)] := rfl

@[simp] theorem ClauseProgram.emit_seq {n : Nat} (first second : ClauseProgram n)
    (input : SAT.Word) (env : Env n) :
    (ClauseProgram.seq first second).emit input env =
      first.emit input env ++ second.emit input env := rfl

@[simp] theorem ClauseProgram.emit_forDown {n : Nat} (bound : NumExpr n)
    (body : ClauseProgram (n + 1)) (input : SAT.Word) (env : Env n) :
    (ClauseProgram.forDown bound body).emit input env =
      (List.range (bound.eval env)).reverse.flatMap (fun i => body.emit input (extend i env)) := rfl

/-- One descending iteration followed by the smaller descending loop. -/
theorem range_reverse_succ_flatMap {α : Type} (n : Nat) (body : Nat → List α) :
    (List.range (n + 1)).reverse.flatMap body =
      body n ++ (List.range n).reverse.flatMap body := by
  simp [List.range_succ]

end Complexity.StackTableauEmitter
