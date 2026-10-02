module

public import Complexity.ConstraintEmitter
public import Complexity.Constraints

/-!
Structural utilities for first-order CNF emitters: expression renaming and
one-hot clauses. The following identities concern exact output formulas.
-/

@[expose] public section

namespace Complexity.StackTableauEmitter

def NumExpr.rename {n m : Nat} (f : Fin n → Fin m) : NumExpr n → NumExpr m
  | .var i => .var (f i)
  | .const k => .const k
  | .add a b => .add (a.rename f) (b.rename f)
  | .mul a b => .mul (a.rename f) (b.rename f)
  | .sub a b => .sub (a.rename f) (b.rename f)
  | .pred a => .pred (a.rename f)

@[simp] theorem NumExpr.eval_rename {n m : Nat} (expr : NumExpr n)
    (f : Fin n → Fin m) (env : Env m) :
    (expr.rename f).eval env = expr.eval (fun i => env (f i)) := by
  induction expr <;> simp [rename, eval, *]

def NumExpr.lift {n : Nat} (expr : NumExpr n) : NumExpr (n + 1) := expr.rename Fin.succ

@[simp] theorem NumExpr.eval_lift {n : Nat} (expr : NumExpr n) (value : Nat) (env : Env n) :
    expr.lift.eval (extend value env) = expr.eval env := by simp [lift]

def positiveClause {n : Nat} (variables : List (NumExpr n)) : ClauseProgram n :=
  .clause (variables.map (fun e => ⟨e, true⟩))

def excludeWith {n : Nat} (v : NumExpr n) : List (NumExpr n) → ClauseProgram n
  | [] => .skip
  | w :: rest => .seq (.clause [⟨v, false⟩, ⟨w, false⟩]) (excludeWith v rest)

def atMostOne {n : Nat} : List (NumExpr n) → ClauseProgram n
  | [] => .skip
  | v :: rest => .seq (excludeWith v rest) (atMostOne rest)

def exactlyOne {n : Nat} (variables : List (NumExpr n)) : ClauseProgram n :=
  .seq (positiveClause variables) (atMostOne variables)

@[simp] theorem emit_positiveClause {n : Nat} (variables : List (NumExpr n))
    (input : SAT.Word) (env : Env n) :
    (positiveClause variables).emit input env =
      [Constraints.positiveClause (variables.map (fun e => e.eval env))] := by
  induction variables with
  | nil => rfl
  | cons v rest ih =>
    simp only [positiveClause, ClauseProgram.emit, List.map_cons, Constraints.positiveClause,
      LiteralExpr.eval] at ih ⊢
    have hh := (List.cons.inj ih).1
    rw [hh]

@[simp] theorem emit_excludeWith {n : Nat} (v : NumExpr n) (variables : List (NumExpr n))
    (input : SAT.Word) (env : Env n) :
    (excludeWith v variables).emit input env =
      Constraints.excludeWith (v.eval env) (variables.map (fun e => e.eval env)) := by
  induction variables with
  | nil => rfl
  | cons w rest ih => simp [excludeWith, Constraints.excludeWith, LiteralExpr.eval, ih]

@[simp] theorem emit_atMostOne {n : Nat} (variables : List (NumExpr n))
    (input : SAT.Word) (env : Env n) :
    (atMostOne variables).emit input env =
      Constraints.atMostOne (variables.map (fun e => e.eval env)) := by
  induction variables with
  | nil => rfl
  | cons v rest ih => simp [atMostOne, Constraints.atMostOne, ih]

@[simp] theorem emit_exactlyOne {n : Nat} (variables : List (NumExpr n))
    (input : SAT.Word) (env : Env n) :
    (exactlyOne variables).emit input env =
      Constraints.exactlyOne (variables.map (fun e => e.eval env)) := by
  simp [exactlyOne, Constraints.exactlyOne]

/-- CNF semantics are unchanged by permutations of clauses. -/
def Equivalent (first second : SAT.CNF) : Prop :=
  ∀ a : SAT.Assignment, SAT.evalCNF a first = true ↔ SAT.evalCNF a second = true

theorem Equivalent.refl (f : SAT.CNF) : Equivalent f f := fun _ => Iff.rfl

theorem Equivalent.trans {f g h : SAT.CNF} (hfg : Equivalent f g) (hgh : Equivalent g h) :
    Equivalent f h := fun a => (hfg a).trans (hgh a)

theorem Equivalent.append {f g h k : SAT.CNF} (hfg : Equivalent f g) (hhk : Equivalent h k) :
    Equivalent (f ++ h) (g ++ k) := by
  intro a
  simp only [SAT.evalCNF_append, Bool.and_eq_true]
  exact and_congr (hfg a) (hhk a)

theorem equivalent_of_membership {f g : SAT.CNF}
    (h : ∀ c, c ∈ f ↔ c ∈ g) : Equivalent f g := by
  intro a
  simp only [SAT.evalCNF, List.all_eq_true]
  constructor
  · intro hf c hc
    exact hf c ((h c).mpr hc)
  · intro hg c hc
    exact hg c ((h c).mp hc)

theorem equivalent_flatMap_finRange {m : Nat} (left : Nat → SAT.CNF)
    (right : Fin m → SAT.CNF) (h : ∀ i : Fin m, Equivalent (left i.val) (right i)) :
    Equivalent ((List.range m).reverse.flatMap left) ((List.finRange m).flatMap right) := by
  intro a
  simp only [CSPSAT.evalCNF_flatMap_iff, List.mem_reverse, List.mem_range,
    List.mem_finRange, true_implies]
  constructor
  · intro hl i
    exact (h i a).mp (hl i.val i.isLt)
  · intro hr i hi
    exact (h ⟨i, hi⟩ a).mpr (hr ⟨i, hi⟩)

theorem Equivalent.satisfiable_iff {f g : SAT.CNF} (h : Equivalent f g) :
    SAT.Satisfiable f ↔ SAT.Satisfiable g := by
  constructor
  · intro ⟨a, ha⟩
    exact ⟨a, (h a).mp ha⟩
  · intro ⟨a, ha⟩
    exact ⟨a, (h a).mpr ha⟩

end Complexity.StackTableauEmitter
