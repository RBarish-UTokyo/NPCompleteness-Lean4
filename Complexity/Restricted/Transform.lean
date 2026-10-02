module

public import Complexity.Restricted.Annotate
public import Complexity.ConstraintEmitter
import Lean.Elab.Tactic.Omega

/-!
# Transformations of clause programs

Syntactic transformations of first-order clause programs (`ClauseProgram`), with the exact
formulas they emit:

* `mapClauses` replaces every `clause` node by a fixed clause program;
* `unitG` and `pad2G` are local rewritings (no fresh variables): the empty clause becomes eight
  unsatisfiable three-literal clauses over the variables `0, 1, 2`, a unit clause `a` becomes
  the four clauses `a ∨ ±y ∨ ±z`, and a two-literal clause `a ∨ b` becomes
  `a ∨ b ∨ y`, `a ∨ b ∨ ¬y`, with `y`, `z` distinct from the variables of the clause;
* `occFull` replaces every literal occurrence by a copy variable, splits long clauses by
  implication chains and adds the implication cycles of `Complexity.Restricted.output`.
-/

@[expose] public section

namespace Complexity.Restricted

open Complexity.SAT StackTableauEmitter

/-! ### Clause lists as programs -/

def clausesProg {n : Nat} : List (List (LiteralExpr n)) → ClauseProgram n
  | [] => .skip
  | c :: cs => .seq (.clause c) (clausesProg cs)

theorem emit_clausesProg {n : Nat} (input : Word) (env : Env n) :
    ∀ cs : List (List (LiteralExpr n)),
      (clausesProg cs).emit input env = cs.map (fun c => c.map (fun l => l.eval env))
  | [] => rfl
  | c :: cs => by simp [clausesProg, emit_clausesProg input env cs]

/-! ### Replacing clause nodes -/

def mapClauses (g : (n : Nat) → List (LiteralExpr n) → ClauseProgram n) :
    {n : Nat} → ClauseProgram n → ClauseProgram n
  | n, .clause lits => g n lits
  | _, .seq a b => .seq (mapClauses g a) (mapClauses g b)
  | _, .forDown bound body => .forDown bound (mapClauses g body)
  | _, .ifLe l r y no => .ifLe l r (mapClauses g y) (mapClauses g no)
  | _, .ifInput idx e z o => .ifInput idx (mapClauses g e) (mapClauses g z) (mapClauses g o)

theorem emit_mapClauses (g : (n : Nat) → List (LiteralExpr n) → ClauseProgram n)
    (h : Clause → CNF)
    (hg : ∀ (n : Nat) (lits : List (LiteralExpr n)) (input : Word) (env : Env n),
      (g n lits).emit input env = h (lits.map (fun l => l.eval env))) (input : Word) :
    ∀ {n : Nat} (P : ClauseProgram n) (env : Env n),
      (mapClauses g P).emit input env = (P.emit input env).flatMap h
  | _, .clause lits, env => by simp [mapClauses, hg]
  | _, .seq a b, env => by
      simp [mapClauses, emit_mapClauses g h hg input a, emit_mapClauses g h hg input b]
  | _, .forDown bound body, env => by
      simp only [mapClauses, ClauseProgram.emit, List.flatMap_assoc]
      congr 1
      funext i
      exact emit_mapClauses g h hg input body _
  | _, .ifLe l r y no, env => by
      simp only [mapClauses, ClauseProgram.emit]
      split
      · exact emit_mapClauses g h hg input y env
      · exact emit_mapClauses g h hg input no env
  | _, .ifInput idx e z o, env => by
      simp only [mapClauses, ClauseProgram.emit]
      cases input[idx.eval env]? with
      | none => exact emit_mapClauses g h hg input e env
      | some b =>
        cases b
        · exact emit_mapClauses g h hg input z env
        · exact emit_mapClauses g h hg input o env

theorem evalCNF_flatMap_of_equiv (a : Assignment) (h : Clause → CNF)
    (hh : ∀ c, evalCNF a (h c) = evalClause a c) :
    ∀ F : CNF, evalCNF a (F.flatMap h) = evalCNF a F
  | [] => rfl
  | c :: F => by
      simp only [List.flatMap_cons, evalCNF_append, evalCNF_cons, hh,
        evalCNF_flatMap_of_equiv a h hh F]

theorem satisfiable_flatMap_iff (h : Clause → CNF)
    (hh : ∀ a c, evalCNF a (h c) = evalClause a c) (F : CNF) :
    Satisfiable (F.flatMap h) ↔ Satisfiable F := by
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨a, by rwa [evalCNF_flatMap_of_equiv a h (hh a)] at ha⟩
  · rintro ⟨a, ha⟩
    exact ⟨a, by rwa [evalCNF_flatMap_of_equiv a h (hh a)]⟩

/-! ### Removing empty and unit clauses -/

def signPatterns : List (Bool × Bool × Bool) :=
  [true, false].flatMap (fun s0 => [true, false].flatMap (fun s1 =>
    [true, false].map (fun s2 => (s0, s1, s2))))

/-- The eight clauses over the variables `0, 1, 2` with all sign patterns. -/
def uVal : CNF :=
  signPatterns.map (fun s => [⟨0, s.1⟩, ⟨1, s.2.1⟩, ⟨2, s.2.2⟩])

def uExprs {n : Nat} : List (List (LiteralExpr n)) :=
  signPatterns.map (fun s => [⟨.const 0, s.1⟩, ⟨.const 1, s.2.1⟩, ⟨.const 2, s.2.2⟩])

def unitVal : Clause → CNF
  | [] => uVal
  | [l] => [[l, ⟨l.var + 1, true⟩, ⟨l.var + 2, true⟩], [l, ⟨l.var + 1, true⟩, ⟨l.var + 2, false⟩],
      [l, ⟨l.var + 1, false⟩, ⟨l.var + 2, true⟩], [l, ⟨l.var + 1, false⟩, ⟨l.var + 2, false⟩]]
  | c => [c]

def unitG (n : Nat) : List (LiteralExpr n) → ClauseProgram n
  | [] => clausesProg uExprs
  | [l] => clausesProg
      [[l, ⟨.add l.index (.const 1), true⟩, ⟨.add l.index (.const 2), true⟩],
        [l, ⟨.add l.index (.const 1), true⟩, ⟨.add l.index (.const 2), false⟩],
        [l, ⟨.add l.index (.const 1), false⟩, ⟨.add l.index (.const 2), true⟩],
        [l, ⟨.add l.index (.const 1), false⟩, ⟨.add l.index (.const 2), false⟩]]
  | l :: m :: rest => .clause (l :: m :: rest)

theorem unitG_emit (n : Nat) (lits : List (LiteralExpr n)) (input : Word) (env : Env n) :
    (unitG n lits).emit input env = unitVal (lits.map (fun l => l.eval env)) := by
  match lits with
  | [] => simp [unitG, emit_clausesProg, uExprs, uVal, unitVal, signPatterns, LiteralExpr.eval,
      NumExpr.eval]
  | [l] => simp [unitG, emit_clausesProg, unitVal, LiteralExpr.eval, NumExpr.eval]
  | l :: m :: rest => simp [unitG, unitVal]

theorem unitVal_eval (a : Assignment) (c : Clause) : evalCNF a (unitVal c) = evalClause a c := by
  match c with
  | [] =>
    simp only [unitVal, uVal, signPatterns, evalClause_nil]
    cases h0 : a 0 <;> cases h1 : a 1 <;> cases h2 : a 2 <;>
      simp [evalCNF, evalClause, evalLiteral, h0, h1, h2]
  | [l] =>
    simp only [unitVal]
    cases hl : evalLiteral a l <;> cases h1 : a (l.var + 1) <;> cases h2 : a (l.var + 2) <;>
      simp [evalCNF, evalClause, evalLiteral, h1, h2]
  | l :: m :: rest => simp [unitVal, evalCNF]

theorem unitVal_length (c : Clause) : ∀ c' ∈ unitVal c, 2 ≤ c'.length := by
  match c with
  | [] => simp [unitVal, uVal, signPatterns]
  | [l] => simp [unitVal]
  | l :: m :: rest => simp [unitVal]

/-! ### Padding two-literal clauses -/

def pad2Val : Clause → CNF
  | [a, b] => [[a, b, ⟨a.var + b.var + 1, true⟩], [a, b, ⟨a.var + b.var + 1, false⟩]]
  | c => [c]

def pad2G (n : Nat) : List (LiteralExpr n) → ClauseProgram n
  | [a, b] => .seq (.clause [a, b, ⟨.add (.add a.index b.index) (.const 1), true⟩])
      (.clause [a, b, ⟨.add (.add a.index b.index) (.const 1), false⟩])
  | [] => .clause []
  | [a] => .clause [a]
  | a :: b :: c :: rest => .clause (a :: b :: c :: rest)

theorem pad2G_emit (n : Nat) (lits : List (LiteralExpr n)) (input : Word) (env : Env n) :
    (pad2G n lits).emit input env = pad2Val (lits.map (fun l => l.eval env)) := by
  match lits with
  | [a, b] => simp [pad2G, pad2Val, LiteralExpr.eval, NumExpr.eval]
  | [] => rfl
  | [a] => rfl
  | a :: b :: c :: rest => simp [pad2G, pad2Val]

theorem pad2Val_eval (a : Assignment) (c : Clause) : evalCNF a (pad2Val c) = evalClause a c := by
  match c with
  | [x, y] =>
    simp only [pad2Val]
    cases h : a (x.var + y.var + 1) <;> simp [evalCNF, evalClause, h]
  | [] => simp [pad2Val, evalCNF]
  | [x] => simp [pad2Val, evalCNF]
  | x :: y :: z :: rest => simp [pad2Val, evalCNF]

theorem pad2Val_shape (c : Clause)
    (hc : (c.length = 2 ∨ c.length = 3) ∧ (c.map Literal.var).Nodup) :
    ∀ c' ∈ pad2Val c, c'.length = 3 ∧ (c'.map Literal.var).Nodup := by
  match c, hc with
  | [x, y], ⟨_, hnd⟩ =>
    simp only [List.map_cons, List.map_nil, List.nodup_cons, List.mem_cons, List.not_mem_nil,
      or_false, List.nodup_nil, and_true] at hnd
    intro c' hc'
    simp only [pad2Val, List.mem_cons, List.not_mem_nil, or_false] at hc'
    rcases hc' with rfl | rfl <;>
      simp only [List.length_cons, List.length_nil, List.map_cons, List.map_nil,
        List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, List.nodup_nil, and_true]
    all_goals
      have := hnd.1
      refine ⟨trivial, ?_, ?_, fun h => h⟩ <;> omega
  | [], ⟨h, _⟩ => simp at h
  | [x], ⟨h, _⟩ => simp at h
  | [x, y, z], ⟨_, hnd⟩ =>
    intro c' hc'
    simp only [pad2Val, List.mem_cons, List.not_mem_nil, or_false] at hc'
    subst hc'
    exact ⟨rfl, hnd⟩
  | x :: y :: z :: w :: rest, ⟨h, _⟩ => simp at h

/-! ### Copies, chains and cycles as a program -/

def wExpr {n : Nat} (Pt : Nat) (R v : NumExpr n) (p : Nat) (r : NumExpr n) : NumExpr n :=
  .mul (.const 2) (.add (.mul (.add (.mul v (.const Pt)) (.const p)) R) r)

def zExpr {n : Nat} (R : NumExpr n) (q : Nat) (r : NumExpr n) : NumExpr n :=
  .add (.mul (.const 2) (.add (.mul (.const q) R) r)) (.const 1)

@[simp] theorem eval_wExpr {n : Nat} (Pt : Nat) (R v : NumExpr n) (p : Nat) (r : NumExpr n)
    (env : Env n) :
    (wExpr Pt R v p r).eval env = wVal Pt (R.eval env) (v.eval env) p (r.eval env) := rfl

@[simp] theorem eval_zExpr {n : Nat} (R : NumExpr n) (q : Nat) (r : NumExpr n) (env : Env n) :
    (zExpr R q r).eval env = zVal (R.eval env) q (r.eval env) := rfl

def copiesE {n : Nat} (Pt : Nat) (R r : NumExpr n) : Nat → List (LiteralExpr n) →
    List (LiteralExpr n)
  | _, [] => []
  | p, l :: ls => ⟨wExpr Pt R l.index p r, false⟩ :: copiesE Pt R r (p + 1) ls

theorem copiesE_eval {n : Nat} (Pt : Nat) (R r : NumExpr n) (env : Env n) :
    ∀ (p : Nat) (lits : List (LiteralExpr n)),
      (copiesE Pt R r p lits).map (fun l => l.eval env) =
        copiesV Pt (R.eval env) (r.eval env) p (lits.map (fun l => l.eval env))
  | _, [] => rfl
  | p, l :: ls => by
      simp only [copiesE, List.map_cons, copiesV, copiesE_eval Pt R r env (p + 1) ls]
      rfl

/-- The slot expression of a clause node at loop depth `d`. -/
def slotE {n : Nat} (D : Nat) (B acc : NumExpr n) (d : Nat) : NumExpr n :=
  .mul acc (CookLevinEmitter.powerExpr B (D - d))

/-- Replace every clause node by its chain of copy literals. -/
def occ (Pt D : Nat) : {n : Nat} → NumExpr n → NumExpr n → NumExpr n → ClauseProgram n →
    Nat → Nat → ClauseProgram n
  | _, B, R, acc, .clause lits, off, d =>
      clausesProg (gadget (fun j => ⟨zExpr R (off + j) (slotE D B acc d), true⟩)
        (fun j => ⟨zExpr R (off + j) (slotE D B acc d), false⟩)
        (copiesE Pt R (slotE D B acc d) off lits))
  | _, B, R, acc, .seq a b, off, d =>
      .seq (occ Pt D B R acc a off d) (occ Pt D B R acc b (off + width a) d)
  | _, B, R, acc, .forDown bound body, off, d =>
      .forDown bound (occ Pt D B.lift R.lift (.add (.mul acc.lift B.lift) (.var 0)) body off (d + 1))
  | _, B, R, acc, .ifLe l r y no, off, d =>
      .ifLe l r (occ Pt D B R acc y off d) (occ Pt D B R acc no (off + width y) d)
  | _, B, R, acc, .ifInput idx e z o, off, d =>
      .ifInput idx (occ Pt D B R acc e off d) (occ Pt D B R acc z (off + width e) d)
        (occ Pt D B R acc o (off + width e + width z) d)

theorem occ_emit (Pt D : Nat) (input : Word) :
    ∀ {n : Nat} (P : ClauseProgram n) (B R acc : NumExpr n) (env : Env n) (off d : Nat),
      (occ Pt D B R acc P off d).emit input env =
        (annot (B.eval env) D input P env off d (acc.eval env)).flatMap
          (gadgetVal Pt (R.eval env))
  | _, .clause lits, B, R, acc, env, off, d => by
      simp only [occ, emit_clausesProg, annot, List.flatMap_cons, List.flatMap_nil,
        List.append_nil, gadgetVal]
      rw [← gadget_map (fun l : LiteralExpr _ => l.eval env), copiesE_eval]
      congr 1
      · funext j
        simp [LiteralExpr.eval, zpV, slotE, NumExpr.eval]
      · funext j
        simp [LiteralExpr.eval, znV, slotE, NumExpr.eval]
      · simp [slotE, NumExpr.eval]
  | _, .seq a b, B, R, acc, env, off, d => by
      simp [occ, annot, occ_emit Pt D input a, occ_emit Pt D input b]
  | _, .forDown bound body, B, R, acc, env, off, d => by
      simp only [occ, annot, ClauseProgram.emit, List.flatMap_assoc]
      congr 1
      funext i
      rw [occ_emit Pt D input body]
      simp [NumExpr.eval]
  | _, .ifLe l r y no, B, R, acc, env, off, d => by
      simp only [occ, annot, ClauseProgram.emit]
      split
      · exact occ_emit Pt D input y _ _ _ _ _ _
      · exact occ_emit Pt D input no _ _ _ _ _ _
  | _, .ifInput idx e z o, B, R, acc, env, off, d => by
      simp only [occ, annot, ClauseProgram.emit]
      cases input[idx.eval env]? with
      | none => exact occ_emit Pt D input e _ _ _ _ _ _
      | some b =>
        cases b
        · exact occ_emit Pt D input z _ _ _ _ _ _
        · exact occ_emit Pt D input o _ _ _ _ _ _

/-- The implication cycles of all variables below `N`. -/
def cycleProg (Pt : Nat) (σ : Nat → Bool) (N R : NumExpr 1) : ClauseProgram 1 :=
  .forDown N (ConstraintEmitter.sequence ((List.range Pt).map (fun p =>
    .forDown R.lift
      (.ifLe (.add (.var 0) (.const 2)) R.lift.lift
        (.clause [⟨wExpr Pt R.lift.lift (.var 1) p (.var 0), σ p⟩,
          ⟨wExpr Pt R.lift.lift (.var 1) p (.add (.var 0) (.const 1)), !σ p⟩])
        (.clause [⟨wExpr Pt R.lift.lift (.var 1) p (.var 0), σ p⟩,
          ⟨wExpr Pt R.lift.lift (.var 1) ((p + 1) % Pt) (.const 0), !σ ((p + 1) % Pt)⟩])))))

theorem emit_cycleProg (Pt : Nat) (σ : Nat → Bool) (N R : NumExpr 1) (input : Word)
    (env : Env 1) :
    (cycleProg Pt σ N R).emit input env = cyclesVal (N.eval env) Pt (R.eval env) σ := by
  simp only [cycleProg, ClauseProgram.emit_forDown, cyclesVal]
  congr 1
  funext v
  rw [ConstraintEmitter.emit_sequence, List.flatMap_map]
  congr 1
  funext p
  rw [ClauseProgram.emit_forDown, List.map_eq_flatMap]
  simp only [NumExpr.eval_lift]
  congr 1
  funext r
  have e1 : extend r (extend v env) (1 : Fin 3) = v := rfl
  have e2 : R.lift.lift.eval (extend r (extend v env)) = R.eval env := by
    simp only [NumExpr.eval_lift]
  simp only [ClauseProgram.emit, NumExpr.eval, e1, e2, extend_zero, cycleClause, nextSlot,
    List.map_cons, List.map_nil, LiteralExpr.eval, eval_wExpr]
  split <;> simp_all

end Complexity.Restricted
