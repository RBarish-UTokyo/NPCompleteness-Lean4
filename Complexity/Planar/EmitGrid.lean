module

public import Complexity.Planar.EmitTable
public import Complexity.Planar.GridTarget
import Lean.Elab.Tactic.Omega

/-!
# Emitting the grid formula

Emitters producing exactly `gridCNF W M bits` and `plainCNF W M bits`, where `W`, `M` and the
positions of the occurrence bits are numeric expressions, and `bits` is read from the input
word: the occurrence bits of clause `j` and variable `v` are the input bits at the positions
`posN A M R W j v 1` and `posN A M R W j v 0` (missing bits read as `false`).

The programs follow the definitions of `Complexity.Planar.Grid` literally: descending loops are
`(List.range n).reverse.flatMap`, and the order of the clauses is the order of the definitions.
-/

@[expose] public section

namespace Complexity.Planar.Emit

open StackTableauEmitter SAT Grid

@[simp] theorem extend_one {k : Nat} (a b : Nat) (env : Env k) :
    extend a (extend b env) (1 : Fin (k + 2)) = b := rfl

/-! ## Expressions -/

section exprs

variable {k : Nat}

def colLenE (W : NumExpr k) : NumExpr k := .add (.mul (.const 9) W) (.const 3)

def colBaseE (W j : NumExpr k) : NumExpr k := .mul j (colLenE W)

def cellOffE (W j idx : NumExpr k) : NumExpr k :=
  .add (.add (colBaseE W j) (.const 1)) (.mul (.const 9) idx)

/-- `W - 1 - v`. -/
def revE (W v : NumExpr k) : NumExpr k := .sub (.sub W (.const 1)) v

def rowE (W : NumExpr k) (odd : Bool) (idx : NumExpr k) : NumExpr k :=
  if odd then revE W idx else idx

def posE (A M R W j v : NumExpr k) (s : Nat) : NumExpr k :=
  .add (.add (.add (.mul (.const 2) A) (.mul M R)) (.const 3))
    (.mul (.const 4) (.add (.mul j R) (.add (.mul (.const 2) (revE W v)) (.const (1 - s)))))

variable (env : Env k)

@[simp] theorem colBaseE_eval (W j : NumExpr k) :
    (colBaseE W j).eval env = colBase (W.eval env) (j.eval env) := rfl

@[simp] theorem cellOffE_eval (W j idx : NumExpr k) :
    (cellOffE W j idx).eval env = cellOff (W.eval env) (j.eval env) (idx.eval env) := rfl

@[simp] theorem revE_eval (W v : NumExpr k) : (revE W v).eval env = W.eval env - 1 - v.eval env :=
  rfl

@[simp] theorem rowE_eval (W : NumExpr k) (odd : Bool) (idx : NumExpr k) :
    (rowE W odd idx).eval env = row (W.eval env) odd (idx.eval env) := by
  cases odd <;> rfl

@[simp] theorem posE_eval (A M R W j v : NumExpr k) (s : Nat) :
    (posE A M R W j v s).eval env =
      posN (A.eval env) (M.eval env) (R.eval env) (W.eval env) (j.eval env) (v.eval env) s := rfl

end exprs

/-! ## Lists of clauses -/

/-- A fixed list of clauses. -/
def clausesProg {k : Nat} : List (List (LiteralExpr k)) → ClauseProgram k
  | [] => .skip
  | c :: cs => .seq (.clause c) (clausesProg cs)

theorem clausesProg_emit {k : Nat} (cs : List (List (LiteralExpr k))) (w : Word) (env : Env k) :
    (clausesProg cs).emit w env = cs.map (fun c => c.map (fun l => l.eval env)) := by
  induction cs with
  | nil => rfl
  | cons c cs ih => simp only [clausesProg, ClauseProgram.emit_seq, ih]; rfl

/-- A template clause at the offset `o`. -/
def instE {k : Nat} (o : NumExpr k) (odd : Bool) (t : TCl) : List (LiteralExpr k) :=
  if t.2 != odd then t.1.map (fun l => ⟨.add o (.const l.1), l.2⟩)
  else (t.1.map (fun l => ⟨.add o (.const l.1), l.2⟩)).reverse

theorem instE_eval {k : Nat} (o : NumExpr k) (odd : Bool) (t : TCl) (env : Env k) :
    (instE o odd t).map (fun l => l.eval env) = inst (o.eval env) odd t := by
  unfold instE inst
  split
  · simp [LiteralExpr.eval, NumExpr.eval]
  · simp [List.map_reverse, LiteralExpr.eval, NumExpr.eval]

/-- The occurrence bits read from the input. -/
def bitsW (w : Word) (A M R W : Nat) : Nat → Nat → Bool × Bool := fun j v =>
  ((w[posN A M R W j v 1]?).getD false, (w[posN A M R W j v 0]?).getD false)

theorem ifInput_bool {k : Nat} (e : NumExpr k) (F : Bool → ClauseProgram k) (w : Word)
    (env : Env k) :
    (ClauseProgram.ifInput e (F false) (F false) (F true)).emit w env =
      (F ((w[e.eval env]?).getD false)).emit w env := by
  simp only [ClauseProgram.emit]
  cases w[e.eval env]? with
  | none => rfl
  | some b => cases b <;> rfl

/-! ## Columns -/

section column

variable {k : Nat}

def cellProg (W j idx : NumExpr k) (odd bp bn : Bool) : ClauseProgram k :=
  clausesProg ((cellT bp bn).map (instE (cellOffE W j idx) odd))

/-- A cell, reading its occurrence bits. -/
def cellFull (A M R W j idx : NumExpr k) (odd : Bool) : ClauseProgram k :=
  .ifInput (posE A M R W j (rowE W odd idx) 1)
    (.ifInput (posE A M R W j (rowE W odd idx) 0) (cellProg W j idx odd false false)
      (cellProg W j idx odd false false) (cellProg W j idx odd false true))
    (.ifInput (posE A M R W j (rowE W odd idx) 0) (cellProg W j idx odd false false)
      (cellProg W j idx odd false false) (cellProg W j idx odd false true))
    (.ifInput (posE A M R W j (rowE W odd idx) 0) (cellProg W j idx odd true false)
      (cellProg W j idx odd true false) (cellProg W j idx odd true true))

def startProg (W j : NumExpr k) : ClauseProgram k :=
  clausesProg [[⟨colBaseE W j, true⟩, ⟨.add (colBaseE W j) (.const 1), false⟩],
    [⟨.add (colBaseE W j) (.const 1), false⟩, ⟨colBaseE W j, false⟩]]

def endProg (W j : NumExpr k) : ClauseProgram k :=
  clausesProg [[⟨cellOffE W j W, true⟩, ⟨.add (cellOffE W j W) (.const 1), true⟩],
    [⟨.add (cellOffE W j W) (.const 1), false⟩, ⟨cellOffE W j W, true⟩]]

def columnProg (A M R W j : NumExpr k) (odd : Bool) : ClauseProgram k :=
  .seq (.seq (startProg W j)
    (.forDown W (cellFull A.lift M.lift R.lift W.lift j.lift (.var 0) odd))) (endProg W j)

variable (w : Word) (env : Env k)

theorem cellProg_emit (W j idx : NumExpr k) (odd bp bn : Bool) :
    (cellProg W j idx odd bp bn).emit w env =
      cellCNF (W.eval env) (j.eval env) (idx.eval env) odd (bp, bn) := by
  unfold cellProg cellCNF
  rw [clausesProg_emit, List.map_map]
  apply List.map_congr_left
  intro t _
  simp only [Function.comp, instE_eval, cellOffE_eval]

theorem cellFull_emit (A M R W j idx : NumExpr k) (odd : Bool) :
    (cellFull A M R W j idx odd).emit w env =
      cellCNF (W.eval env) (j.eval env) (idx.eval env) odd
        (bitsW w (A.eval env) (M.eval env) (R.eval env) (W.eval env) (j.eval env)
          (row (W.eval env) odd (idx.eval env))) := by
  unfold cellFull bitsW
  rw [ifInput_bool _ (fun bp => .ifInput (posE A M R W j (rowE W odd idx) 0)
    (cellProg W j idx odd bp false) (cellProg W j idx odd bp false) (cellProg W j idx odd bp true))]
  · simp only [posE_eval, rowE_eval]
    cases (w[posN (A.eval env) (M.eval env) (R.eval env) (W.eval env) (j.eval env)
      (row (W.eval env) odd (idx.eval env)) 1]?.getD false) <;>
    · rw [ifInput_bool _ (fun bn => cellProg W j idx _ _ bn), cellProg_emit]
      simp only [posE_eval, rowE_eval]

theorem columnProg_emit (A M R W j : NumExpr k) (odd : Bool) :
    (columnProg A M R W j odd).emit w env =
      column (W.eval env) (j.eval env) odd
        (bitsW w (A.eval env) (M.eval env) (R.eval env) (W.eval env)) := by
  unfold columnProg column startProg endProg
  simp only [ClauseProgram.emit_seq, ClauseProgram.emit_forDown, clausesProg_emit]
  congr 1
  congr 1
  apply flatMap_congr_range
  intro idx _
  rw [cellFull_emit]
  simp only [NumExpr.eval_lift, NumExpr.eval, extend_zero]

end column

/-! ## Rainbows -/

section rainbow

variable {k : Nat}

def rbEvenProg (W j v : NumExpr k) : ClauseProgram k :=
  clausesProg
    [[⟨.add (cellOffE W j v) (.const 8), false⟩,
      ⟨.add (cellOffE W (.add j (.const 1)) (revE W v)) (.const 1), true⟩],
     [⟨.add (cellOffE W j v) (.const 8), true⟩,
      ⟨.add (cellOffE W (.add j (.const 1)) (revE W v)) (.const 1), false⟩]]

def rbOddProg (W j v : NumExpr k) : ClauseProgram k :=
  clausesProg
    [[⟨.add (cellOffE W (.add j (.const 1)) v) (.const 1), true⟩,
      ⟨.add (cellOffE W j (revE W v)) (.const 8), false⟩],
     [⟨.add (cellOffE W (.add j (.const 1)) v) (.const 1), false⟩,
      ⟨.add (cellOffE W j (revE W v)) (.const 8), true⟩]]

variable (w : Word) (env : Env k)

theorem rbEvenProg_emit (W j v : NumExpr k) :
    (rbEvenProg W j v).emit w env = rbEven (W.eval env) (j.eval env) (v.eval env) := by
  unfold rbEvenProg rbEven
  rw [clausesProg_emit]
  rfl

theorem rbOddProg_emit (W j v : NumExpr k) :
    (rbOddProg W j v).emit w env = rbOdd (W.eval env) (j.eval env) (v.eval env) := by
  unfold rbOddProg rbOdd
  rw [clausesProg_emit]
  rfl

end rainbow

/-! ## The grid formula -/

section grid

variable {k : Nat}

def twoE (e : NumExpr k) (c : Nat) : NumExpr k := .add (.mul (.const 2) e) (.const c)

def colsEP (A M R W : NumExpr k) : ClauseProgram k :=
  .forDown M (.ifLe (twoE (.var 0) 1) M.lift
    (columnProg A.lift M.lift R.lift W.lift (twoE (.var 0) 0) false) .skip)

def colsOP (A M R W : NumExpr k) : ClauseProgram k :=
  .forDown M (.ifLe (twoE (.var 0) 2) M.lift
    (columnProg A.lift M.lift R.lift W.lift (twoE (.var 0) 1) true) .skip)

def rbsEP (M W : NumExpr k) : ClauseProgram k :=
  .forDown M (.ifLe (twoE (.var 0) 2) M.lift
    (.forDown W.lift (rbEvenProg W.lift.lift (twoE (.var 1) 0) (.var 0))) .skip)

def rbsOP (M W : NumExpr k) : ClauseProgram k :=
  .forDown M (.ifLe (twoE (.var 0) 3) M.lift
    (.forDown W.lift (rbOddProg W.lift.lift (twoE (.var 1) 1) (.var 0))) .skip)

/-- **The grid emitter.** -/
def gridProg (A M R W : NumExpr k) : ClauseProgram k :=
  .seq (.seq (.seq (colsEP A M R W) (colsOP A M R W)) (rbsEP M W)) (rbsOP M W)

variable (w : Word) (env : Env k)

theorem gridProg_emit (A M R W : NumExpr k) :
    (gridProg A M R W).emit w env =
      gridCNF (W.eval env) (M.eval env)
        (bitsW w (A.eval env) (M.eval env) (R.eval env) (W.eval env)) := by
  unfold gridProg gridCNF colsEP colsOP rbsEP rbsOP
  simp only [ClauseProgram.emit_seq, ClauseProgram.emit_forDown]
  congr 1
  congr 1
  congr 1
  · apply flatMap_congr_range
    intro i _
    simp only [ClauseProgram.emit, twoE, NumExpr.eval, NumExpr.eval_lift, extend_zero,
      columnProg_emit, Nat.add_zero]
    rfl
  · apply flatMap_congr_range
    intro i _
    simp only [ClauseProgram.emit, twoE, NumExpr.eval, NumExpr.eval_lift, extend_zero,
      columnProg_emit]
    rfl
  · apply flatMap_congr_range
    intro i _
    simp only [ClauseProgram.emit, twoE, NumExpr.eval, NumExpr.eval_lift, extend_zero]
    split
    · apply flatMap_congr_range
      intro v _
      rw [rbEvenProg_emit]
      simp only [NumExpr.eval, NumExpr.eval_lift, extend_zero, extend_one, Nat.add_zero]
    · rfl
  · apply flatMap_congr_range
    intro i _
    simp only [ClauseProgram.emit, twoE, NumExpr.eval, NumExpr.eval_lift, extend_zero]
    split
    · apply flatMap_congr_range
      intro v _
      rw [rbOddProg_emit]
      simp only [NumExpr.eval, NumExpr.eval_lift, extend_zero, extend_one]
    · rfl

/-! ## The spine clauses -/

/-- `K = M (9 W + 3)`. -/
def KE (M W : NumExpr k) : NumExpr k := NumExpr.mul M (colLenE W)

/-- The clauses `x_u ∨ z_u ∨ x_{u+1 mod K}` for `K = M (9 W + 3)`. -/
def spineProg (M W : NumExpr k) : ClauseProgram k :=
  .forDown (KE M W)
    (.ifLe (.var 0) (.const 0)
      (.clause [⟨revE (KE M W).lift (.var 0), true⟩,
        ⟨.add (KE M W).lift (revE (KE M W).lift (.var 0)), true⟩,
        ⟨.const 0, true⟩])
      (.clause [⟨revE (KE M W).lift (.var 0), true⟩,
        ⟨.add (KE M W).lift (revE (KE M W).lift (.var 0)), true⟩,
        ⟨.sub (KE M W).lift (.var 0), true⟩]))

omit w env in
theorem flatMap_rev_singleton {α : Type} (K : Nat) (g : Nat → α) :
    (List.range K).reverse.flatMap (fun i => [g (K - 1 - i)]) = (List.range K).map g := by
  have hl : ∀ L : List Nat, L.flatMap (fun i => [g (K - 1 - i)]) =
      L.map (fun i => g (K - 1 - i)) := by
    intro L; induction L with
    | nil => rfl
    | cons a L ih => simp [ih]
  rw [hl]
  apply List.ext_getElem
  · simp
  · intro p h1 h2
    simp only [List.getElem_map, List.getElem_reverse, List.getElem_range, List.length_range]
    congr 1
    simp at h2
    omega

theorem KE_eval (M W : NumExpr k) : (KE M W).eval env = M.eval env * (9 * W.eval env + 3) := rfl

theorem spineProg_emit (M W : NumExpr k) :
    (spineProg M W).emit w env =
      (List.range (M.eval env * (9 * W.eval env + 3))).map
        (spineClause (M.eval env * (9 * W.eval env + 3))) := by
  unfold spineProg
  rw [ClauseProgram.emit_forDown, KE_eval, ← flatMap_rev_singleton]
  apply flatMap_congr_range
  intro i hi
  simp only [ClauseProgram.emit, NumExpr.eval, extend_zero]
  unfold spineClause
  by_cases h : i ≤ 0
  · simp only [h, ↓reduceIte]
    have : i = 0 := by omega
    subst this
    simp only [LiteralExpr.eval, NumExpr.eval, NumExpr.eval_lift, revE_eval, extend_zero,
      KE_eval, List.map_cons, List.map_nil]
    rw [show M.eval env * (9 * W.eval env + 3) - 1 - 0 + 1 = M.eval env * (9 * W.eval env + 3)
      by omega, Nat.mod_self]
  · simp only [h, ↓reduceIte]
    simp only [LiteralExpr.eval, NumExpr.eval, NumExpr.eval_lift, revE_eval, extend_zero,
      KE_eval, List.map_cons, List.map_nil]
    rw [Nat.mod_eq_of_lt (by omega), show M.eval env * (9 * W.eval env + 3) - 1 - i + 1 =
      M.eval env * (9 * W.eval env + 3) - i by omega]

/-- **The plain emitter.** -/
def plainProg (A M R W : NumExpr k) : ClauseProgram k :=
  .seq (gridProg A M R W) (spineProg M W)

theorem plainProg_emit (A M R W : NumExpr k) :
    (plainProg A M R W).emit w env =
      plainCNF (W.eval env) (M.eval env)
        (bitsW w (A.eval env) (M.eval env) (R.eval env) (W.eval env)) := by
  unfold plainProg plainCNF
  rw [ClauseProgram.emit_seq, gridProg_emit, spineProg_emit]

end grid

end Complexity.Planar.Emit
