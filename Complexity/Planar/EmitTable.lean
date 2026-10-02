module

public import Complexity.Planar.EmitBounds
import Lean.Elab.Tactic.Omega

/-!
# The occurrence table of an emitted formula

The first stage of the reduction to planar 3-SAT turns a formula emitter `P` into an emitter
`stage1 P` whose output describes the formula `φ` emitted by `P` in a rigid format: `A n` empty
clauses followed, for each clause `c` of `φ`, by a row of `2 W n` unit clauses `[⟨0, b⟩]`, the
bit `b` telling whether the variable `v < W n` occurs in `c` positively, resp. negatively.

Rows are emitted by replacing each clause instruction of `P` by two loops over `v` and the sign,
comparing the literals of the clause with `v` arithmetically.  In the code of the output the bit
of clause `j`, variable `v` and sign `s` sits at a position computed by `posN` from `A n`, the
number of clauses of `φ` and `W n`.
-/

@[expose] public section

namespace Complexity.Planar.Emit

open StackTableauEmitter SAT

/-! ## Comparing literals arithmetically -/

/-- `1` if `a = b`, else `0`. -/
def eqE {k : Nat} (a b : NumExpr k) : NumExpr k := .sub (.const 1) (.add (.sub a b) (.sub b a))

theorem eqE_eval {k : Nat} (a b : NumExpr k) (env : Env k) :
    (eqE a b).eval env = if a.eval env = b.eval env then 1 else 0 := by
  simp only [eqE, NumExpr.eval]
  split <;> omega

/-- `s` for a positive literal, `1 - s` for a negative one. -/
def sgnE {k : Nat} (pos : Bool) (s : NumExpr k) : NumExpr k :=
  if pos then s else .sub (.const 1) s

/-- The number of literals of `lits` on the variable `var 1` with the sign `var 0`. -/
def sumE {k : Nat} : List (LiteralExpr k) → NumExpr (k + 2)
  | [] => .const 0
  | l :: ls => .add (.mul (eqE l.index.lift.lift (.var 1)) (sgnE l.positive (.var 0))) (sumE ls)

/-- Whether the variable `v` occurs in `c` with sign `s` (`1`: positive, `0`: negative). -/
def bitB (c : Clause) (v s : Nat) : Bool := c.any fun l => l.var == v && l.positive == (s == 1)

theorem sumE_pos {k : Nat} (lits : List (LiteralExpr k)) (env : Env k) {v s : Nat} (hs : s < 2) :
    1 ≤ (sumE lits).eval (extend s (extend v env)) ↔
      bitB (lits.map (fun literal => literal.eval env)) v s = true := by
  induction lits with
  | nil => simp [sumE, bitB, NumExpr.eval]
  | cons l ls ih =>
    have h1 : extend s (extend v env) (1 : Fin (k + 2)) = v := rfl
    have h0 : extend s (extend v env) (0 : Fin (k + 2)) = s := rfl
    have hterm : (NumExpr.mul (eqE l.index.lift.lift (.var 1)) (sgnE l.positive (.var 0))).eval
        (extend s (extend v env)) =
        if (l.index.eval env == v && l.positive == (s == 1)) = true then 1 else 0 := by
      show (eqE l.index.lift.lift (.var 1)).eval _ * (sgnE l.positive (.var 0)).eval _ = _
      rw [eqE_eval, NumExpr.eval_lift, NumExpr.eval_lift]
      show (if l.index.eval env = extend s (extend v env) 1 then 1 else 0) *
        (sgnE l.positive (.var 0)).eval (extend s (extend v env)) = _
      rw [h1]
      have hsg : (sgnE l.positive (.var 0)).eval (extend s (extend v env)) =
          if l.positive = true then s else 1 - s := by
        cases l.positive
        · show 1 - extend s (extend v env) 0 = _
          rw [h0]; rfl
        · show extend s (extend v env) 0 = _
          rw [h0]; rfl
      rw [hsg]
      rcases (show s = 0 ∨ s = 1 by omega) with rfl | rfl <;> cases l.positive <;>
        by_cases he : l.index.eval env = v <;> simp [he]
    have e : (sumE (l :: ls)).eval (extend s (extend v env)) =
        (NumExpr.mul (eqE l.index.lift.lift (.var 1)) (sgnE l.positive (.var 0))).eval
          (extend s (extend v env)) + (sumE ls).eval (extend s (extend v env)) := rfl
    have e2 : bitB ((l :: ls).map (fun literal => literal.eval env)) v s =
        ((l.index.eval env == v && l.positive == (s == 1)) ||
          bitB (ls.map (fun literal => literal.eval env)) v s) := rfl
    rw [e, hterm, e2, Bool.or_eq_true, ← ih]
    cases (l.index.eval env == v && l.positive == (s == 1)) <;> simp

/-! ## The rows -/

/-- The bits of the row of a clause: for `v = W - 1, …, 0`, the positive then negative bit. -/
def rowBits (W : Nat) (c : Clause) : List Bool :=
  (List.range W).reverse.flatMap fun v => (List.range 2).reverse.flatMap fun s => [bitB c v s]

/-- A bit as a unit clause on the variable `0`. -/
def unitOf (b : Bool) : Clause := [⟨0, b⟩]

/-- The row of a clause. -/
def rowOf (W : Nat) (c : Clause) : CNF :=
  (List.range W).reverse.flatMap fun v => (List.range 2).reverse.flatMap fun s => [unitOf (bitB c v s)]

theorem rowOf_eq (W : Nat) (c : Clause) : rowOf W c = (rowBits W c).map unitOf := by
  unfold rowOf rowBits
  simp [List.map_flatMap]

/-- One emitted bit. -/
def bitProg {k : Nat} (lits : List (LiteralExpr k)) : ClauseProgram (k + 2) :=
  .ifLe (.const 1) (sumE lits) (.clause [⟨.const 0, true⟩]) (.clause [⟨.const 0, false⟩])

theorem bitProg_emit {k : Nat} (lits : List (LiteralExpr k)) (input : Word) (env : Env k)
    {v s : Nat} (hs : s < 2) :
    (bitProg lits).emit input (extend s (extend v env)) =
      [unitOf (bitB (lits.map (fun literal => literal.eval env)) v s)] := by
  unfold bitProg
  simp only [ClauseProgram.emit, NumExpr.eval]
  by_cases h : 1 ≤ (sumE lits).eval (extend s (extend v env))
  · simp only [h, ↓reduceIte]
    rw [(sumE_pos lits env hs).mp h]; rfl
  · simp only [h, ↓reduceIte]
    have : bitB (lits.map (fun literal => literal.eval env)) v s = false := by
      cases hb : bitB (lits.map (fun literal => literal.eval env)) v s
      · rfl
      · exact absurd ((sumE_pos lits env hs).mpr hb) h
    rw [this]; rfl

/-- **The table transformation**: each clause instruction emits the row of its clause. -/
def tab : {k : Nat} → NumExpr k → ClauseProgram k → ClauseProgram k
  | _, Wk, .clause lits => .forDown Wk (.forDown (.const 2) (bitProg lits))
  | _, Wk, .seq a b => .seq (tab Wk a) (tab Wk b)
  | _, Wk, .forDown bound body => .forDown bound (tab Wk.lift body)
  | _, Wk, .ifLe l r y n => .ifLe l r (tab Wk y) (tab Wk n)
  | _, Wk, .ifInput i e z o => .ifInput i (tab Wk e) (tab Wk z) (tab Wk o)

theorem flatMap_congr_range {α : Type} {N : Nat} {f g : Nat → List α}
    (h : ∀ i, i < N → f i = g i) :
    (List.range N).reverse.flatMap f = (List.range N).reverse.flatMap g := by
  induction N with
  | zero => rfl
  | succ N ih =>
    rw [range_reverse_succ_flatMap, range_reverse_succ_flatMap, h N (by omega),
      ih (fun i hi => h i (by omega))]

theorem tab_emit {k : Nat} (P : ClauseProgram k) (input : Word) :
    ∀ (Wk : NumExpr k) (env : Env k),
      (tab Wk P).emit input env = (P.emit input env).flatMap (rowOf (Wk.eval env)) := by
  induction P with
  | clause lits =>
    intro Wk env
    simp only [tab, ClauseProgram.emit_forDown, ClauseProgram.emit_clause, List.flatMap_cons,
      List.flatMap_nil, List.append_nil]
    unfold rowOf
    apply flatMap_congr_range
    intro v _
    simp only [NumExpr.eval]
    apply flatMap_congr_range
    intro s hs
    exact bitProg_emit lits input env hs
  | seq a b iha ihb =>
    intro Wk env
    simp only [tab, ClauseProgram.emit_seq, List.flatMap_append, iha, ihb]
  | forDown bound body ih =>
    intro Wk env
    simp only [tab, ClauseProgram.emit_forDown, ih, NumExpr.eval_lift, List.flatMap_assoc]
  | ifLe l r y n ihy ihn =>
    intro Wk env
    simp only [tab, ClauseProgram.emit]
    split
    · exact ihy Wk env
    · exact ihn Wk env
  | ifInput i e z o ihe ihz iho =>
    intro Wk env
    simp only [tab, ClauseProgram.emit]
    split
    · exact ihe Wk env
    · exact ihz Wk env
    · exact iho Wk env

/-! ## The first stage -/

/-- The first stage: `A n` empty clauses, then the table of the formula emitted by `P`. -/
def stage1 (P : ClauseProgram 1) : ClauseProgram 1 :=
  .seq (.forDown (Ax P) (.clause [])) (tab (Wx P) P)

theorem flatMap_const_singleton {α β : Type} (L : List α) (b : β) :
    L.flatMap (fun _ => [b]) = List.replicate L.length b := by
  induction L with
  | nil => rfl
  | cons a L ih => simp [ih, List.replicate_succ]

theorem stage1_emit (P : ClauseProgram 1) (input : Word) (env : Env 1) :
    (stage1 P).emit input env =
      List.replicate ((Ax P).eval env) [] ++
        ((P.emit input env).flatMap (rowBits ((Wx P).eval env))).map unitOf := by
  unfold stage1
  simp only [ClauseProgram.emit_seq, ClauseProgram.emit_forDown, ClauseProgram.emit_clause,
    List.map_nil, tab_emit, flatMap_const_singleton, List.length_reverse, List.length_range]
  congr 1
  rw [List.map_flatMap]
  congr 1
  funext c
  exact rowOf_eq _ c

/-! ## Positions of the bits in the code -/

theorem writeNat_eq (N : Nat) : writeNat N = List.replicate N true ++ [false] := by
  induction N with
  | zero => rfl
  | succ N ih => simp [writeNat, ih, List.replicate_succ]

theorem writeValues_append {α : Type} (enc : α → Word) (l1 l2 : List α) :
    writeValues enc (l1 ++ l2) = writeValues enc l1 ++ writeValues enc l2 := by
  induction l1 with
  | nil => rfl
  | cons a l ih => simp [writeValues, ih, List.append_assoc]

theorem writeValues_empty (A : Nat) :
    writeValues encodeClause (List.replicate A ([] : Clause)) = List.replicate A false := by
  induction A with
  | zero => rfl
  | succ A ih =>
    rw [List.replicate_succ, List.replicate_succ, writeValues, ih]
    rfl

/-- The code of a unit clause. -/
def unitCode (b : Bool) : Word := [true, false, b, false]

theorem writeValues_units (bits : List Bool) :
    writeValues encodeClause (bits.map unitOf) = bits.flatMap unitCode := by
  induction bits with
  | nil => rfl
  | cons b bs ih =>
    simp only [List.map_cons, writeValues, ih, List.flatMap_cons]
    rfl

theorem encode_table (A : Nat) (bits : List Bool) :
    encode (List.replicate A [] ++ bits.map unitOf) =
      List.replicate (A + bits.length) true ++ [false] ++ List.replicate A false ++
        bits.flatMap unitCode := by
  unfold encode writeList
  rw [writeNat_eq, writeValues_append, writeValues_empty, writeValues_units]
  simp [List.append_assoc]

theorem getElem?_flatMap_const {α β : Type} (L : List α) (g : α → List β) (k : Nat)
    (hg : ∀ a, (g a).length = k) :
    ∀ u i, (hu : u < L.length) → i < k → (L.flatMap g)[k * u + i]? = (g L[u])[i]? := by
  induction L with
  | nil => intro u i hu; simp at hu
  | cons a L ih =>
    intro u i hu hi
    cases u with
    | zero =>
      simp only [List.flatMap_cons, Nat.mul_zero, Nat.zero_add, List.getElem_cons_zero]
      rw [List.getElem?_append_left (by rw [hg]; omega)]
    | succ u =>
      simp only [List.flatMap_cons, List.getElem_cons_succ]
      rw [List.getElem?_append_right (by rw [hg]; rw [Nat.mul_succ]; omega), hg,
        show k * (u + 1) + i - k = k * u + i by rw [Nat.mul_succ]; omega]
      exact ih u i (by simp at hu; omega) hi

theorem length_flatMap_const {α β : Type} (L : List α) (g : α → List β) (k : Nat)
    (hg : ∀ a, (g a).length = k) : (L.flatMap g).length = L.length * k := by
  induction L with
  | nil => simp
  | cons a L ih => simp only [List.flatMap_cons, List.length_append, hg, ih, List.length_cons]; rw [Nat.succ_mul]; omega

theorem rowBits_length (W : Nat) (c : Clause) : (rowBits W c).length = 2 * W := by
  unfold rowBits
  rw [length_flatMap_const _ _ 2 (fun _ => rfl)]
  simp [Nat.mul_comm]

theorem rowBits_get (W : Nat) (c : Clause) {v s : Nat} (hv : v < W) (hs : s < 2) :
    (rowBits W c)[2 * (W - 1 - v) + (1 - s)]? = some (bitB c v s) := by
  unfold rowBits
  rw [getElem?_flatMap_const _ _ 2 (fun _ => rfl) (W - 1 - v) (1 - s) (by simp; omega)
    (by omega)]
  have : (List.range W).reverse[W - 1 - v]'(by simp; omega) = v := by
    rw [List.getElem_reverse]; simp; omega
  rw [this]
  rcases (show s = 0 ∨ s = 1 by omega) with rfl | rfl <;> rfl

/-- The position of the bit of clause `j`, variable `v`, sign `s` in the code of the table with
padding `A`, `M` rows and row width `R = 2 W`. -/
def posN (A M R W j v s : Nat) : Nat :=
  2 * A + M * R + 3 + 4 * (j * R + (2 * (W - 1 - v) + (1 - s)))

theorem table_bit (A W : Nat) (φ : CNF) {j v s : Nat} (hj : j < φ.length) (hv : v < W)
    (hs : s < 2) :
    (encode (List.replicate A [] ++ (φ.flatMap (rowBits W)).map unitOf))[
      posN A φ.length (2 * W) W j v s]? = some (bitB φ[j] v s) := by
  have hlen : (φ.flatMap (rowBits W)).length = φ.length * (2 * W) :=
    length_flatMap_const _ _ _ (rowBits_length W)
  rw [encode_table]
  have hq : j * (2 * W) + (2 * (W - 1 - v) + (1 - s)) < φ.length * (2 * W) := by
    have : (j + 1) * (2 * W) ≤ φ.length * (2 * W) := Nat.mul_le_mul_right _ hj
    rw [Nat.succ_mul] at this
    omega
  have e1 : posN A φ.length (2 * W) W j v s =
      (A + (φ.flatMap (rowBits W)).length + 1 + A) +
        (4 * (j * (2 * W) + (2 * (W - 1 - v) + (1 - s))) + 2) := by
    unfold posN; rw [hlen]; omega
  rw [e1, List.getElem?_append_right (by
      simp only [List.length_append, List.length_replicate, List.length_singleton]; omega),
    List.length_append, List.length_append,
    List.length_replicate, List.length_replicate, List.length_singleton, Nat.add_sub_cancel_left]
  rw [getElem?_flatMap_const _ unitCode 4 (fun _ => rfl) _ 2 (by omega) (by omega)]
  have e2 : (φ.flatMap (rowBits W))[j * (2 * W) + (2 * (W - 1 - v) + (1 - s))]'(by omega) =
      bitB φ[j] v s := by
    have := getElem?_flatMap_const φ (rowBits W) (2 * W) (rowBits_length W) j
      (2 * (W - 1 - v) + (1 - s)) hj (by omega)
    rw [rowBits_get W φ[j] hv hs, Nat.mul_comm] at this
    rw [List.getElem?_eq_getElem (by omega)] at this
    exact Option.some.inj this
  rw [e2]
  rfl

theorem table_length (A W : Nat) (φ : CNF) :
    (encode (List.replicate A [] ++ (φ.flatMap (rowBits W)).map unitOf)).length =
      2 * A + 1 + 5 * (φ.length * (2 * W)) := by
  have hlen : (φ.flatMap (rowBits W)).length = φ.length * (2 * W) :=
    length_flatMap_const _ _ _ (rowBits_length W)
  rw [encode_table]
  simp only [List.length_append, List.length_replicate, List.length_singleton, hlen]
  rw [length_flatMap_const _ unitCode 4 (fun _ => rfl), hlen]
  omega

end Complexity.Planar.Emit
