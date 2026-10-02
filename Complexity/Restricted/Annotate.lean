module

public import Complexity.Restricted.Copies
public import Complexity.CookLevinEmitter
import Lean.Elab.Tactic.Omega

/-!
# Static measures and annotated emission of clause programs

For a first-order clause program (`StackTableauEmitter.ClauseProgram`) this file defines

* its literal positions (`width`, `signs`): every literal of every `clause` node of the
  program text gets a position, numbered in program order;
* its loop depth (`depth`);
* syntactic upper bounds, as numeric expressions in the input length, for all loop bounds
  (`loopSum`) and all emitted variable indices (`varSum`);
* the *annotated emission* `annot`, which lists every emitted clause together with the
  position of its first literal and a *slot* computed from the loop indices.

The main results say that the annotated emission is a well-formed entry list in the sense
of `Complexity.Restricted.WF`: different emitted clauses own different position–slot pairs.
-/

@[expose] public section

namespace Complexity.Restricted

open Complexity.SAT StackTableauEmitter

/-- The number of literal positions of a program. -/
def width : {n : Nat} → ClauseProgram n → Nat
  | _, .clause lits => lits.length
  | _, .seq a b => width a + width b
  | _, .forDown _ body => width body
  | _, .ifLe _ _ y no => width y + width no
  | _, .ifInput _ e z o => width e + width z + width o

/-- The signs of the literals at all positions of a program. -/
def signs : {n : Nat} → ClauseProgram n → List Bool
  | _, .clause lits => lits.map (·.positive)
  | _, .seq a b => signs a ++ signs b
  | _, .forDown _ body => signs body
  | _, .ifLe _ _ y no => signs y ++ signs no
  | _, .ifInput _ e z o => signs e ++ signs z ++ signs o

theorem signs_length : ∀ {n : Nat} (P : ClauseProgram n), (signs P).length = width P
  | _, .clause lits => by simp [signs, width]
  | _, .seq a b => by simp [signs, width, signs_length a, signs_length b]
  | _, .forDown _ body => by simp [signs, width, signs_length body]
  | _, .ifLe _ _ y no => by simp [signs, width, signs_length y, signs_length no]
  | _, .ifInput _ e z o => by
      simp [signs, width, signs_length e, signs_length z, signs_length o, Nat.add_assoc]

/-- The nesting depth of loops. -/
def depth : {n : Nat} → ClauseProgram n → Nat
  | _, .clause _ => 0
  | _, .seq a b => max (depth a) (depth b)
  | _, .forDown _ body => depth body + 1
  | _, .ifLe _ _ y no => max (depth y) (depth no)
  | _, .ifInput _ e z o => max (max (depth e) (depth z)) (depth o)

/-! ### Upper-bound expressions -/

/-- An expression in the input length bounding `e`, given bounds `ctx` for the variables. -/
def ub {n : Nat} (ctx : Fin n → NumExpr 1) : NumExpr n → NumExpr 1
  | .var i => ctx i
  | .const c => .const c
  | .add a b => .add (ub ctx a) (ub ctx b)
  | .mul a b => .mul (ub ctx a) (ub ctx b)
  | .sub a _ => ub ctx a
  | .pred a => ub ctx a

def extendCtx {n : Nat} (u : NumExpr 1) (ctx : Fin n → NumExpr 1) : Fin (n + 1) → NumExpr 1 :=
  Fin.cases u ctx

/-- The variables of `env` are bounded by the expressions `ctx`. -/
def CtxOK {n : Nat} (ctx : Fin n → NumExpr 1) (env : Env n) (env0 : Env 1) : Prop :=
  ∀ i, env i ≤ (ctx i).eval env0

theorem eval_le_ub {n : Nat} {ctx : Fin n → NumExpr 1} {env : Env n} {env0 : Env 1}
    (h : CtxOK ctx env env0) : ∀ e : NumExpr n, e.eval env ≤ (ub ctx e).eval env0
  | .var i => h i
  | .const c => Nat.le_refl c
  | .add a b => Nat.add_le_add (eval_le_ub h a) (eval_le_ub h b)
  | .mul a b => Nat.mul_le_mul (eval_le_ub h a) (eval_le_ub h b)
  | .sub a _ => Nat.le_trans (Nat.sub_le _ _) (eval_le_ub h a)
  | .pred a => Nat.le_trans (Nat.sub_le _ _) (eval_le_ub h a)

theorem CtxOK.extend {n : Nat} {ctx : Fin n → NumExpr 1} {env : Env n} {env0 : Env 1}
    (h : CtxOK ctx env env0) {u : NumExpr 1} {i : Nat} (hi : i ≤ u.eval env0) :
    CtxOK (extendCtx u ctx) (StackTableauEmitter.extend i env) env0 := by
  intro j
  refine Fin.cases ?_ ?_ j
  · exact hi
  · intro k
    exact h k

def sumExpr : List (NumExpr 1) → NumExpr 1
  | [] => .const 0
  | e :: es => .add e (sumExpr es)

theorem le_sumExpr (env0 : Env 1) : ∀ (es : List (NumExpr 1)), ∀ e ∈ es,
    e.eval env0 ≤ (sumExpr es).eval env0
  | [], e, he => by simp at he
  | x :: xs, e, he => by
    rcases List.mem_cons.mp he with h | h
    · subst h; simp only [sumExpr, NumExpr.eval]; omega
    · have := le_sumExpr env0 xs e h
      simp only [sumExpr, NumExpr.eval]; omega

/-- A bound for the sum of all loop bounds of a program. -/
def loopSum : {n : Nat} → (Fin n → NumExpr 1) → ClauseProgram n → NumExpr 1
  | _, _, .clause _ => .const 0
  | _, ctx, .seq a b => .add (loopSum ctx a) (loopSum ctx b)
  | _, ctx, .forDown bound body =>
      .add (ub ctx bound) (loopSum (extendCtx (ub ctx bound) ctx) body)
  | _, ctx, .ifLe _ _ y no => .add (loopSum ctx y) (loopSum ctx no)
  | _, ctx, .ifInput _ e z o => .add (.add (loopSum ctx e) (loopSum ctx z)) (loopSum ctx o)

/-- A bound for all variable indices emitted by a program. -/
def varSum : {n : Nat} → (Fin n → NumExpr 1) → ClauseProgram n → NumExpr 1
  | _, ctx, .clause lits => sumExpr (lits.map (fun l => ub ctx l.index))
  | _, ctx, .seq a b => .add (varSum ctx a) (varSum ctx b)
  | _, ctx, .forDown bound body => varSum (extendCtx (ub ctx bound) ctx) body
  | _, ctx, .ifLe _ _ y no => .add (varSum ctx y) (varSum ctx no)
  | _, ctx, .ifInput _ e z o => .add (.add (varSum ctx e) (varSum ctx z)) (varSum ctx o)

/-! ### Annotated emission -/

/-- The emitted clauses with the position of their first literal and their slot. The slot of
a clause at loop depth `d` with accumulated loop index `acc` is `acc * B ^ (D - d)`. -/
def annot (B D : Nat) (input : Word) :
    {n : Nat} → ClauseProgram n → Env n → Nat → Nat → Nat → List Entry
  | _, .clause lits, env, off, d, acc => [(off, acc * B ^ (D - d), lits.map (fun l => l.eval env))]
  | _, .seq a b, env, off, d, acc =>
      annot B D input a env off d acc ++ annot B D input b env (off + width a) d acc
  | _, .forDown bound body, env, off, d, acc =>
      (List.range (bound.eval env)).reverse.flatMap (fun i =>
        annot B D input body (StackTableauEmitter.extend i env) off (d + 1) (acc * B + i))
  | _, .ifLe l r y no, env, off, d, acc =>
      if l.eval env ≤ r.eval env then annot B D input y env off d acc
      else annot B D input no env (off + width y) d acc
  | _, .ifInput idx e z o, env, off, d, acc =>
      match input[idx.eval env]? with
      | none => annot B D input e env off d acc
      | some false => annot B D input z env (off + width e) d acc
      | some true => annot B D input o env (off + width e + width z) d acc

theorem annot_map (B D : Nat) (input : Word) :
    ∀ {n : Nat} (P : ClauseProgram n) (env : Env n) (off d acc : Nat),
      (annot B D input P env off d acc).map (fun e => e.2.2) = P.emit input env
  | _, .clause lits, env, off, d, acc => rfl
  | _, .seq a b, env, off, d, acc => by
      simp [annot, ClauseProgram.emit, annot_map B D input a, annot_map B D input b]
  | _, .forDown bound body, env, off, d, acc => by
      simp only [annot, ClauseProgram.emit, List.map_flatMap]
      congr 1
      funext i
      exact annot_map B D input body _ _ _ _
  | _, .ifLe l r y no, env, off, d, acc => by
      simp only [annot, ClauseProgram.emit]
      split
      · exact annot_map B D input y _ _ _ _
      · exact annot_map B D input no _ _ _ _
  | _, .ifInput idx e z o, env, off, d, acc => by
      simp only [annot, ClauseProgram.emit]
      cases input[idx.eval env]? with
      | none => exact annot_map B D input e _ _ _ _
      | some b =>
        cases b
        · exact annot_map B D input z _ _ _ _
        · exact annot_map B D input o _ _ _ _

/-- Positions of entries lie in the range of the subprogram. -/
theorem annot_pos (B D : Nat) (input : Word) :
    ∀ {n : Nat} (P : ClauseProgram n) (env : Env n) (off d acc : Nat),
      ∀ e ∈ annot B D input P env off d acc, off ≤ e.1 ∧ e.1 + e.2.2.length ≤ off + width P
  | _, .clause lits, env, off, d, acc => by
      intro e he
      simp [annot] at he
      subst he
      simp [width]
  | _, .seq a b, env, off, d, acc => by
      intro e he
      simp only [annot, List.mem_append] at he
      rcases he with he | he
      · have := annot_pos B D input a env off d acc e he
        simp only [width]; omega
      · have := annot_pos B D input b env (off + width a) d acc e he
        simp only [width]; omega
  | _, .forDown bound body, env, off, d, acc => by
      intro e he
      simp only [annot, List.mem_flatMap] at he
      obtain ⟨i, _, he⟩ := he
      exact annot_pos B D input body _ off (d + 1) _ e he
  | _, .ifLe l r y no, env, off, d, acc => by
      intro e he
      simp only [annot] at he
      split at he
      · have := annot_pos B D input y env off d acc e he
        simp only [width]; omega
      · have := annot_pos B D input no env (off + width y) d acc e he
        simp only [width]; omega
  | _, .ifInput idx e z o, env, off, d, acc => by
      intro x hx
      simp only [annot] at hx
      split at hx
      · have := annot_pos B D input e env off d acc x hx
        simp only [width]; omega
      · have := annot_pos B D input z env (off + width e) d acc x hx
        simp only [width]; omega
      · have := annot_pos B D input o env (off + width e + width z) d acc x hx
        simp only [width]; omega

theorem slot_step {B W acc i : Nat} (hi : i < B) :
    acc * (B * W) ≤ (acc * B + i) * W ∧ (acc * B + i + 1) * W ≤ (acc + 1) * (B * W) := by
  constructor
  · rw [← Nat.mul_assoc]
    exact Nat.mul_le_mul_right W (Nat.le_add_right _ _)
  · rw [← Nat.mul_assoc]
    apply Nat.mul_le_mul_right W
    rw [Nat.add_mul, Nat.one_mul]
    omega

/-- Slots of entries lie in the interval of the accumulated loop index. -/
theorem annot_slot (B D : Nat) (input : Word) (env0 : Env 1) :
    ∀ {n : Nat} (P : ClauseProgram n) (ctx : Fin n → NumExpr 1) (env : Env n) (off d acc : Nat),
      0 < B → CtxOK ctx env env0 → (loopSum ctx P).eval env0 ≤ B → d + depth P ≤ D →
      ∀ e ∈ annot B D input P env off d acc,
        acc * B ^ (D - d) ≤ e.2.1 ∧ e.2.1 < (acc + 1) * B ^ (D - d)
  | _, .clause lits, ctx, env, off, d, acc, hB0, _, hB, hD => by
      intro e he
      simp [annot] at he
      subst he
      simp only
      have : 0 < B ^ (D - d) := Nat.pow_pos hB0
      constructor
      · exact Nat.le_refl _
      · rw [Nat.add_mul, Nat.one_mul]
        omega
  | _, .seq a b, ctx, env, off, d, acc, hB0, hc, hB, hD => by
      intro e he
      simp only [loopSum, NumExpr.eval, depth] at hB hD
      simp only [annot, List.mem_append] at he
      rcases he with he | he
      · exact annot_slot B D input env0 a ctx env off d acc hB0 hc (by omega) (by omega) e he
      · exact annot_slot B D input env0 b ctx env _ d acc hB0 hc (by omega) (by omega) e he
  | _, .forDown bound body, ctx, env, off, d, acc, hB0, hc, hB, hD => by
      intro e he
      simp only [loopSum, NumExpr.eval, depth] at hB hD
      simp only [annot, List.mem_flatMap, List.mem_reverse, List.mem_range] at he
      obtain ⟨i, hi, he⟩ := he
      have hib := eval_le_ub hc bound
      have hiB : i < B := by omega
      have hc' := hc.extend (u := ub ctx bound) (i := i) (by omega)
      have := annot_slot B D input env0 body _ _ off (d + 1) (acc * B + i) hB0 hc' (by omega)
        (by omega) e he
      have hpow : B ^ (D - d) = B * B ^ (D - (d + 1)) := by
        rw [show D - d = D - (d + 1) + 1 by omega, Nat.pow_succ, Nat.mul_comm]
      rw [hpow]
      have hs := slot_step (W := B ^ (D - (d + 1))) (acc := acc) hiB
      omega
  | _, .ifLe l r y no, ctx, env, off, d, acc, hB0, hc, hB, hD => by
      intro e he
      simp only [loopSum, NumExpr.eval, depth] at hB hD
      simp only [annot] at he
      split at he
      · exact annot_slot B D input env0 y ctx env off d acc hB0 hc (by omega) (by omega) e he
      · exact annot_slot B D input env0 no ctx env _ d acc hB0 hc (by omega) (by omega) e he
  | _, .ifInput idx e z o, ctx, env, off, d, acc, hB0, hc, hB, hD => by
      intro x hx
      simp only [loopSum, NumExpr.eval, depth] at hB hD
      simp only [annot] at hx
      split at hx
      · exact annot_slot B D input env0 e ctx env off d acc hB0 hc (by omega) (by omega) x hx
      · exact annot_slot B D input env0 z ctx env _ d acc hB0 hc (by omega) (by omega) x hx
      · exact annot_slot B D input env0 o ctx env _ d acc hB0 hc (by omega) (by omega) x hx



/-- Variables of entries are bounded by `varSum`. -/
theorem annot_var (B D : Nat) (input : Word) (env0 : Env 1) :
    ∀ {n : Nat} (P : ClauseProgram n) (ctx : Fin n → NumExpr 1) (env : Env n) (off d acc : Nat),
      CtxOK ctx env env0 →
      ∀ e ∈ annot B D input P env off d acc, ∀ l ∈ e.2.2, l.var ≤ (varSum ctx P).eval env0
  | _, .clause lits, ctx, env, off, d, acc, hc => by
      intro e he l hl
      simp [annot] at he
      subst he
      simp only [List.mem_map] at hl
      obtain ⟨x, hx, rfl⟩ := hl
      simp only [varSum, LiteralExpr.eval]
      exact Nat.le_trans (eval_le_ub hc x.index)
        (le_sumExpr env0 _ _ (List.mem_map.mpr ⟨x, hx, rfl⟩))
  | _, .seq a b, ctx, env, off, d, acc, hc => by
      intro e he l hl
      simp only [varSum, NumExpr.eval]
      simp only [annot, List.mem_append] at he
      rcases he with he | he
      · have := annot_var B D input env0 a ctx env off d acc hc e he l hl; omega
      · have := annot_var B D input env0 b ctx env _ d acc hc e he l hl; omega
  | _, .forDown bound body, ctx, env, off, d, acc, hc => by
      intro e he l hl
      simp only [varSum]
      simp only [annot, List.mem_flatMap, List.mem_reverse, List.mem_range] at he
      obtain ⟨i, hi, he⟩ := he
      have hib := eval_le_ub hc bound
      exact annot_var B D input env0 body _ _ off (d + 1) _ (hc.extend (by omega)) e he l hl
  | _, .ifLe lft rgt y no, ctx, env, off, d, acc, hc => by
      intro e he l hl
      simp only [varSum, NumExpr.eval]
      simp only [annot] at he
      split at he
      · have := annot_var B D input env0 y ctx env off d acc hc e he l hl; omega
      · have := annot_var B D input env0 no ctx env _ d acc hc e he l hl; omega
  | _, .ifInput idx e z o, ctx, env, off, d, acc, hc => by
      intro x hx l hl
      simp only [varSum, NumExpr.eval]
      simp only [annot] at hx
      split at hx
      · have := annot_var B D input env0 e ctx env off d acc hc x hx l hl; omega
      · have := annot_var B D input env0 z ctx env _ d acc hc x hx l hl; omega
      · have := annot_var B D input env0 o ctx env _ d acc hc x hx l hl; omega

theorem getD_append_left {l₁ l₂ : List Bool} {i : Nat} (h : i < l₁.length) :
    (l₁ ++ l₂).getD i false = l₁.getD i false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_append_right {l₁ l₂ : List Bool} (i : Nat) :
    (l₁ ++ l₂).getD (l₁.length + i) false = l₂.getD i false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right]

theorem signsFrom_map {n : Nat} (σ : Nat → Bool) (env : Env n) :
    ∀ (lits : List (LiteralExpr n)) (p : Nat),
      (∀ i, i < lits.length → σ (p + i) = (lits.map (·.positive)).getD i false) →
      SignsFrom σ p (lits.map (fun l => l.eval env))
  | [], _, _ => trivial
  | l :: ls, p, h => by
      refine ⟨?_, ?_⟩
      · have := h 0 (by simp)
        simpa [LiteralExpr.eval] using this.symm
      · apply signsFrom_map σ env ls (p + 1)
        intro i hi
        have := h (i + 1) (by simp; omega)
        simpa [Nat.add_assoc, Nat.add_comm 1 i] using this

/-- Signs of entries agree with the static signs of the program. -/
theorem annot_sign (B D : Nat) (input : Word) (σ : Nat → Bool) :
    ∀ {n : Nat} (P : ClauseProgram n) (env : Env n) (off d acc : Nat),
      (∀ i, i < width P → σ (off + i) = (signs P).getD i false) →
      ∀ e ∈ annot B D input P env off d acc, SignsFrom σ e.1 e.2.2
  | _, .clause lits, env, off, d, acc, hσ => by
      intro e he
      simp [annot] at he
      subst he
      exact signsFrom_map σ env lits off hσ
  | _, .seq a b, env, off, d, acc, hσ => by
      intro e he
      simp only [annot, List.mem_append] at he
      rcases he with he | he
      · apply annot_sign B D input σ a env off d acc _ e he
        intro i hi
        rw [hσ i (by simp only [width]; omega), signs,
          getD_append_left (by rw [signs_length]; exact hi)]
      · apply annot_sign B D input σ b env _ d acc _ e he
        intro i hi
        have := hσ (width a + i) (by simp only [width]; omega)
        rw [Nat.add_assoc, this, signs, ← signs_length a, getD_append_right]
  | _, .forDown bound body, env, off, d, acc, hσ => by
      intro e he
      simp only [annot, List.mem_flatMap] at he
      obtain ⟨i, _, he⟩ := he
      exact annot_sign B D input σ body _ off (d + 1) _ hσ e he
  | _, .ifLe lft rgt y no, env, off, d, acc, hσ => by
      intro e he
      simp only [annot] at he
      split at he
      · apply annot_sign B D input σ y env off d acc _ e he
        intro i hi
        rw [hσ i (by simp only [width]; omega), signs,
          getD_append_left (by rw [signs_length]; exact hi)]
      · apply annot_sign B D input σ no env _ d acc _ e he
        intro i hi
        have := hσ (width y + i) (by simp only [width]; omega)
        rw [Nat.add_assoc, this, signs, ← signs_length y, getD_append_right]
  | _, .ifInput idx e z o, env, off, d, acc, hσ => by
      intro x hx
      simp only [annot] at hx
      split at hx
      · apply annot_sign B D input σ e env off d acc _ x hx
        intro i hi
        rw [hσ i (by simp only [width]; omega), signs, List.append_assoc,
          getD_append_left (by rw [signs_length]; exact hi)]
      · apply annot_sign B D input σ z env _ d acc _ x hx
        intro i hi
        have := hσ (width e + i) (by simp only [width]; omega)
        rw [Nat.add_assoc, this, signs, List.append_assoc, ← signs_length e, getD_append_right,
          getD_append_left (by rw [signs_length]; exact hi)]
      · apply annot_sign B D input σ o env _ d acc _ x hx
        intro i hi
        have := hσ (width e + width z + i) (by simp only [width]; omega)
        rw [show off + width e + width z + i = off + (width e + width z + i) by omega, this, signs,
          List.append_assoc, ← signs_length e, Nat.add_assoc, getD_append_right, ← signs_length z,
          getD_append_right]

theorem sum_zero_of_forall {l : List Nat} (f : Nat → Nat) (h : ∀ i ∈ l, f i = 0) :
    (l.map f).sum = 0 := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [h x (by simp), ih (fun i hi => h i (by simp [hi]))]

theorem sum_map_le_one {l : List Nat} (hl : l.Nodup) (f : Nat → Nat) (h1 : ∀ i ∈ l, f i ≤ 1)
    (h2 : ∀ i ∈ l, ∀ j ∈ l, 0 < f i → 0 < f j → i = j) : (l.map f).sum ≤ 1 := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons]
    have hx := List.nodup_cons.mp hl
    by_cases hfx : f x = 0
    · rw [hfx, Nat.zero_add]
      exact ih hx.2 (fun i hi => h1 i (by simp [hi]))
        (fun i hi j hj => h2 i (by simp [hi]) j (by simp [hj]))
    · have hzero : (xs.map f).sum = 0 := by
        apply sum_zero_of_forall
        intro i hi
        by_cases hfi : f i = 0
        · exact hfi
        · exfalso
          have := h2 x (by simp) i (by simp [hi]) (by omega) (by omega)
          subst this
          exact hx.1 hi
      rw [hzero]
      have := h1 x (by simp)
      omega

theorem nodup_reverse_of {l : List Nat} (h : l.Nodup) : l.reverse.Nodup := by
  unfold List.Nodup at *
  rw [List.pairwise_reverse]
  exact h.imp (fun hab => Ne.symm hab)

theorem interval_unique {x y W r : Nat} (hx : x * W ≤ r ∧ r < (x + 1) * W)
    (hy : y * W ≤ r ∧ r < (y + 1) * W) : x = y := by
  rcases Nat.lt_trichotomy x y with h | h | h
  · have := Nat.mul_le_mul_right W (show x + 1 ≤ y by omega)
    omega
  · exact h
  · have := Nat.mul_le_mul_right W (show y + 1 ≤ x by omega)
    omega

theorem owns_spec {p r : Nat} {e : Entry} (h : owns p r e = true) :
    e.1 ≤ p ∧ p < e.1 + e.2.2.length ∧ e.2.1 = r := by
  simpa [owns] using h

/-- Different entries own different position–slot pairs. -/
theorem annot_unique (B D : Nat) (input : Word) (env0 : Env 1) (p r : Nat) :
    ∀ {n : Nat} (P : ClauseProgram n) (ctx : Fin n → NumExpr 1) (env : Env n) (off d acc : Nat),
      0 < B → CtxOK ctx env env0 → (loopSum ctx P).eval env0 ≤ B → d + depth P ≤ D →
      (annot B D input P env off d acc).countP (owns p r) ≤ 1
  | _, .clause lits, ctx, env, off, d, acc, _, _, _, _ => by
      simp only [annot]
      exact Nat.le_trans List.countP_le_length (by simp)
  | _, .seq a b, ctx, env, off, d, acc, hB0, hc, hB, hD => by
      simp only [loopSum, NumExpr.eval, depth] at hB hD
      simp only [annot, List.countP_append]
      have ha := annot_unique B D input env0 p r a ctx env off d acc hB0 hc (by omega) (by omega)
      have hb := annot_unique B D input env0 p r b ctx env (off + width a) d acc hB0 hc
        (by omega) (by omega)
      by_cases hca : (annot B D input a env off d acc).countP (owns p r) = 0
      · omega
      · by_cases hcb : (annot B D input b env (off + width a) d acc).countP (owns p r) = 0
        · omega
        · exfalso
          obtain ⟨e, he, hoe⟩ := List.countP_pos_iff.mp (Nat.pos_of_ne_zero hca)
          obtain ⟨e', he', hoe'⟩ := List.countP_pos_iff.mp (Nat.pos_of_ne_zero hcb)
          have h1 := annot_pos B D input a env off d acc e he
          have h2 := annot_pos B D input b env (off + width a) d acc e' he'
          have h3 := owns_spec hoe
          have h4 := owns_spec hoe'
          omega
  | _, .forDown bound body, ctx, env, off, d, acc, hB0, hc, hB, hD => by
      simp only [loopSum, NumExpr.eval, depth] at hB hD
      have hib := eval_le_ub hc bound
      simp only [annot, List.countP_flatMap]
      apply sum_map_le_one (nodup_reverse_of List.nodup_range)
      · intro i hi
        simp only [List.mem_reverse, List.mem_range] at hi
        exact annot_unique B D input env0 p r body _ _ off (d + 1) _ hB0
          (hc.extend (u := ub ctx bound) (by omega)) (by omega) (by omega)
      · intro i hi j hj hfi hfj
        simp only [List.mem_reverse, List.mem_range] at hi hj
        simp only [Function.comp] at hfi hfj
        obtain ⟨e, he, hoe⟩ := List.countP_pos_iff.mp hfi
        obtain ⟨e', he', hoe'⟩ := List.countP_pos_iff.mp hfj
        have hsi := annot_slot B D input env0 body _ _ off (d + 1) (acc * B + i) hB0
          (hc.extend (u := ub ctx bound) (by omega)) (by omega) (by omega) e he
        have hsj := annot_slot B D input env0 body _ _ off (d + 1) (acc * B + j) hB0
          (hc.extend (u := ub ctx bound) (by omega)) (by omega) (by omega) e' he'
        have h3 := owns_spec hoe
        have h4 := owns_spec hoe'
        rw [h3.2.2] at hsi
        rw [h4.2.2] at hsj
        have := interval_unique hsi hsj
        omega
  | _, .ifLe lft rgt y no, ctx, env, off, d, acc, hB0, hc, hB, hD => by
      simp only [loopSum, NumExpr.eval, depth] at hB hD
      simp only [annot]
      split
      · exact annot_unique B D input env0 p r y ctx env off d acc hB0 hc (by omega) (by omega)
      · exact annot_unique B D input env0 p r no ctx env _ d acc hB0 hc (by omega) (by omega)
  | _, .ifInput idx e z o, ctx, env, off, d, acc, hB0, hc, hB, hD => by
      simp only [loopSum, NumExpr.eval, depth] at hB hD
      simp only [annot]
      split
      · exact annot_unique B D input env0 p r e ctx env off d acc hB0 hc (by omega) (by omega)
      · exact annot_unique B D input env0 p r z ctx env _ d acc hB0 hc (by omega) (by omega)
      · exact annot_unique B D input env0 p r o ctx env _ d acc hB0 hc (by omega) (by omega)

/-! ### The annotated emission of a whole program -/

def ctx0 : Fin 1 → NumExpr 1 := fun _ => .var 0

/-- Loop indices are below `loopBound P input`. -/
def loopBound (P : ClauseProgram 1) (input : Word) : Nat :=
  (loopSum ctx0 P).eval (CookLevinEmitter.inputEnv input) + 2

def slotCount (P : ClauseProgram 1) (input : Word) : Nat :=
  loopBound P input ^ (depth P + 1)

def varCount (P : ClauseProgram 1) (input : Word) : Nat :=
  (varSum ctx0 P).eval (CookLevinEmitter.inputEnv input) + 1

def signAt (P : ClauseProgram 1) (p : Nat) : Bool := (signs P).getD p false

def entries (P : ClauseProgram 1) (input : Word) : List Entry :=
  annot (loopBound P input) (depth P + 1) input P (CookLevinEmitter.inputEnv input) 0 0 0

theorem entries_map (P : ClauseProgram 1) (input : Word) :
    (entries P input).map (fun e => e.2.2) = P.emit input (CookLevinEmitter.inputEnv input) :=
  annot_map _ _ _ _ _ _ _ _

theorem ctx0_ok (input : Word) :
    CtxOK ctx0 (CookLevinEmitter.inputEnv input) (CookLevinEmitter.inputEnv input) := by
  intro i
  simp [ctx0, NumExpr.eval, CookLevinEmitter.inputEnv]

theorem two_le_slotCount (P : ClauseProgram 1) (input : Word) : 2 ≤ slotCount P input := by
  unfold slotCount loopBound
  rw [Nat.pow_succ]
  have h1 : 1 ≤ ((loopSum ctx0 P).eval (CookLevinEmitter.inputEnv input) + 2) ^ depth P :=
    Nat.pow_pos (by omega)
  have := Nat.mul_le_mul h1
    (show 2 ≤ (loopSum ctx0 P).eval (CookLevinEmitter.inputEnv input) + 2 by omega)
  omega

theorem entries_WF (P : ClauseProgram 1) (input : Word)
    (hlen : ∀ c ∈ P.emit input (CookLevinEmitter.inputEnv input), 2 ≤ c.length) :
    WF (width P) (slotCount P input) (varCount P input) (signAt P) (entries P input) where
  len := by
    intro e he
    apply hlen
    rw [← entries_map]
    exact List.mem_map.mpr ⟨e, he, rfl⟩
  pos := by
    intro e he
    have := annot_pos _ _ input P _ 0 0 0 e he
    omega
  slot := by
    intro e he
    have := annot_slot (loopBound P input) (depth P + 1) input (CookLevinEmitter.inputEnv input)
      P ctx0 _ 0 0 0 (by unfold loopBound; omega) (ctx0_ok input)
      (by unfold loopBound; omega) (by omega) e he
    simpa [slotCount] using this.2
  var := by
    intro e he l hl
    have := annot_var _ _ input (CookLevinEmitter.inputEnv input) P ctx0 _ 0 0 0 (ctx0_ok input)
      e he l hl
    unfold varCount
    omega
  sign := by
    intro e he
    exact annot_sign _ _ input (signAt P) P _ 0 0 0 (by intro i _; simp [signAt]) e he
  unique := by
    intro p r
    exact annot_unique (loopBound P input) (depth P + 1) input (CookLevinEmitter.inputEnv input)
      p r P ctx0 _ 0 0 0 (by unfold loopBound; omega) (ctx0_ok input)
      (by unfold loopBound; omega) (by omega)

end Complexity.Restricted
