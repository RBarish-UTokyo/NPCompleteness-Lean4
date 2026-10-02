module

public import Complexity.EmitterTools
import Lean.Elab.Tactic.Omega

/-!
# Syntactic bounds for formula emitters

For a formula emitter `P : ClauseProgram 1`, expressions in the input length `n` bounding

* every numeric expression evaluated while emitting (`ubN`): subtraction and predecessor are
  bounded by their first argument, and a loop variable by its loop bound;
* the number of emitted clauses (`countB`);
* every emitted variable, strictly (`varB`).

These bounds are built from constants, the variable, `+` and `*` only, so they are monotone in
`n`.
-/

@[expose] public section

namespace Complexity.Planar.Emit

open StackTableauEmitter SAT

/-! ## Bounds -/

/-- An upper bound for a numeric expression in terms of bounds for its variables. -/
def ubN {k : Nat} (bnd : Fin k → NumExpr 1) : NumExpr k → NumExpr 1
  | .var i => bnd i
  | .const v => .const v
  | .add a b => .add (ubN bnd a) (ubN bnd b)
  | .mul a b => .mul (ubN bnd a) (ubN bnd b)
  | .sub a _ => ubN bnd a
  | .pred a => ubN bnd a

theorem ubN_sound {k : Nat} (bnd : Fin k → NumExpr 1) (ρ : Env 1) (env : Env k)
    (h : ∀ i, env i ≤ (bnd i).eval ρ) (e : NumExpr k) : e.eval env ≤ (ubN bnd e).eval ρ := by
  induction e with
  | var i => exact h i
  | const v => exact Nat.le_refl _
  | add a b iha ihb => exact Nat.add_le_add iha ihb
  | mul a b iha ihb => exact Nat.mul_le_mul iha ihb
  | sub a b iha _ => exact Nat.le_trans (Nat.sub_le _ _) iha
  | pred a iha => exact Nat.le_trans (Nat.sub_le _ _) iha

/-- Variable bounds under a loop binder. -/
def extB {k : Nat} (b : NumExpr 1) (bnd : Fin k → NumExpr 1) : Fin (k + 1) → NumExpr 1 :=
  Fin.cases b bnd

theorem extB_sound {k : Nat} {b : NumExpr 1} {bnd : Fin k → NumExpr 1} {ρ : Env 1} {env : Env k}
    (h : ∀ i, env i ≤ (bnd i).eval ρ) {v : Nat} (hv : v ≤ b.eval ρ) :
    ∀ i, extend v env i ≤ (extB b bnd i).eval ρ := by
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact hv
  · exact h j

/-- A bound on the number of emitted clauses. -/
def countB : {k : Nat} → (Fin k → NumExpr 1) → ClauseProgram k → NumExpr 1
  | _, _, .clause _ => .const 1
  | _, bnd, .seq a b => .add (countB bnd a) (countB bnd b)
  | _, bnd, .forDown bound body =>
      .mul (ubN bnd bound) (countB (extB (ubN bnd bound) bnd) body)
  | _, bnd, .ifLe _ _ y n => .add (countB bnd y) (countB bnd n)
  | _, bnd, .ifInput _ e z o => .add (.add (countB bnd e) (countB bnd z)) (countB bnd o)

/-- A strict bound on the variables of a list of literals. -/
def litB {k : Nat} (bnd : Fin k → NumExpr 1) : List (LiteralExpr k) → NumExpr 1
  | [] => .const 0
  | l :: ls => .add (.add (ubN bnd l.index) (.const 1)) (litB bnd ls)

/-- A strict bound on the emitted variables. -/
def varB : {k : Nat} → (Fin k → NumExpr 1) → ClauseProgram k → NumExpr 1
  | _, bnd, .clause lits => litB bnd lits
  | _, bnd, .seq a b => .add (varB bnd a) (varB bnd b)
  | _, bnd, .forDown bound body => varB (extB (ubN bnd bound) bnd) body
  | _, bnd, .ifLe _ _ y n => .add (varB bnd y) (varB bnd n)
  | _, bnd, .ifInput _ e z o => .add (.add (varB bnd e) (varB bnd z)) (varB bnd o)

theorem length_flatMap_le {α β : Type} (L : List α) (F : α → List β) (c : Nat)
    (h : ∀ a ∈ L, (F a).length ≤ c) : (L.flatMap F).length ≤ L.length * c := by
  induction L with
  | nil => simp
  | cons a L ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    have h1 := h a List.mem_cons_self
    have h2 := ih (fun b hb => h b (List.mem_cons_of_mem _ hb))
    rw [Nat.succ_mul]
    omega

theorem countB_sound {k : Nat} (P : ClauseProgram k) (input : Word) (ρ : Env 1) :
    ∀ (bnd : Fin k → NumExpr 1) (env : Env k), (∀ i, env i ≤ (bnd i).eval ρ) →
      (P.emit input env).length ≤ (countB bnd P).eval ρ := by
  induction P with
  | clause lits => intro bnd env _; simp [ClauseProgram.emit, countB, NumExpr.eval]
  | seq a b iha ihb =>
    intro bnd env h
    simp only [ClauseProgram.emit, List.length_append, countB, NumExpr.eval]
    exact Nat.add_le_add (iha bnd env h) (ihb bnd env h)
  | forDown bound body ih =>
    intro bnd env h
    simp only [ClauseProgram.emit, countB, NumExpr.eval]
    have hb := ubN_sound bnd ρ env h bound
    calc ((List.range (bound.eval env)).reverse.flatMap
          (fun i => body.emit input (extend i env))).length
        ≤ (List.range (bound.eval env)).reverse.length *
            (countB (extB (ubN bnd bound) bnd) body).eval ρ := by
          apply length_flatMap_le
          intro i hi
          simp only [List.mem_reverse, List.mem_range] at hi
          exact ih _ _ (extB_sound h (by omega))
      _ ≤ _ := by
          simp only [List.length_reverse, List.length_range]
          exact Nat.mul_le_mul_right _ hb
  | ifLe l r y n ihy ihn =>
    intro bnd env h
    simp only [ClauseProgram.emit, countB, NumExpr.eval]
    split
    · exact Nat.le_trans (ihy bnd env h) (Nat.le_add_right _ _)
    · exact Nat.le_trans (ihn bnd env h) (Nat.le_add_left _ _)
  | ifInput i e z o ihe ihz iho =>
    intro bnd env h
    simp only [ClauseProgram.emit, countB, NumExpr.eval]
    split
    · have := ihe bnd env h; omega
    · have := ihz bnd env h; omega
    · have := iho bnd env h; omega

theorem litB_sound {k : Nat} (bnd : Fin k → NumExpr 1) (ρ : Env 1) (env : Env k)
    (h : ∀ i, env i ≤ (bnd i).eval ρ) (lits : List (LiteralExpr k)) :
    ∀ l ∈ lits.map (fun literal => literal.eval env), l.var < (litB bnd lits).eval ρ := by
  induction lits with
  | nil => intro l hl; simp at hl
  | cons a ls ih =>
    intro l hl
    simp only [List.map_cons, List.mem_cons] at hl
    simp only [litB, NumExpr.eval]
    rcases hl with rfl | hl
    · have := ubN_sound bnd ρ env h a.index
      simp only [LiteralExpr.eval]
      omega
    · have := ih l hl
      omega

theorem varB_sound {k : Nat} (P : ClauseProgram k) (input : Word) (ρ : Env 1) :
    ∀ (bnd : Fin k → NumExpr 1) (env : Env k), (∀ i, env i ≤ (bnd i).eval ρ) →
      ∀ c ∈ P.emit input env, ∀ l ∈ c, l.var < (varB bnd P).eval ρ := by
  induction P with
  | clause lits =>
    intro bnd env h c hc
    simp only [ClauseProgram.emit, List.mem_singleton] at hc
    subst hc
    exact litB_sound bnd ρ env h lits
  | seq a b iha ihb =>
    intro bnd env h c hc l hl
    simp only [ClauseProgram.emit, List.mem_append] at hc
    simp only [varB, NumExpr.eval]
    rcases hc with hc | hc
    · have := iha bnd env h c hc l hl; omega
    · have := ihb bnd env h c hc l hl; omega
  | forDown bound body ih =>
    intro bnd env h c hc l hl
    simp only [ClauseProgram.emit, List.mem_flatMap, List.mem_reverse, List.mem_range] at hc
    obtain ⟨i, hi, hc⟩ := hc
    have hb := ubN_sound bnd ρ env h bound
    exact ih _ _ (extB_sound h (by omega)) c hc l hl
  | ifLe lft rgt y n ihy ihn =>
    intro bnd env h c hc l hl
    simp only [ClauseProgram.emit] at hc
    simp only [varB, NumExpr.eval]
    split at hc
    · have := ihy bnd env h c hc l hl; omega
    · have := ihn bnd env h c hc l hl; omega
  | ifInput i e z o ihe ihz iho =>
    intro bnd env h c hc l hl
    simp only [ClauseProgram.emit] at hc
    simp only [varB, NumExpr.eval]
    split at hc
    · have := ihe bnd env h c hc l hl; omega
    · have := ihz bnd env h c hc l hl; omega
    · have := iho bnd env h c hc l hl; omega

/-! ## Monotonicity -/

/-- An expression in the input length that grows with it. -/
def Mono (e : NumExpr 1) : Prop := ∀ a b, a ≤ b → e.eval (fun _ => a) ≤ e.eval (fun _ => b)

theorem mono_const (v : Nat) : Mono (.const v) := fun _ _ _ => Nat.le_refl _

theorem mono_var (i : Fin 1) : Mono (.var i) := fun _ _ h => h

theorem mono_add {a b : NumExpr 1} (ha : Mono a) (hb : Mono b) : Mono (.add a b) :=
  fun x y h => Nat.add_le_add (ha x y h) (hb x y h)

theorem mono_mul {a b : NumExpr 1} (ha : Mono a) (hb : Mono b) : Mono (.mul a b) :=
  fun x y h => Nat.mul_le_mul (ha x y h) (hb x y h)

theorem mono_ubN {k : Nat} {bnd : Fin k → NumExpr 1} (hb : ∀ i, Mono (bnd i)) (e : NumExpr k) :
    Mono (ubN bnd e) := by
  induction e with
  | var i => exact hb i
  | const v => exact mono_const v
  | add a b iha ihb => exact mono_add iha ihb
  | mul a b iha ihb => exact mono_mul iha ihb
  | sub a _ iha _ => exact iha
  | pred a iha => exact iha

theorem mono_extB {k : Nat} {b : NumExpr 1} {bnd : Fin k → NumExpr 1} (hb0 : Mono b)
    (hb : ∀ i, Mono (bnd i)) : ∀ i, Mono (extB b bnd i) := by
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact hb0
  · exact hb j

theorem mono_countB {k : Nat} (P : ClauseProgram k) :
    ∀ (bnd : Fin k → NumExpr 1), (∀ i, Mono (bnd i)) → Mono (countB bnd P) := by
  induction P with
  | clause _ => intro _ _; exact mono_const 1
  | seq a b iha ihb => intro bnd hb; exact mono_add (iha bnd hb) (ihb bnd hb)
  | forDown bound body ih =>
    intro bnd hb
    exact mono_mul (mono_ubN hb bound) (ih _ (mono_extB (mono_ubN hb bound) hb))
  | ifLe _ _ y n ihy ihn => intro bnd hb; exact mono_add (ihy bnd hb) (ihn bnd hb)
  | ifInput _ e z o ihe ihz iho =>
    intro bnd hb; exact mono_add (mono_add (ihe bnd hb) (ihz bnd hb)) (iho bnd hb)

theorem mono_litB {k : Nat} {bnd : Fin k → NumExpr 1} (hb : ∀ i, Mono (bnd i))
    (lits : List (LiteralExpr k)) : Mono (litB bnd lits) := by
  induction lits with
  | nil => exact mono_const 0
  | cons a ls ih => exact mono_add (mono_add (mono_ubN hb a.index) (mono_const 1)) ih

theorem mono_varB {k : Nat} (P : ClauseProgram k) :
    ∀ (bnd : Fin k → NumExpr 1), (∀ i, Mono (bnd i)) → Mono (varB bnd P) := by
  induction P with
  | clause lits => intro bnd hb; exact mono_litB hb lits
  | seq a b iha ihb => intro bnd hb; exact mono_add (iha bnd hb) (ihb bnd hb)
  | forDown bound body ih =>
    intro bnd hb
    exact ih _ (mono_extB (mono_ubN hb bound) hb)
  | ifLe _ _ y n ihy ihn => intro bnd hb; exact mono_add (ihy bnd hb) (ihn bnd hb)
  | ifInput _ e z o ihe ihz iho =>
    intro bnd hb; exact mono_add (mono_add (ihe bnd hb) (ihz bnd hb)) (iho bnd hb)

/-! ## The bounds of a fixed emitter -/

section fixed

variable (P : ClauseProgram 1)

/-- The input length bounds itself. -/
def bnd0 : Fin 1 → NumExpr 1 := fun _ => .var 0

/-- `W n`: a strict bound on the variables, at least one. -/
def Wx : NumExpr 1 := .add (varB bnd0 P) (.const 1)

/-- `M n`: a bound on the number of clauses. -/
def Mx : NumExpr 1 := countB bnd0 P

/-- `R n = 2 W n`: the width of a row of occurrence bits. -/
def Rx : NumExpr 1 := .mul (.const 2) (Wx P)

/-- `B n = 5 M n R n + 1`. -/
def Bx : NumExpr 1 := .add (.mul (.mul (.const 5) (Mx P)) (Rx P)) (.const 1)

/-- `A n = (n + 1) B n`: the padding. -/
def Ax : NumExpr 1 := .mul (.add (.var 0) (.const 1)) (Bx P)

theorem env_bnd0 (n : Nat) : ∀ i, (fun _ => n : Env 1) i ≤ (bnd0 i).eval (fun _ => n) :=
  fun _ => Nat.le_refl _

theorem mono_bnd0 : ∀ i, Mono (bnd0 i) := fun _ => mono_var 0

theorem emit_length_le (input : Word) :
    (P.emit input (fun _ => input.length)).length ≤ (Mx P).eval (fun _ => input.length) :=
  countB_sound P input _ bnd0 _ (env_bnd0 input.length)

theorem emit_var_lt (input : Word) :
    ∀ c ∈ P.emit input (fun _ => input.length), ∀ l ∈ c,
      l.var < (Wx P).eval (fun _ => input.length) := by
  intro c hc l hl
  have := varB_sound P input _ bnd0 _ (env_bnd0 input.length) c hc l hl
  simp only [Wx, NumExpr.eval]
  omega

theorem mono_Bx : Mono (Bx P) :=
  mono_add (mono_mul (mono_mul (mono_const 5) (mono_countB P bnd0 mono_bnd0))
    (mono_mul (mono_const 2) (mono_add (mono_varB P bnd0 mono_bnd0) (mono_const 1))))
    (mono_const 1)

end fixed

end Complexity.Planar.Emit
