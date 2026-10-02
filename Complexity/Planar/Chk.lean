module

public import Complexity.StackTableauEmitter
import Lean.Elab.Tactic.Omega

/-!
# A check language compiled to formula emitters

`Chk S` describes a finite conjunction of bounded checks on a binary word, with `S` named
numeric slots: loops bind a slot to `0, 1, …, bound - 1`, tests compare expressions or read a
bit of the word.  `Chk.compile` translates a check into a `ClauseProgram` that emits one empty
clause for every failed check, and `Chk.compile_holds` states that it emits nothing exactly
when the check holds.  This is how polynomial-time verifiers are written below, without
programming the stack machine directly.
-/

@[expose] public section

namespace Complexity.Planar

open StackTableauEmitter

/-- Numeric expressions over named slots. -/
inductive Ex (S : Nat) where
  | slot (s : Fin S)
  | const (c : Nat)
  | add (a b : Ex S)
  | mul (a b : Ex S)
  | sub (a b : Ex S)

namespace Ex

variable {S : Nat}

def eval : Ex S → (Fin S → Nat) → Nat
  | .slot s, ρ => ρ s
  | .const c, _ => c
  | .add a b, ρ => a.eval ρ + b.eval ρ
  | .mul a b, ρ => a.eval ρ * b.eval ρ
  | .sub a b, ρ => a.eval ρ - b.eval ρ

def compile {n : Nat} : Ex S → (Fin S → Fin n) → NumExpr n
  | .slot s, σ => .var (σ s)
  | .const c, _ => .const c
  | .add a b, σ => .add (a.compile σ) (b.compile σ)
  | .mul a b, σ => .mul (a.compile σ) (b.compile σ)
  | .sub a b, σ => .sub (a.compile σ) (b.compile σ)

theorem eval_compile {n : Nat} (e : Ex S) (σ : Fin S → Fin n) (env : Env n)
    (ρ : Fin S → Nat) (h : ∀ s, env (σ s) = ρ s) : (e.compile σ).eval env = e.eval ρ := by
  induction e with
  | slot s => exact h s
  | const c => rfl
  | add a b iha ihb => simp [compile, eval, NumExpr.eval, iha, ihb]
  | mul a b iha ihb => simp [compile, eval, NumExpr.eval, iha, ihb]
  | sub a b iha ihb => simp [compile, eval, NumExpr.eval, iha, ihb]

instance : OfNat (Ex S) k := ⟨.const k⟩
instance : Add (Ex S) := ⟨.add⟩
instance : Mul (Ex S) := ⟨.mul⟩
instance : Sub (Ex S) := ⟨.sub⟩

@[simp] theorem eval_slot (s : Fin S) (ρ : Fin S → Nat) : (Ex.slot s).eval ρ = ρ s := rfl
@[simp] theorem eval_const (c : Nat) (ρ : Fin S → Nat) : (Ex.const c : Ex S).eval ρ = c := rfl
@[simp] theorem eval_ofNat (c : Nat) (ρ : Fin S → Nat) : (OfNat.ofNat c : Ex S).eval ρ = c := rfl
@[simp] theorem eval_add (a b : Ex S) (ρ : Fin S → Nat) : (a + b).eval ρ = a.eval ρ + b.eval ρ := rfl
@[simp] theorem eval_mul (a b : Ex S) (ρ : Fin S → Nat) : (a * b).eval ρ = a.eval ρ * b.eval ρ := rfl
@[simp] theorem eval_sub (a b : Ex S) (ρ : Fin S → Nat) : (a - b).eval ρ = a.eval ρ - b.eval ρ := rfl

end Ex

/-- Bounded checks on a word, with named slots. -/
inductive Chk (S : Nat) where
  | ok
  | fail
  | both (a b : Chk S)
  | all (s : Fin S) (bound : Ex S) (body : Chk S)
  | le (a b : Ex S) (yes no : Chk S)
  | bit (p : Ex S) (onNone onZero onOne : Chk S)

/-- Update one slot. -/
def setSlot {S : Nat} (ρ : Fin S → Nat) (s : Fin S) (v : Nat) : Fin S → Nat :=
  fun t => if t = s then v else ρ t

@[simp] theorem setSlot_same {S : Nat} (ρ : Fin S → Nat) (s : Fin S) (v : Nat) :
    setSlot ρ s v s = v := by simp [setSlot]

theorem setSlot_other {S : Nat} (ρ : Fin S → Nat) {s t : Fin S} (h : t ≠ s) (v : Nat) :
    setSlot ρ s v t = ρ t := by simp [setSlot, h]

namespace Chk

variable {S : Nat}

/-- The meaning of a check on the word `u` in the slot environment `ρ`. -/
def Holds (u : List Bool) : Chk S → (Fin S → Nat) → Prop
  | .ok, _ => True
  | .fail, _ => False
  | .both a b, ρ => Holds u a ρ ∧ Holds u b ρ
  | .all s bound body, ρ => ∀ i, i < bound.eval ρ → Holds u body (setSlot ρ s i)
  | .le a b yes no, ρ => if a.eval ρ ≤ b.eval ρ then Holds u yes ρ else Holds u no ρ
  | .bit p onNone onZero onOne, ρ =>
      match u[p.eval ρ]? with
      | Option.none => Holds u onNone ρ
      | some false => Holds u onZero ρ
      | some true => Holds u onOne ρ

/-- Rebind slot `s` to the new innermost variable. -/
def bindSlot {n : Nat} (σ : Fin S → Fin n) (s : Fin S) : Fin S → Fin (n + 1) :=
  fun t => if t = s then 0 else (σ t).succ

/-- Translation to a formula emitter: every failed check emits one empty clause. -/
def compile {n : Nat} : Chk S → (Fin S → Fin n) → ClauseProgram n
  | .ok, _ => ClauseProgram.skip
  | .fail, _ => .clause []
  | .both a b, σ => .seq (a.compile σ) (b.compile σ)
  | .all s bound body, σ => .forDown (bound.compile σ) (body.compile (bindSlot σ s))
  | .le a b yes no, σ => .ifLe (a.compile σ) (b.compile σ) (yes.compile σ) (no.compile σ)
  | .bit p onNone onZero onOne, σ =>
      .ifInput (p.compile σ) (onNone.compile σ) (onZero.compile σ) (onOne.compile σ)

theorem bindSlot_agree {n : Nat} (σ : Fin S → Fin n) (s : Fin S) (env : Env n)
    (ρ : Fin S → Nat) (h : ∀ t, env (σ t) = ρ t) (i : Nat) :
    ∀ t, extend i env (bindSlot σ s t) = setSlot ρ s i t := by
  intro t
  by_cases ht : t = s
  · subst ht; simp [bindSlot, setSlot]
  · simp [bindSlot, setSlot, ht, h t]

theorem flatMap_eq_nil_iff {α β : Type} (l : List α) (f : α → List β) :
    l.flatMap f = [] ↔ ∀ a ∈ l, f a = [] := by
  induction l with
  | nil => simp
  | cons a l ih => simp [List.flatMap_cons, ih]

/-- The compiled emitter emits nothing exactly when the check holds. -/
theorem compile_holds {n : Nat} (c : Chk S) (u : List Bool) (σ : Fin S → Fin n) (env : Env n)
    (ρ : Fin S → Nat) (h : ∀ t, env (σ t) = ρ t) :
    (c.compile σ).emit u env = [] ↔ c.Holds u ρ := by
  induction c generalizing n env ρ with
  | ok => simp [compile, Holds]
  | fail => simp [compile, Holds]
  | both a b iha ihb =>
    simp only [compile, ClauseProgram.emit, List.append_eq_nil_iff, Holds]
    rw [iha σ env ρ h, ihb σ env ρ h]
  | all s bound body ih =>
    simp only [compile, ClauseProgram.emit, Holds]
    rw [flatMap_eq_nil_iff]
    rw [Ex.eval_compile bound σ env ρ h]
    constructor
    · intro hh i hi
      have := hh i (by simp [List.mem_reverse, List.mem_range, hi])
      exact (ih (bindSlot σ s) (extend i env) (setSlot ρ s i) (bindSlot_agree σ s env ρ h i)).mp this
    · intro hh i hi
      simp only [List.mem_reverse, List.mem_range] at hi
      exact (ih (bindSlot σ s) (extend i env) (setSlot ρ s i) (bindSlot_agree σ s env ρ h i)).mpr
        (hh i hi)
  | le a b yes no ihy ihn =>
    simp only [compile, ClauseProgram.emit, Holds, Ex.eval_compile a σ env ρ h,
      Ex.eval_compile b σ env ρ h]
    split
    · exact ihy σ env ρ h
    · exact ihn σ env ρ h
  | bit p onNone onZero onOne ihn ihz iho =>
    simp only [compile, ClauseProgram.emit, Holds, Ex.eval_compile p σ env ρ h]
    rcases hu : u[p.eval ρ]? with _ | _ | _
    · exact ihn σ env ρ h
    · exact ihz σ env ρ h
    · exact iho σ env ρ h

/-! ## Derived checks -/

/-- `a = b` decides between two checks. -/
def eq (a b : Ex S) (yes no : Chk S) : Chk S := .le a b (.le b a yes no) no

theorem holds_eq (u : List Bool) (a b : Ex S) (yes no : Chk S) (ρ : Fin S → Nat) :
    Holds u (eq a b yes no) ρ ↔ if a.eval ρ = b.eval ρ then Holds u yes ρ else Holds u no ρ := by
  simp only [eq, Holds]
  by_cases h1 : a.eval ρ ≤ b.eval ρ
  · by_cases h2 : b.eval ρ ≤ a.eval ρ
    · have : a.eval ρ = b.eval ρ := by omega
      simp [this]
    · have : a.eval ρ ≠ b.eval ρ := by omega
      simp [h2, this]
  · have : a.eval ρ ≠ b.eval ρ := by omega
    simp [h1, this]

/-- Require `a ≤ b`. -/
def reqLe (a b : Ex S) : Chk S := .le a b .ok .fail

/-- Require `a = b`. -/
def reqEq (a b : Ex S) : Chk S := eq a b .ok .fail

/-- Require `a < b`. -/
def reqLt (a b : Ex S) : Chk S := .le (.add a (.const 1)) b .ok .fail

/-- Run `c` only when `a ≤ b`. -/
def whenLe (a b : Ex S) (c : Chk S) : Chk S := .le a b c .ok

/-- Run `c` only when `a < b`. -/
def whenLt (a b : Ex S) (c : Chk S) : Chk S := .le (.add a (.const 1)) b c .ok

/-- Run `c` only when `a = b`. -/
def whenEq (a b : Ex S) (c : Chk S) : Chk S := eq a b c .ok

/-- Run `c` only when `a ≠ b`. -/
def whenNe (a b : Ex S) (c : Chk S) : Chk S := eq a b .ok c

/-- Require the bit at `p` to exist and equal `v`. -/
def reqBit (p : Ex S) (v : Bool) : Chk S :=
  .bit p .fail (if v then .fail else .ok) (if v then .ok else .fail)

/-- A bounded universal statement. -/
def forall' (s : Fin S) (bound : Ex S) (body : Chk S) : Chk S := .all s bound body

@[simp] theorem holds_ok (u : List Bool) (ρ : Fin S → Nat) : Holds u (.ok : Chk S) ρ := trivial
@[simp] theorem holds_fail (u : List Bool) (ρ : Fin S → Nat) : ¬ Holds u (.fail : Chk S) ρ := id

@[simp] theorem holds_both (u : List Bool) (a b : Chk S) (ρ : Fin S → Nat) :
    Holds u (.both a b) ρ ↔ Holds u a ρ ∧ Holds u b ρ := Iff.rfl

@[simp] theorem holds_all (u : List Bool) (s : Fin S) (bound : Ex S) (body : Chk S)
    (ρ : Fin S → Nat) :
    Holds u (.all s bound body) ρ ↔ ∀ i, i < bound.eval ρ → Holds u body (setSlot ρ s i) :=
  Iff.rfl

@[simp] theorem holds_reqLe (u : List Bool) (a b : Ex S) (ρ : Fin S → Nat) :
    Holds u (reqLe a b) ρ ↔ a.eval ρ ≤ b.eval ρ := by
  simp only [reqLe, Holds]; by_cases h : a.eval ρ ≤ b.eval ρ <;> simp [h]

@[simp] theorem holds_reqLt (u : List Bool) (a b : Ex S) (ρ : Fin S → Nat) :
    Holds u (reqLt a b) ρ ↔ a.eval ρ < b.eval ρ := by
  simp only [reqLt, Holds, Ex.eval]
  by_cases h : a.eval ρ + 1 ≤ b.eval ρ <;> simp [h] <;> omega

@[simp] theorem holds_reqEq (u : List Bool) (a b : Ex S) (ρ : Fin S → Nat) :
    Holds u (reqEq a b) ρ ↔ a.eval ρ = b.eval ρ := by
  rw [reqEq, holds_eq]; by_cases h : a.eval ρ = b.eval ρ <;> simp [h]

@[simp] theorem holds_whenLe (u : List Bool) (a b : Ex S) (c : Chk S) (ρ : Fin S → Nat) :
    Holds u (whenLe a b c) ρ ↔ (a.eval ρ ≤ b.eval ρ → Holds u c ρ) := by
  simp only [whenLe, Holds]; by_cases h : a.eval ρ ≤ b.eval ρ <;> simp [h]

@[simp] theorem holds_whenLt (u : List Bool) (a b : Ex S) (c : Chk S) (ρ : Fin S → Nat) :
    Holds u (whenLt a b c) ρ ↔ (a.eval ρ < b.eval ρ → Holds u c ρ) := by
  simp only [whenLt, Holds, Ex.eval]
  by_cases h : a.eval ρ + 1 ≤ b.eval ρ
  · simp [h, show a.eval ρ < b.eval ρ by omega]
  · simp [h, show ¬ a.eval ρ < b.eval ρ by omega]

@[simp] theorem holds_whenEq (u : List Bool) (a b : Ex S) (c : Chk S) (ρ : Fin S → Nat) :
    Holds u (whenEq a b c) ρ ↔ (a.eval ρ = b.eval ρ → Holds u c ρ) := by
  rw [whenEq, holds_eq]; by_cases h : a.eval ρ = b.eval ρ <;> simp [h]

@[simp] theorem holds_whenNe (u : List Bool) (a b : Ex S) (c : Chk S) (ρ : Fin S → Nat) :
    Holds u (whenNe a b c) ρ ↔ (a.eval ρ ≠ b.eval ρ → Holds u c ρ) := by
  rw [whenNe, holds_eq]; by_cases h : a.eval ρ = b.eval ρ <;> simp [h]

@[simp] theorem holds_reqBit (u : List Bool) (p : Ex S) (v : Bool) (ρ : Fin S → Nat) :
    Holds u (reqBit p v) ρ ↔ u[p.eval ρ]? = some v := by
  simp only [reqBit, Holds]
  split <;> cases v <;> simp_all

@[simp] theorem holds_forall' (u : List Bool) (s : Fin S) (bound : Ex S) (body : Chk S)
    (ρ : Fin S → Nat) :
    Holds u (forall' s bound body) ρ ↔ ∀ i, i < bound.eval ρ → Holds u body (setSlot ρ s i) :=
  Iff.rfl

/-- Conjunction of a list of checks. -/
def allOf : List (Chk S) → Chk S
  | [] => .ok
  | c :: cs => .both c (allOf cs)

@[simp] theorem holds_allOf (u : List Bool) (cs : List (Chk S)) (ρ : Fin S → Nat) :
    Holds u (allOf cs) ρ ↔ ∀ c ∈ cs, Holds u c ρ := by
  induction cs with
  | nil => simp [allOf]
  | cons c cs ih => simp [allOf, ih]

end Chk

end Complexity.Planar
