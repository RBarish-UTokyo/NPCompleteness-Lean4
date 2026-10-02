module

public import Complexity.StackThreeSAT
import Lean.Elab.Tactic.Omega

/-!
# Generic tools for Boolean-stack programs

* `iterStep` and `whileCounter_iter`: a counted loop computes the iterate of a partial
  register transformer, including early failure;
* `testEmpty`: a two-instruction emptiness test;
* `embed`: run a program over the first registers of a larger register file.
-/

@[expose] public section

namespace Complexity.Binary

open Complexity.StackMachine (Registers set branch)
open Complexity.StackProgram

/-- A terminating run with decision `b` and final registers `out` realizes a partial
register transformer's result. -/
def Realizes {k : Nat} (expected : Option (Registers k)) (b : Bool) (out : Registers k) : Prop :=
  match expected with
  | none => b = false
  | some q => b = true ∧ out = q

@[simp] theorem realizes_none {k : Nat} (b : Bool) (out : Registers k) :
    Realizes none b out ↔ b = false := Iff.rfl

@[simp] theorem realizes_some {k : Nat} (q : Registers k) (b : Bool) (out : Registers k) :
    Realizes (some q) b out ↔ b = true ∧ out = q := Iff.rfl

/-- `n` iterations of `step`, the counter register `j` holding the remaining count. -/
def iterStep {k : Nat} (j : Fin (k + 1)) (step : Registers k → Option (Registers k)) :
    Nat → Registers k → Option (Registers k)
  | 0, r => some r
  | n + 1, r => do
      let next ← step (set r j (List.replicate n true))
      iterStep j step n next

theorem iterStep_zero {k : Nat} (j : Fin (k + 1)) (step : Registers k → Option (Registers k))
    (r : Registers k) : iterStep j step 0 r = some r := rfl

theorem iterStep_succ {k : Nat} (j : Fin (k + 1)) (step : Registers k → Option (Registers k))
    (n : Nat) (r : Registers k) :
    iterStep j step (n + 1) r =
      (step (set r j (List.replicate n true))).bind (iterStep j step n) := rfl

/-- A counted loop realizes the iterate of the transformer realized by its body. -/
theorem whileCounter_iter {k : Nat} {L : Type} (body : Program k L) (j : Fin (k + 1))
    (step : Registers k → Option (Registers k)) (I : Registers k → Prop) (cost : Nat)
    (hpop : ∀ r tail, I r → r j = true :: tail → I (set r j tail))
    (hbody : ∀ r, I r → ∃ t b out, t ≤ cost ∧ Exec body body.start r t (b, out) ∧
      Realizes (step r) b out)
    (hstep : ∀ r out, I r → step r = some out → I out ∧ out j = r j)
    (n : Nat) (r : Registers k) (hr : r j = List.replicate n true) (hI : I r) :
    ∃ t b out, t ≤ n * (cost + 1) + 2 ∧
      Exec (whileCounter j body) (.inl false) r t (b, out) ∧
      Realizes (iterStep j step n r) b out := by
  induction n generalizing r with
  | zero =>
    refine ⟨2, true, r, by simp, exec_whileCounter_done j body r (by simpa using hr), ?_⟩
    simp [iterStep]
  | succ n ih =>
    let r' := set r j (List.replicate n true)
    have hrcons : r j = true :: List.replicate n true := by simpa [List.replicate_succ] using hr
    have hI' : I r' := hpop r _ hI hrcons
    obtain ⟨t, b, mid, ht, he, hspec⟩ := hbody r' hI'
    cases hs : step r' with
    | none =>
      have hb : b = false := by simpa [hs] using hspec
      subst b
      refine ⟨t + 1, false, mid, ?_, exec_whileCounter_failure j body hrcons he, ?_⟩
      · have : cost + 1 ≤ (n + 1) * (cost + 1) := by simp [Nat.succ_mul]
        omega
      · simp [iterStep_succ, r', hs]
    | some q =>
      have hspec' : b = true ∧ mid = q := by simpa [hs] using hspec
      obtain ⟨rfl, rfl⟩ := hspec'
      obtain ⟨hIq, hjq⟩ := hstep r' mid hI' hs
      have hmj : mid j = List.replicate n true := by simpa [r'] using hjq
      obtain ⟨s, b, out, hsle, he', hspec''⟩ := ih mid hmj hIq
      refine ⟨t + s + 1, b, out, ?_, exec_whileCounter_next j body hrcons he he', ?_⟩
      · simp only [Nat.succ_mul]; omega
      · simpa [iterStep_succ, r', hs] using hspec''

/-- The invariant survives the iterate, and the counter ends empty. -/
theorem iterStep_invariant {k : Nat} (j : Fin (k + 1))
    (step : Registers k → Option (Registers k)) (I : Registers k → Prop)
    (hpop : ∀ r tail, I r → r j = true :: tail → I (set r j tail))
    (hstep : ∀ r out, I r → step r = some out → I out ∧ out j = r j)
    (n : Nat) (r : Registers k) (hr : r j = List.replicate n true) (hI : I r)
    (out : Registers k) (h : iterStep j step n r = some out) : I out ∧ out j = [] := by
  induction n generalizing r with
  | zero =>
    simp only [iterStep, Option.some.injEq] at h
    subst h
    exact ⟨hI, by simpa using hr⟩
  | succ n ih =>
    have hrcons : r j = true :: List.replicate n true := by simpa [List.replicate_succ] using hr
    have hI' := hpop r _ hI hrcons
    cases hs : step (set r j (List.replicate n true)) with
    | none => simp [iterStep_succ, hs] at h
    | some q =>
      rw [iterStep_succ, hs, Option.bind_some] at h
      obtain ⟨hIq, hjq⟩ := hstep _ q hI' hs
      exact ih q (by simpa using hjq) hIq h

/-- A two-instruction emptiness test. -/
def testEmpty {k : Nat} (j : Fin (k + 1)) (emptyResult nonemptyResult : Bool) :
    Program k (Fin 3) where
  start := 0
  code := fun q => if q = 0 then .peek j 1 2 2
    else if q = 1 then .halt emptyResult else .halt nonemptyResult

theorem exec_testEmpty {k : Nat} (j : Fin (k + 1)) (emptyResult nonemptyResult : Bool)
    (r : Registers k) :
    Exec (testEmpty j emptyResult nonemptyResult) (testEmpty j emptyResult nonemptyResult).start
      r 2 ((if (r j).isEmpty then emptyResult else nonemptyResult), r) := by
  cases hr : r j with
  | nil =>
    apply Exec.next (q' := 1) (r' := r)
    · simp [StackProgram.step, testEmpty, hr, branch]
    · exact .halt (by simp [StackProgram.step, testEmpty])
  | cons b tail =>
    apply Exec.next (q' := 2) (r' := r)
    · cases b <;> simp [StackProgram.step, testEmpty, hr, branch]
    · exact .halt (by simp [StackProgram.step, testEmpty])

/-! ## Embedding a program into a larger register file -/

/-- A register of the smaller file, as a register of the larger one. -/
def liftReg {k k' : Nat} (h : k ≤ k') (j : Fin (k + 1)) : Fin (k' + 1) :=
  ⟨j.val, by have := h; have := j.isLt; omega⟩

def embedOp {k k' : Nat} {L : Type} (h : k ≤ k') : Op k L → Op k' L
  | .halt b => .halt b
  | .goto q => .goto q
  | .push j b q => .push (liftReg h j) b q
  | .pop j e z o => .pop (liftReg h j) e z o
  | .peek j e z o => .peek (liftReg h j) e z o

/-- The same program, acting on the first registers of a larger file. -/
def embed {k k' : Nat} {L : Type} (h : k ≤ k') (p : Program k L) : Program k' L where
  start := p.start
  code := fun q => embedOp h (p.code q)

def restrict {k k' : Nat} (h : k ≤ k') (R : Registers k') : Registers k :=
  fun j => R (liftReg h j)

def extend {k k' : Nat} (_h : k ≤ k') (R : Registers k') (r : Registers k) : Registers k' :=
  fun j => if hj : j.val < k + 1 then r ⟨j.val, hj⟩ else R j

@[simp] theorem restrict_extend {k k' : Nat} (h : k ≤ k') (R : Registers k')
    (r : Registers k) : restrict h (extend h R r) = r := by
  funext j
  simp [restrict, extend, liftReg, j.isLt]

@[simp] theorem extend_extend {k k' : Nat} (h : k ≤ k') (R : Registers k')
    (r s : Registers k) : extend h (extend h R r) s = extend h R s := by
  funext j
  by_cases hj : j.val < k + 1 <;> simp [extend, hj]

theorem extend_set {k k' : Nat} (h : k ≤ k') (R : Registers k') (j : Fin (k + 1))
    (xs : List Bool) : extend h R (set (restrict h R) j xs) = set R (liftReg h j) xs := by
  funext i
  by_cases hi : i.val < k + 1
  · by_cases hij : i = liftReg h j
    · subst hij
      simp [extend, liftReg, StackMachine.set]
    · have hne : (⟨i.val, hi⟩ : Fin (k + 1)) ≠ j := by
        intro he
        apply hij
        subst he
        rfl
      simp only [liftReg] at hij
      simp [extend, hi, StackMachine.set, hne, hij, restrict, liftReg]
  · have hij : i ≠ liftReg h j := by
      intro he
      subst he
      exact hi j.isLt
    simp [extend, hi, StackMachine.set, hij]

theorem step_embed {k k' : Nat} {L : Type} (h : k ≤ k') (p : Program k L) (q : L)
    (R : Registers k') :
    StackProgram.step (embed h p) q R = match StackProgram.step p q (restrict h R) with
      | .inl (b, r) => .inl (b, extend h R r)
      | .inr (q', r) => .inr (q', extend h R r) := by
  have hid : extend h R (restrict h R) = R := by
    funext i
    by_cases hi : i.val < k + 1
    · simp [extend, hi, restrict, liftReg]
    · simp [extend, hi]
  cases hc : p.code q with
  | halt b => simp [StackProgram.step, embed, embedOp, hc, hid]
  | goto q' => simp [StackProgram.step, embed, embedOp, hc, hid]
  | push j b q' =>
    simp only [StackProgram.step, embed, embedOp, hc]
    rw [extend_set]
    rfl
  | pop j e z o =>
    simp only [StackProgram.step, embed, embedOp, hc]
    rw [extend_set]
    rfl
  | peek j e z o => simp [StackProgram.step, embed, embedOp, hc, hid, restrict]

theorem exec_embed_aux {k k' : Nat} {L : Type} (h : k ≤ k') (p : Program k L)
    {q : L} {r : Registers k} {t : Nat} {result : Bool × Registers k}
    (he : Exec p q r t result) :
    ∀ R, restrict h R = r → Exec (embed h p) q R t (result.1, extend h R result.2) := by
  induction he with
  | halt hs =>
    intro R hR
    subst hR
    exact .halt (by rw [step_embed, hs])
  | next hs _ ih =>
    intro R hR
    subst hR
    have hh := ih _ (restrict_extend h R _)
    rw [extend_extend] at hh
    exact .next (by rw [step_embed, hs]) hh

/-- Running an embedded program changes only the embedded registers. -/
theorem exec_embedded {k k' : Nat} {L : Type} (h : k ≤ k') (p : Program k L)
    {q : L} {R : Registers k'} {t : Nat} {b : Bool} {r : Registers k}
    (he : Exec p q (restrict h R) t (b, r)) : Exec (embed h p) q R t (b, extend h R r) :=
  exec_embed_aux h p he R rfl

end Complexity.Binary
