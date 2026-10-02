module

public import Complexity.SAT
import Lean.Elab.Tactic.Omega

/-!
# Implication chains over an abstract literal type

A clause `a₀ ∨ a₁ ∨ … ∨ a_(k-1)` with `k ≥ 4` is split into the three-literal clauses
`a₀ ∨ a₁ ∨ z₁`, `¬z₁ ∨ a₂ ∨ z₂`, …, `¬z_(k-3) ∨ a_(k-2) ∨ a_(k-1)`; clauses with two or three
literals are kept. The literal type is abstract (`zp j` and `zn j` are the two signs of the
chain variable `z_j`), so the same definition serves for literal expressions and for literal
values. This file proves the semantic facts used by the restricted-SAT reductions.
-/

@[expose] public section

namespace Complexity.Restricted

/-- The chain of clauses for `a :: rest`, starting with chain variable number `j`. -/
def chainFrom {α : Type} (zp zn : Nat → α) : α → List α → Nat → List (List α)
  | a, [], _ => [[a]]
  | a, [b], _ => [[a, b]]
  | a, [b, c], _ => [[a, b, c]]
  | a, b :: c :: d :: rest, j => [a, b, zp j] :: chainFrom zp zn (zn j) (c :: d :: rest) (j + 1)

/-- The chain of a clause; chain variables are numbered from `1`. -/
def gadget {α : Type} (zp zn : Nat → α) : List α → List (List α)
  | [] => []
  | a :: rest => chainFrom zp zn a rest 1

theorem chainFrom_map {α β : Type} (f : α → β) (zp zn : Nat → α) (a : α) (rest : List α)
    (j : Nat) :
    chainFrom (fun i => f (zp i)) (fun i => f (zn i)) (f a) (rest.map f) j =
      (chainFrom zp zn a rest j).map (List.map f) := by
  induction rest generalizing a j with
  | nil => rfl
  | cons b tail ih =>
    match tail, ih with
    | [], _ => rfl
    | [c], _ => rfl
    | c :: d :: rest, ih =>
      simp only [List.map_cons, chainFrom]
      have h := ih (zn j) (j + 1)
      simp only [List.map_cons] at h
      rw [h]
      rfl

theorem gadget_map {α β : Type} (f : α → β) (zp zn : Nat → α) (xs : List α) :
    gadget (fun i => f (zp i)) (fun i => f (zn i)) (xs.map f) = (gadget zp zn xs).map (List.map f) := by
  cases xs with
  | nil => rfl
  | cons a rest => exact chainFrom_map f zp zn a rest 1

/-- Every clause of a chain built from at least two literals has two or three literals. -/
theorem chainFrom_length {α : Type} (zp zn : Nat → α) (a : α) (rest : List α) (j : Nat)
    (hrest : rest ≠ []) :
    ∀ c ∈ chainFrom zp zn a rest j, c.length = 2 ∨ c.length = 3 := by
  induction rest generalizing a j with
  | nil => exact absurd rfl hrest
  | cons b tail ih =>
    match tail, ih with
    | [], _ => intro c hc; simp [chainFrom] at hc; subst hc; simp
    | [c], _ => intro c' hc; simp [chainFrom] at hc; subst hc; simp
    | c :: d :: rest, ih =>
      intro c' hc
      simp only [chainFrom, List.mem_cons] at hc
      rcases hc with hc | hc
      · subst hc; simp
      · exact ih (zn j) (j + 1) (by simp) c' hc

/-- If every clause of the chain holds, the original clause holds. -/
theorem chainFrom_sound {α : Type} (val : α → Bool) (zp zn : Nat → α)
    (hz : ∀ i, val (zn i) = !val (zp i)) (a : α) (rest : List α) (j : Nat)
    (h : ∀ c ∈ chainFrom zp zn a rest j, c.any val = true) :
    (val a || rest.any val) = true := by
  induction rest generalizing a j with
  | nil => simpa [chainFrom] using h
  | cons b tail ih =>
    match tail, ih with
    | [], _ => simpa [chainFrom] using h
    | [c], _ => simpa [chainFrom, Bool.or_assoc] using h
    | c :: d :: rest, ih =>
      have h₁ : ([a, b, zp j] : List α).any val = true := h _ (by simp [chainFrom])
      have h₂ := ih (zn j) (j + 1) (fun c hc => h c (by simp [chainFrom, hc]))
      rw [hz] at h₂
      cases hzj : val (zp j)
      · simp only [hzj, List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_true] at h₁
        simp only [List.any_cons, Bool.or_eq_true]
        rcases h₁ with h | h <;> simp [h]
      · have key : (c :: d :: rest).any val = true := by simpa [hzj] using h₂
        rw [List.any_cons, key]
        simp

/-- With the intended values of the chain variables, every clause of the chain holds. -/
theorem chainFrom_complete {α : Type} (val : α → Bool) (zp zn : Nat → α) (a : α)
    (rest : List α) (j : Nat)
    (hz : ∀ i, i + 2 < rest.length →
      val (zp (j + i)) = !(val a || (rest.take (i + 1)).any val) ∧
      val (zn (j + i)) = (val a || (rest.take (i + 1)).any val))
    (h : (val a || rest.any val) = true) :
    ∀ c ∈ chainFrom zp zn a rest j, c.any val = true := by
  induction rest generalizing a j with
  | nil => intro c hc; simp [chainFrom] at hc; subst hc; simpa using h
  | cons b tail ih =>
    match tail, ih, hz with
    | [], _, _ => intro c hc; simp [chainFrom] at hc; subst hc; simpa using h
    | [c], _, _ => intro c' hc; simp [chainFrom] at hc; subst hc; simpa [Bool.or_assoc] using h
    | c :: d :: rest, ih, hz =>
      intro c' hc
      simp only [chainFrom, List.mem_cons] at hc
      have h0 := hz 0 (by simp)
      simp only [Nat.add_zero, List.take_succ_cons, List.take_zero, List.any_cons,
        List.any_nil, Bool.or_false] at h0
      rcases hc with hc | hc
      · subst hc
        simp only [List.any_cons, List.any_nil, Bool.or_false, h0.1]
        cases val a <;> cases val b <;> rfl
      · refine ih (zn j) (j + 1) ?_ ?_ c' hc
        · intro i hi
          have hi' := hz (i + 1) (by simp at hi ⊢; omega)
          have e1 : j + 1 + i = j + (i + 1) := by omega
          rw [e1, h0.2]
          simp only [List.take_succ_cons, List.any_cons] at hi'
          simpa [Bool.or_assoc] using hi'
        · rw [h0.2]
          simpa [Bool.or_assoc] using h

/-- Distinct variables in the clause and fresh chain variables give distinct variables in
every clause of the chain. -/
theorem chainFrom_nodup {α : Type} (vars : α → Nat) (zp zn : Nat → α)
    (hzn : ∀ i, vars (zn i) = vars (zp i))
    (hinj : ∀ i i', vars (zp i) = vars (zp i') → i = i') (a : α) (rest : List α) (j : Nat)
    (hnodup : ((a :: rest).map vars).Nodup)
    (hfresh : ∀ i, j ≤ i → vars (zp i) ∉ (a :: rest).map vars) :
    ∀ c ∈ chainFrom zp zn a rest j, (c.map vars).Nodup := by
  induction rest generalizing a j with
  | nil => intro c hc; simp [chainFrom] at hc; subst hc; simp
  | cons b tail ih =>
    match tail, ih with
    | [], _ => intro c hc; simp [chainFrom] at hc; subst hc; simpa using hnodup
    | [c], _ => intro c' hc; simp [chainFrom] at hc; subst hc; simpa using hnodup
    | c :: d :: rest, ih =>
      intro c' hc
      simp only [chainFrom, List.mem_cons] at hc
      have hj := hfresh j (Nat.le_refl j)
      have h1 := (List.nodup_cons.mp hnodup).1
      have h2 : (List.map vars (c :: d :: rest)).Nodup :=
        (List.nodup_cons.mp (List.nodup_cons.mp hnodup).2).2
      rcases hc with hc | hc
      · subst hc
        have hab : vars a ≠ vars b := fun h => h1 (by rw [h]; simp)
        have hza : vars (zp j) ≠ vars a := fun h => hj (by rw [h]; simp)
        have hzb : vars (zp j) ≠ vars b := fun h => hj (by rw [h]; simp)
        simp [List.nodup_cons, hab, Ne.symm hza, Ne.symm hzb]
      · refine ih (zn j) (j + 1) ?_ ?_ c' hc
        · refine List.nodup_cons.mpr ⟨?_, h2⟩
          rw [hzn]
          exact fun h => hj (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h))
        · intro i hi h
          rcases List.mem_cons.mp h with h | h
          · rw [hzn] at h
            have := hinj _ _ h
            omega
          · exact hfresh i (by omega) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h))

end Complexity.Restricted
