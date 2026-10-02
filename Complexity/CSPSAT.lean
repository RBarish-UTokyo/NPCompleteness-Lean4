module

public import Complexity.Constraints
import Lean.Elab.Tactic.Omega

/-!
Finite-domain constraints reduced to CNF using one-hot Boolean variables.
A forbidden tuple lists simultaneous variable/value equalities that may not all
hold. The translation is semantic; it makes no machine-time assertion.
-/

@[expose] public section

namespace Complexity.CSPSAT

open Complexity.SAT Complexity.Constraints

abbrev Atom (m d : Nat) := Fin m × Fin (d + 1)
abbrev ForbiddenTuple (m d : Nat) := List (Atom m d)
abbrev Instance (m d : Nat) := List (ForbiddenTuple m d)
abbrev Valuation (m d : Nat) := Fin m → Fin (d + 1)

def TupleSatisfied {m d : Nat} (v : Valuation m d) (t : ForbiddenTuple m d) : Prop :=
  ∃ atom ∈ t, v atom.1 ≠ atom.2

def Satisfied {m d : Nat} (v : Valuation m d) (problem : Instance m d) : Prop :=
  ∀ t ∈ problem, TupleSatisfied v t

def atomIndex {m d : Nat} (atom : Atom m d) : Nat :=
  atom.1.val * (d + 1) + atom.2.val

theorem atomIndex_injective {m d : Nat} {x y : Atom m d}
    (h : atomIndex x = atomIndex y) : x = y := by
  obtain ⟨i, j⟩ := x
  obtain ⟨i', j'⟩ := y
  simp only [atomIndex] at h
  have hi : i.val = i'.val := by
    by_cases heq : i.val = i'.val
    · exact heq
    have hord : i.val < i'.val ∨ i'.val < i.val := by omega
    rcases hord with hlt | hgt
    · have hm := Nat.mul_le_mul_right (d + 1) (Nat.succ_le_of_lt hlt)
      simp only [Nat.succ_mul] at hm
      have hj := j.isLt
      have hj' := j'.isLt
      omega
    · have hm := Nat.mul_le_mul_right (d + 1) (Nat.succ_le_of_lt hgt)
      simp only [Nat.succ_mul] at hm
      have hj := j.isLt
      have hj' := j'.isLt
      omega
  have hi' : i = i' := Fin.ext hi
  subst i'
  have hj : j = j' := Fin.ext (by omega)
  subst j'
  rfl

theorem atomIndex_lt {m d : Nat} (atom : Atom m d) :
    atomIndex atom < m * (d + 1) := by
  have hm := Nat.mul_le_mul_right (d + 1) (Nat.succ_le_of_lt atom.1.isLt)
  simp only [Nat.succ_mul] at hm
  have hj := atom.2.isLt
  simp only [atomIndex]
  omega

def rowVariables {m : Nat} (d : Nat) (i : Fin m) : List Nat :=
  (List.finRange (d + 1)).map (fun j => atomIndex (i, j))

@[simp] theorem rowVariables_length {m d : Nat} (i : Fin m) :
    (rowVariables d i).length = d + 1 := by simp [rowVariables]

def oneHotCNF (m d : Nat) : CNF :=
  (List.finRange m).flatMap (fun i => exactlyOne (rowVariables d i))

def forbiddenClause {m d : Nat} (t : ForbiddenTuple m d) : Clause :=
  t.map (fun atom => ⟨atomIndex atom, false⟩)

def encode {m d : Nat} (problem : Instance m d) : CNF :=
  oneHotCNF m d ++ problem.map forbiddenClause

theorem countTrue_eq_filter_length (a : Assignment) (variables : List Nat) :
    countTrue a variables = (variables.filter a).length := by
  induction variables with
  | nil => rfl
  | cons v rest ih => cases h : a v <;> simp [countTrue, h, ih, Nat.add_comm]

theorem countTrue_map {α : Type} (a : Assignment) (f : α → Nat) (xs : List α) :
    countTrue a (xs.map f) = xs.countP (fun x => a (f x)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [countTrue, List.countP_cons, ih, Nat.add_comm]

theorem countTrue_one_exists (a : Assignment) (variables : List Nat)
    (h : countTrue a variables = 1) : ∃ v ∈ variables, a v = true := by
  rw [countTrue_eq_filter_length] at h
  obtain ⟨v, hv⟩ := List.length_eq_one_iff.mp h
  have hm : v ∈ variables.filter a := by rw [hv]; simp
  exact ⟨v, List.mem_filter.mp hm⟩

theorem countTrue_one_unique (a : Assignment) (variables : List Nat)
    (h : countTrue a variables = 1) {x y : Nat}
    (hx : x ∈ variables) (hy : y ∈ variables) (hax : a x = true) (hay : a y = true) :
    x = y := by
  rw [countTrue_eq_filter_length] at h
  obtain ⟨v, hv⟩ := List.length_eq_one_iff.mp h
  have hx' : x ∈ variables.filter a := List.mem_filter.mpr ⟨hx, hax⟩
  have hy' : y ∈ variables.filter a := List.mem_filter.mpr ⟨hy, hay⟩
  rw [hv] at hx' hy'
  have hxv : x = v := by simpa using hx'
  have hyv : y = v := by simpa using hy'
  exact hxv.trans hyv.symm

theorem evalCNF_flatMap_iff {α : Type} (a : Assignment) (f : α → CNF) (xs : List α) :
    evalCNF a (xs.flatMap f) = true ↔ ∀ x ∈ xs, evalCNF a (f x) = true := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [List.flatMap_cons, evalCNF_append, Bool.and_eq_true, ih]

theorem oneHotCNF_correct (a : Assignment) (m d : Nat) :
    evalCNF a (oneHotCNF m d) = true ↔
      ∀ i : Fin m, countTrue a (rowVariables d i) = 1 := by
  simp [oneHotCNF, evalCNF_flatMap_iff, exactlyOne_correct, List.mem_finRange]

theorem forbiddenClause_correct {m d : Nat} (a : Assignment) (t : ForbiddenTuple m d) :
    evalClause a (forbiddenClause t) = true ↔
      ∃ atom ∈ t, a (atomIndex atom) = false := by
  simp [forbiddenClause, evalClause, List.any_map, List.any_eq_true, evalLiteral]

theorem encode_correct {m d : Nat} (a : Assignment) (problem : Instance m d) :
    evalCNF a (encode problem) = true ↔
      (∀ i : Fin m, countTrue a (rowVariables d i) = 1) ∧
      (∀ t ∈ problem, ∃ atom ∈ t, a (atomIndex atom) = false) := by
  simp only [encode, evalCNF_append, Bool.and_eq_true, oneHotCNF_correct]
  congr 1
  simp [evalCNF, List.all_map, forbiddenClause_correct]

/-- The Boolean assignment associated to a finite-domain valuation. -/
def assignmentOf {m d : Nat} (v : Valuation m d) : Assignment := fun n =>
  (List.finRange m).any (fun i => decide (atomIndex (i, v i) = n))

@[simp] theorem assignmentOf_atom {m d : Nat} (v : Valuation m d) (atom : Atom m d) :
    assignmentOf v (atomIndex atom) = true ↔ v atom.1 = atom.2 := by
  simp only [assignmentOf, List.any_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨i, _, h⟩
    have heq := atomIndex_injective h
    cases heq
    rfl
  · intro h
    refine ⟨atom.1, List.mem_finRange _, ?_⟩
    cases atom
    simp_all

theorem assignmentOf_atom_eq {m d : Nat} (v : Valuation m d) (atom : Atom m d) :
    assignmentOf v (atomIndex atom) = decide (v atom.1 = atom.2) := by
  apply Bool.eq_iff_iff.mpr
  simp

theorem assignmentOf_oneHot {m d : Nat} (v : Valuation m d) (i : Fin m) :
    countTrue (assignmentOf v) (rowVariables d i) = 1 := by
  rw [rowVariables, countTrue_map]
  simp only [assignmentOf_atom_eq]
  have hc := (List.nodup_finRange (d + 1)).count_of_mem (List.mem_finRange (v i))
  have hf : (fun x : Fin (d + 1) => x == v i) = (fun x => decide (v i = x)) := by
    funext x
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq, decide_eq_true_eq]
    exact eq_comm
  rw [List.count_eq_countP, hf] at hc
  exact hc

theorem valuation_satisfies_encode {m d : Nat} (v : Valuation m d)
    (problem : Instance m d) (h : Satisfied v problem) :
    evalCNF (assignmentOf v) (encode problem) = true := by
  apply (encode_correct _ _).mpr
  refine ⟨assignmentOf_oneHot v, ?_⟩
  intro t ht
  obtain ⟨atom, hatom, hne⟩ := h t ht
  refine ⟨atom, hatom, ?_⟩
  rw [assignmentOf_atom_eq]
  simp [hne]

theorem row_has_value {m d : Nat} (a : Assignment)
    (h : ∀ i : Fin m, countTrue a (rowVariables d i) = 1) (i : Fin m) :
    ∃ j : Fin (d + 1), a (atomIndex (i, j)) = true := by
  obtain ⟨n, hn, ha⟩ := countTrue_one_exists a _ (h i)
  obtain ⟨j, _, hj⟩ := List.mem_map.mp hn
  exact ⟨j, hj ▸ ha⟩

noncomputable def valuationOf {m d : Nat} (a : Assignment)
    (h : ∀ i : Fin m, countTrue a (rowVariables d i) = 1) : Valuation m d :=
  fun i => Classical.choose (row_has_value a h i)

theorem valuationOf_selected {m d : Nat} (a : Assignment)
    (h : ∀ i : Fin m, countTrue a (rowVariables d i) = 1) (i : Fin m) :
    a (atomIndex (i, valuationOf a h i)) = true :=
  Classical.choose_spec (row_has_value a h i)

theorem valuationOf_atom {m d : Nat} (a : Assignment)
    (h : ∀ i : Fin m, countTrue a (rowVariables d i) = 1) (atom : Atom m d) :
    a (atomIndex atom) = true ↔ valuationOf a h atom.1 = atom.2 := by
  constructor
  · intro hatom
    have hm₁ : atomIndex (atom.1, valuationOf a h atom.1) ∈ rowVariables d atom.1 :=
      List.mem_map.mpr ⟨_, List.mem_finRange _, rfl⟩
    have hm₂ : atomIndex atom ∈ rowVariables d atom.1 :=
      List.mem_map.mpr ⟨atom.2, List.mem_finRange _, rfl⟩
    have heq := countTrue_one_unique a _ (h atom.1) hm₁ hm₂
      (valuationOf_selected a h atom.1) hatom
    exact congrArg Prod.snd (atomIndex_injective heq)
  · intro heq
    have hs := valuationOf_selected a h atom.1
    simpa [heq] using hs

theorem assignment_satisfies_instance {m d : Nat} (a : Assignment)
    (problem : Instance m d) (ha : evalCNF a (encode problem) = true) :
    ∃ v : Valuation m d, Satisfied v problem := by
  obtain ⟨hrows, htuples⟩ := (encode_correct a problem).mp ha
  refine ⟨valuationOf a hrows, ?_⟩
  intro t ht
  obtain ⟨atom, hatom, hafalse⟩ := htuples t ht
  refine ⟨atom, hatom, ?_⟩
  intro heq
  have hatrue := (valuationOf_atom a hrows atom).mpr heq
  simp [hafalse] at hatrue

theorem satisfiable_encode_iff {m d : Nat} (problem : Instance m d) :
    Satisfiable (encode problem) ↔ ∃ v : Valuation m d, Satisfied v problem := by
  constructor
  · rintro ⟨a, ha⟩
    exact assignment_satisfies_instance a problem ha
  · rintro ⟨v, hv⟩
    exact ⟨assignmentOf v, valuation_satisfies_encode v problem hv⟩

@[simp] theorem forbiddenClause_length {m d : Nat} (t : ForbiddenTuple m d) :
    (forbiddenClause t).length = t.length := by simp [forbiddenClause]

theorem flatMap_length_le {α β : Type} (xs : List α) (f : α → List β) (bound : Nat)
    (h : ∀ x ∈ xs, (f x).length ≤ bound) :
    (xs.flatMap f).length ≤ xs.length * bound := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx := h x (by simp)
    have hr : ∀ y ∈ xs, (f y).length ≤ bound := by
      intro y hy
      exact h y (by simp [hy])
    have ht := ih hr
    simp only [List.flatMap_cons, List.length_append, List.length_cons, Nat.add_mul,
      Nat.one_mul]
    omega

theorem oneHotCNF_length_le (m d : Nat) :
    (oneHotCNF m d).length ≤ m * ((d + 1) * (d + 1) + 1) := by
  have h := flatMap_length_le (List.finRange m)
    (fun i => exactlyOne (rowVariables d i)) ((d + 1) * (d + 1) + 1) (by
      intro i _
      simpa using exactlyOne_length_le (rowVariables d i))
  simpa [oneHotCNF] using h

theorem encode_length_le {m d : Nat} (problem : Instance m d) :
    (encode problem).length ≤ m * ((d + 1) * (d + 1) + 1) + problem.length := by
  have h := oneHotCNF_length_le m d
  simp only [encode, List.length_append, List.length_map]
  omega

/-- Total number of atoms in the forbidden tuples. -/
def instanceSize {m d : Nat} : Instance m d → Nat
  | [] => 0
  | t :: rest => t.length + instanceSize rest

theorem forbiddenClauses_literalCount {m d : Nat} (problem : Instance m d) :
    literalCount (problem.map forbiddenClause) = instanceSize problem := by
  induction problem with
  | nil => rfl
  | cons t rest ih => simp [literalCount, instanceSize, ih]

theorem flatMap_literalCount_le {α : Type} (xs : List α) (f : α → CNF) (bound : Nat)
    (h : ∀ x ∈ xs, literalCount (f x) ≤ bound) :
    literalCount (xs.flatMap f) ≤ xs.length * bound := by
  induction xs with
  | nil => simp [literalCount]
  | cons x xs ih =>
    have hx := h x (by simp)
    have hr : ∀ y ∈ xs, literalCount (f y) ≤ bound := by
      intro y hy
      exact h y (by simp [hy])
    have ht := ih hr
    simp only [List.flatMap_cons, literalCount_append, List.length_cons, Nat.add_mul,
      Nat.one_mul]
    omega

theorem oneHotCNF_literalCount_le (m d : Nat) :
    literalCount (oneHotCNF m d) ≤ m * ((d + 1) + 2 * ((d + 1) * (d + 1))) := by
  have h := flatMap_literalCount_le (List.finRange m)
    (fun i => exactlyOne (rowVariables d i)) ((d + 1) + 2 * ((d + 1) * (d + 1))) (by
      intro i _
      simpa using exactlyOne_literalCount_le (rowVariables d i))
  simpa [oneHotCNF] using h

theorem encode_literalCount_le {m d : Nat} (problem : Instance m d) :
    literalCount (encode problem) ≤
      m * ((d + 1) + 2 * ((d + 1) * (d + 1))) + instanceSize problem := by
  have h := oneHotCNF_literalCount_le m d
  simp only [encode, literalCount_append, forbiddenClauses_literalCount]
  omega

theorem positiveClause_variable_mem (variables : List Nat) {l : Literal}
    (h : l ∈ positiveClause variables) : l.var ∈ variables := by
  induction variables with
  | nil => simp [positiveClause] at h
  | cons v rest ih =>
      simp only [positiveClause, List.mem_cons] at h
      rcases h with rfl | h
      · simp
      · exact List.mem_cons_of_mem v (ih h)

theorem excludeWith_variable_mem (v : Nat) (variables : List Nat)
    {c : Clause} {l : Literal} (hc : c ∈ excludeWith v variables) (hl : l ∈ c) :
    l.var = v ∨ l.var ∈ variables := by
  induction variables with
  | nil => simp [excludeWith] at hc
  | cons w rest ih =>
      simp only [excludeWith, List.mem_cons] at hc
      rcases hc with rfl | hc
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
        rcases hl with rfl | rfl <;> simp
      · rcases ih hc with heq | hm
        · exact Or.inl heq
        · exact Or.inr (List.mem_cons_of_mem w hm)

theorem atMostOne_variable_mem (variables : List Nat) {c : Clause} {l : Literal}
    (hc : c ∈ atMostOne variables) (hl : l ∈ c) : l.var ∈ variables := by
  induction variables with
  | nil => simp [atMostOne] at hc
  | cons v rest ih =>
      simp only [atMostOne, List.mem_append] at hc
      rcases hc with hc | hc
      · rcases excludeWith_variable_mem v rest hc hl with heq | hm
        · simp [heq]
        · exact List.mem_cons_of_mem v hm
      · exact List.mem_cons_of_mem v (ih hc)

theorem exactlyOne_variable_mem (variables : List Nat) {c : Clause} {l : Literal}
    (hc : c ∈ exactlyOne variables) (hl : l ∈ c) : l.var ∈ variables := by
  simp only [exactlyOne, List.mem_cons] at hc
  rcases hc with rfl | hc
  · exact positiveClause_variable_mem variables hl
  · exact atMostOne_variable_mem variables hc hl

theorem oneHotCNF_variables_lt (m d : Nat) {c : Clause} {l : Literal}
    (hc : c ∈ oneHotCNF m d) (hl : l ∈ c) : l.var < m * (d + 1) := by
  obtain ⟨i, _, hi⟩ := List.mem_flatMap.mp hc
  have hm := exactlyOne_variable_mem (rowVariables d i) hi hl
  obtain ⟨j, _, hj⟩ := List.mem_map.mp hm
  rw [← hj]
  exact atomIndex_lt (i, j)

theorem forbiddenClause_variables_lt {m d : Nat} (t : ForbiddenTuple m d)
    {l : Literal} (h : l ∈ forbiddenClause t) : l.var < m * (d + 1) := by
  obtain ⟨atom, _, rfl⟩ := List.mem_map.mp h
  exact atomIndex_lt atom

/-- Every Boolean identifier is inside the rectangular one-hot array. -/
theorem encode_variables_lt {m d : Nat} (problem : Instance m d)
    {c : Clause} {l : Literal} (hc : c ∈ encode problem) (hl : l ∈ c) :
    l.var < m * (d + 1) := by
  simp only [encode, List.mem_append] at hc
  rcases hc with hc | hc
  · exact oneHotCNF_variables_lt m d hc hl
  · obtain ⟨t, _, rfl⟩ := List.mem_map.mp hc
    exact forbiddenClause_variables_lt t hl

end Complexity.CSPSAT
