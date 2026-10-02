module

public import Complexity.SAT
import Lean.Elab.Tactic.Omega

/-!
# A fresh-variable reduction from CNF satisfiability to 3-CNF satisfiability

Here “3-CNF” means that each clause has at most three literals.  A clause
`a ∨ b ∨ r` is replaced by `(a ∨ b ∨ z) ∧ (¬z ∨ r)`, with a new variable `z`.
Fresh variables are allocated explicitly above all variables in the input.

The results in this file concern semantics and output size.  They do not, by
themselves, assert a running-time bound in a machine model.
-/

@[expose] public section

namespace Complexity.ThreeSAT

open Complexity.SAT

def pos (n : Nat) : Literal := ⟨n, true⟩
def neg (n : Nat) : Literal := ⟨n, false⟩

@[simp] theorem eval_pos (a : Assignment) (n : Nat) :
    evalLiteral a (pos n) = a n := by simp [pos, evalLiteral]

@[simp] theorem eval_neg (a : Assignment) (n : Nat) :
    evalLiteral a (neg n) = !(a n) := by simp [neg, evalLiteral]

def ClauseBelow (n : Nat) (c : Clause) : Prop := ∀ l ∈ c, l.var < n
def CNFBelow (n : Nat) (f : CNF) : Prop := ∀ c ∈ f, ClauseBelow n c
def AgreesBelow (n : Nat) (a b : Assignment) : Prop := ∀ i, i < n → a i = b i

theorem evalClause_agrees {n : Nat} {a b : Assignment} {c : Clause}
    (hc : ClauseBelow n c) (hab : AgreesBelow n a b) :
    evalClause a c = evalClause b c := by
  induction c with
  | nil => rfl
  | cons l rest ih =>
    have hl := hc l (by simp)
    have hr : ClauseBelow n rest := by
      intro x hx
      exact hc x (by simp [hx])
    have heq : evalLiteral a l = evalLiteral b l := by
      simp [evalLiteral, hab l.var hl]
    simp only [evalClause_cons, heq, ih hr]

theorem evalCNF_agrees {n : Nat} {a b : Assignment} {f : CNF}
    (hf : CNFBelow n f) (hab : AgreesBelow n a b) :
    evalCNF a f = evalCNF b f := by
  induction f with
  | nil => rfl
  | cons c rest ih =>
    have hc := hf c (by simp)
    have hr : CNFBelow n rest := by
      intro d hd
      exact hf d (by simp [hd])
    simp only [evalCNF_cons, evalClause_agrees hc hab, ih hr]

/-- Splitting allocates one new variable at each recursive step. -/
def splitClause (n : Nat) (c : Clause) : CNF :=
  match c with
  | [] => [[]]
  | [a] => [[a]]
  | a :: b :: rest => [a, b, pos n] :: splitClause (n + 1) (neg n :: rest)
termination_by c.length

theorem splitClause_three (n : Nat) (c : Clause) :
    IsThreeCNF (splitClause n c) := by
  cases c with
  | nil => simp [splitClause, IsThreeCNF]
  | cons a tail =>
    cases tail with
    | nil => simp [splitClause, IsThreeCNF]
    | cons b rest =>
      have ih := splitClause_three (n + 1) (neg n :: rest)
      simpa [splitClause, IsThreeCNF] using ih
termination_by c.length

/-- Every satisfying assignment of the output also satisfies the input clause. -/
theorem splitClause_sound (n : Nat) (c : Clause) (a : Assignment)
    (h : evalCNF a (splitClause n c) = true) : evalClause a c = true := by
  cases c with
  | nil => simp [splitClause, evalCNF] at h
  | cons l tail =>
    cases tail with
    | nil => simpa [splitClause, evalCNF] using h
    | cons m rest =>
      have hparts : evalClause a [l, m, pos n] = true ∧
          evalCNF a (splitClause (n + 1) (neg n :: rest)) = true := by
        simpa [splitClause, evalCNF, Bool.and_eq_true] using h
      have hrest := splitClause_sound (n + 1) (neg n :: rest) a hparts.2
      simp only [evalClause, List.any_cons, List.any_nil, Bool.or_false,
        eval_pos, eval_neg] at hparts hrest ⊢
      cases h₁ : evalLiteral a l <;> cases h₂ : evalLiteral a m <;>
        cases h₃ : a n <;> cases h₄ : rest.any (evalLiteral a) <;> simp_all
termination_by c.length

/-- Splitting only uses input variables and variables below the allocated bound. -/
theorem splitClause_below (n : Nat) (c : Clause) (hc : ClauseBelow n c) :
    CNFBelow (n + c.length + 1) (splitClause n c) := by
  cases c with
  | nil => simp [splitClause, CNFBelow, ClauseBelow]
  | cons l tail =>
    cases tail with
    | nil =>
      have hl := hc l (by simp)
      simp [splitClause, CNFBelow, ClauseBelow]
      omega
    | cons m rest =>
      have hl : l.var < n := hc l (by simp)
      have hm : m.var < n := hc m (by simp)
      have hr : ClauseBelow n rest := by
        intro x hx
        exact hc x (by simp [hx])
      have hnext : ClauseBelow (n + 1) (neg n :: rest) := by
        intro x hx
        simp only [List.mem_cons] at hx
        rcases hx with rfl | hx
        · simp [neg]
        · have := hr x hx; omega
      have ih := splitClause_below (n + 1) (neg n :: rest) hnext
      intro d hd
      simp only [splitClause, List.mem_cons] at hd
      rcases hd with rfl | hd
      · intro x hx
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl <;> simp [pos] <;> omega
      · have hh := ih d hd
        simpa [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hh
termination_by c.length

/-- A satisfying assignment extends to the freshly introduced variables. -/
theorem splitClause_complete (n : Nat) (c : Clause) (a : Assignment)
    (hc : ClauseBelow n c) (ha : evalClause a c = true) :
    ∃ b, AgreesBelow n a b ∧ evalCNF b (splitClause n c) = true := by
  cases c with
  | nil => simp [evalClause] at ha
  | cons l tail =>
    cases tail with
    | nil =>
      exact ⟨a, by intro i hi; rfl, by simpa [splitClause, evalCNF] using ha⟩
    | cons m rest =>
      have hl : l.var < n := hc l (by simp)
      have hm : m.var < n := hc m (by simp)
      have hr : ClauseBelow n rest := by
        intro x hx
        exact hc x (by simp [hx])
      let a' : Assignment := fun i => if i = n then evalClause a rest else a i
      have hagree : AgreesBelow n a a' := by
        intro i hi
        simp [a', Nat.ne_of_lt hi]
      have hat : a' n = evalClause a rest := by simp [a']
      have heq : evalClause a' rest = evalClause a rest :=
        (evalClause_agrees hr hagree).symm
      have hnext : ClauseBelow (n + 1) (neg n :: rest) := by
        intro x hx
        simp only [List.mem_cons] at hx
        rcases hx with rfl | hx
        · simp [neg]
        · have := hr x hx; omega
      have hsat : evalClause a' (neg n :: rest) = true := by
        simp only [evalClause_cons, eval_neg]
        rw [hat, heq]
        cases evalClause a rest <;> rfl
      obtain ⟨b, hb, hbsat⟩ := splitClause_complete (n + 1) (neg n :: rest) a' hnext hsat
      have hab : AgreesBelow n a b := by
        intro i hi
        exact (hagree i hi).trans (hb i (by omega))
      refine ⟨b, hab, ?_⟩
      have hleft : evalLiteral b l = evalLiteral a l := by
        simp [evalLiteral, ← hab l.var hl]
      have hmiddle : evalLiteral b m = evalLiteral a m := by
        simp [evalLiteral, ← hab m.var hm]
      have hfresh : b n = evalClause a rest := (hb n (by omega)).symm.trans hat
      have hhead : evalClause b [l, m, pos n] = true := by
        simpa [evalClause, hleft, hmiddle, hfresh] using ha
      simpa [splitClause, evalCNF, Bool.and_eq_true] using And.intro hhead hbsat
termination_by c.length

theorem splitClause_length (n : Nat) (c : Clause) :
    (splitClause n c).length ≤ c.length + 1 := by
  cases c with
  | nil => simp [splitClause]
  | cons a tail =>
    cases tail with
    | nil => simp [splitClause]
    | cons b rest =>
      have ih := splitClause_length (n + 1) (neg n :: rest)
      simp only [splitClause, List.length_cons] at ih ⊢
      omega
termination_by c.length

/-- One unit per clause plus one per literal; used to allocate disjoint intervals. -/
def formulaSize : CNF → Nat
  | [] => 0
  | c :: rest => c.length + 1 + formulaSize rest

/-- Translate clauses in order, reserving a fresh interval for each clause. -/
def splitCNF (n : Nat) : CNF → CNF
  | [] => []
  | c :: rest => splitClause n c ++ splitCNF (n + c.length + 1) rest

theorem splitCNF_three (n : Nat) (f : CNF) : IsThreeCNF (splitCNF n f) := by
  induction f generalizing n with
  | nil => simp [splitCNF, IsThreeCNF]
  | cons c rest ih =>
    intro d hd
    simp only [splitCNF, List.mem_append] at hd
    rcases hd with hd | hd
    · exact splitClause_three n c d hd
    · exact ih (n + c.length + 1) d hd

theorem splitCNF_length (n : Nat) (f : CNF) :
    (splitCNF n f).length ≤ formulaSize f := by
  induction f generalizing n with
  | nil => simp [splitCNF, formulaSize]
  | cons c rest ih =>
    have hc := splitClause_length n c
    have hr := ih (n + c.length + 1)
    simp only [splitCNF, List.length_append, formulaSize]
    omega

theorem splitCNF_sound (n : Nat) (f : CNF) (a : Assignment)
    (h : evalCNF a (splitCNF n f) = true) : evalCNF a f = true := by
  induction f generalizing n with
  | nil => rfl
  | cons c rest ih =>
    have hp : evalCNF a (splitClause n c) = true ∧
        evalCNF a (splitCNF (n + c.length + 1) rest) = true := by
      simpa [splitCNF, evalCNF_append, Bool.and_eq_true] using h
    simp only [evalCNF_cons, Bool.and_eq_true]
    exact ⟨splitClause_sound n c a hp.1, ih _ hp.2⟩

theorem splitCNF_complete (n : Nat) (f : CNF) (a : Assignment)
    (hf : CNFBelow n f) (ha : evalCNF a f = true) :
    ∃ b, AgreesBelow n a b ∧ evalCNF b (splitCNF n f) = true := by
  induction f generalizing n a with
  | nil => exact ⟨a, by intro i hi; rfl, rfl⟩
  | cons c rest ih =>
    have hc : ClauseBelow n c := hf c (by simp)
    have hr : CNFBelow n rest := by
      intro d hd
      exact hf d (by simp [hd])
    have hp : evalClause a c = true ∧ evalCNF a rest = true := by
      simpa only [evalCNF_cons, Bool.and_eq_true] using ha
    obtain ⟨b, hab, hb⟩ := splitClause_complete n c a hc hp.1
    have hrest : evalCNF b rest = true := by
      rw [← evalCNF_agrees hr hab]
      exact hp.2
    have hrnext : CNFBelow (n + c.length + 1) rest := by
      intro d hd l hl
      have := hr d hd l hl
      omega
    obtain ⟨d, hbd, hd⟩ := ih (n + c.length + 1) b hrnext hrest
    refine ⟨d, ?_, ?_⟩
    · intro i hi
      exact (hab i hi).trans (hbd i (by omega))
    · have hhead : evalCNF d (splitClause n c) = true := by
        rw [← evalCNF_agrees (splitClause_below n c hc) hbd]
        exact hb
      simpa [splitCNF, evalCNF_append, Bool.and_eq_true] using And.intro hhead hd

/-- The complete CNF-to-3-CNF transformation starts above every input variable. -/
def toThreeCNF (f : CNF) : CNF := splitCNF (variableBound f) f

theorem input_below_bound (f : CNF) : CNFBelow (variableBound f) f := by
  intro c hc l hl
  exact Nat.lt_of_lt_of_le (literal_lt_clauseBound hl) (clauseBound_le_variableBound hc)

theorem toThreeCNF_three (f : CNF) : IsThreeCNF (toThreeCNF f) :=
  splitCNF_three (variableBound f) f

theorem toThreeCNF_equisatisfiable (f : CNF) :
    Satisfiable (toThreeCNF f) ↔ Satisfiable f := by
  constructor
  · intro ⟨a, ha⟩
    exact ⟨a, splitCNF_sound (variableBound f) f a ha⟩
  · intro ⟨a, ha⟩
    obtain ⟨b, _, hb⟩ := splitCNF_complete (variableBound f) f a (input_below_bound f) ha
    exact ⟨b, hb⟩

/-- The number of output clauses is at most the number of input literals plus clauses. -/
theorem toThreeCNF_length (f : CNF) : (toThreeCNF f).length ≤ formulaSize f :=
  splitCNF_length (variableBound f) f

/-- At most three literals in each output clause gives a linear structural bound. -/
theorem formulaSize_le_of_three (f : CNF) (hf : IsThreeCNF f) :
    formulaSize f ≤ 4 * f.length := by
  induction f with
  | nil => simp [formulaSize]
  | cons c rest ih =>
    have hc := hf c (by simp)
    have hr : IsThreeCNF rest := by
      intro d hd
      exact hf d (by simp [hd])
    have ht := ih hr
    simp only [formulaSize, List.length_cons]
    omega

theorem toThreeCNF_size (f : CNF) : formulaSize (toThreeCNF f) ≤ 4 * formulaSize f := by
  have hshape := formulaSize_le_of_three (toThreeCNF f) (toThreeCNF_three f)
  have hcount := toThreeCNF_length f
  omega

/-- A total map on encoded inputs; malformed inputs map to an unsatisfiable formula. -/
def reduceWord (input : Word) : Word :=
  match decode input with
  | none => encode [[]]
  | some f => encode (toThreeCNF f)

/-- Semantic many-one equivalence, without an unproved running-time assertion. -/
theorem reduceWord_correct (input : Word) :
    SAT input ↔ Complexity.SAT.ThreeSAT (reduceWord input) := by
  cases hd : decode input with
  | none =>
    simp [SAT, hd, reduceWord, Complexity.SAT.ThreeSAT,
      Satisfiable, evalCNF, evalClause]
  | some f =>
    simp [SAT, hd, reduceWord, ThreeSAT_encode_iff, toThreeCNF_three,
      toThreeCNF_equisatisfiable]

end Complexity.ThreeSAT
