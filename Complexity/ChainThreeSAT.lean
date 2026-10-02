module

public import Complexity.SATBounds
import Lean.Elab.Tactic.Omega

/-!
# The implication-chain SAT-to-3-SAT reduction

Clauses are emitted by prepending, matching the concrete serializer. Each input
literal contributes `z_(i+1) ∨ literal ∨ ¬z_i`; endpoint units force the first
fresh variable true and the last false. All freshness intervals are explicit.
These are semantic and size theorems; runtime is proved by the stack compiler.
-/

@[expose] public section

namespace Complexity.ChainThreeSAT

open Complexity.SAT Complexity.ThreeSAT

def implicationClause (n : Nat) (l : Literal) : Clause := [pos (n + 1), l, neg n]

def chainEnd (n : Nat) : Clause → CNF
  | [] => [[neg n]]
  | l :: rest => chainEnd (n + 1) rest ++ [implicationClause n l]

def chainClause (n : Nat) (c : Clause) : CNF := chainEnd n c ++ [[pos n]]

/-- Each completed chunk is prepended to the preceding chunks. -/
def chainCNF (n : Nat) : CNF → CNF
  | [] => []
  | c :: rest => chainCNF (n + c.length + 1) rest ++ chainClause n c

theorem chainEnd_three (n : Nat) (c : Clause) : IsThreeCNF (chainEnd n c) := by
  induction c generalizing n with
  | nil => simp [chainEnd, IsThreeCNF]
  | cons l c ih =>
    intro d hd
    simp only [chainEnd, List.mem_append, List.mem_singleton] at hd
    rcases hd with hd | rfl
    · exact ih (n + 1) d hd
    · simp [implicationClause]

theorem chainClause_three (n : Nat) (c : Clause) : IsThreeCNF (chainClause n c) := by
  intro d hd
  simp only [chainClause, List.mem_append, List.mem_singleton] at hd
  rcases hd with hd | rfl
  · exact chainEnd_three n c d hd
  · simp

theorem chainCNF_three (n : Nat) (f : CNF) : IsThreeCNF (chainCNF n f) := by
  induction f generalizing n with
  | nil => simp [chainCNF, IsThreeCNF]
  | cons c rest ih =>
    intro d hd
    simp only [chainCNF, List.mem_append] at hd
    rcases hd with hd | hd
    · exact ih _ d hd
    · exact chainClause_three n c d hd

theorem chainEnd_length (n : Nat) (c : Clause) : (chainEnd n c).length = c.length + 1 := by
  induction c generalizing n with
  | nil => rfl
  | cons l c ih => simp [chainEnd, ih, Nat.add_assoc]

theorem chainClause_length (n : Nat) (c : Clause) : (chainClause n c).length = c.length + 2 := by
  simp [chainClause, chainEnd_length, Nat.add_assoc]

theorem chainCNF_length (n : Nat) (f : CNF) : (chainCNF n f).length = formulaSize f + f.length := by
  induction f generalizing n with
  | nil => rfl
  | cons c f ih =>
    simp only [chainCNF, List.length_append, chainClause_length, ih, formulaSize, List.length_cons]
    omega

theorem chainEnd_below (n : Nat) (c : Clause) (hc : ClauseBelow n c) :
    CNFBelow (n + c.length + 1) (chainEnd n c) := by
  induction c generalizing n with
  | nil => simp [chainEnd, CNFBelow, ClauseBelow, neg]
  | cons l c ih =>
    have hl : l.var < n := hc l (by simp)
    have ht : ClauseBelow (n + 1) c := by
      intro x hx
      have h := hc x (by simp [hx])
      omega
    intro d hd
    simp only [chainEnd, List.mem_append, List.mem_singleton] at hd
    rcases hd with hd | rfl
    · have hh := ih (n + 1) ht d hd
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hh
    · intro x hx
      simp only [implicationClause, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> simp [pos, neg] <;> omega

theorem chainClause_below (n : Nat) (c : Clause) (hc : ClauseBelow n c) :
    CNFBelow (n + c.length + 1) (chainClause n c) := by
  intro d hd
  simp only [chainClause, List.mem_append, List.mem_singleton] at hd
  rcases hd with hd | rfl
  · exact chainEnd_below n c hc d hd
  · simp [ClauseBelow, pos]
    omega

theorem chainEnd_sound (n : Nat) (c : Clause) (a : Assignment)
    (hs : evalCNF a (chainEnd n c) = true) (hn : a n = true) : evalClause a c = true := by
  induction c generalizing n with
  | nil => simp [chainEnd, hn] at hs
  | cons l c ih =>
    have hh : evalCNF a (chainEnd (n + 1) c) = true ∧
        evalClause a (implicationClause n l) = true := by
      simpa [chainEnd, evalCNF_append, Bool.and_eq_true] using hs
    have htail := ih (n + 1) hh.1
    simp only [implicationClause, evalClause_cons, evalClause_nil, eval_pos, eval_neg,
      hn, Bool.not_true, Bool.or_false] at hh
    cases hv : evalLiteral a l with
    | true => simp [hv]
    | false =>
      have hnext : a (n + 1) = true := by simpa [hv] using hh.2
      simp [hv, htail hnext]

theorem chainClause_sound (n : Nat) (c : Clause) (a : Assignment)
    (hs : evalCNF a (chainClause n c) = true) : evalClause a c = true := by
  have hh : evalCNF a (chainEnd n c) = true ∧ a n = true := by
    simpa [chainClause, evalCNF_append, Bool.and_eq_true] using hs
  exact chainEnd_sound n c a hh.1 hh.2

/-- The initial fresh variable records the disjunction of the original clause. -/
theorem chainEnd_complete (n : Nat) (c : Clause) (a : Assignment) (hc : ClauseBelow n c) :
    ∃ b, AgreesBelow n a b ∧ b n = evalClause a c ∧ evalCNF b (chainEnd n c) = true := by
  induction c generalizing n a with
  | nil =>
    let b : Assignment := fun i => if i = n then false else a i
    refine ⟨b, ?_, ?_, ?_⟩
    · intro i hi; simp [b, Nat.ne_of_lt hi]
    · simp [b]
    · simp [chainEnd, b]
  | cons l c ih =>
    have hl : l.var < n := hc l (by simp)
    have ht : ClauseBelow n c := by intro x hx; exact hc x (by simp [hx])
    let a' : Assignment := fun i => if i = n then evalClause a (l :: c) else a i
    have hagree : AgreesBelow n a a' := by
      intro i hi; simp [a', Nat.ne_of_lt hi]
    have ht' : ClauseBelow (n + 1) c := by
      intro x hx; have hh := ht x hx; omega
    obtain ⟨b, hab, hbNext, hbTail⟩ := ih (n + 1) a' ht'
    have hfinalAgree : AgreesBelow n a b := by
      intro i hi; exact (hagree i hi).trans (hab i (by omega))
    have hbStart : b n = evalClause a (l :: c) := by
      rw [← hab n (by omega)]
      simp [a']
    have hbNext' : b (n + 1) = evalClause a c := by
      rw [hbNext, ← evalClause_agrees ht hagree]
    have hbLit : evalLiteral b l = evalLiteral a l := by
      simp [evalLiteral, ← hfinalAgree l.var hl]
    refine ⟨b, hfinalAgree, hbStart, ?_⟩
    have himp : evalClause b (implicationClause n l) = true := by
      simp only [implicationClause, evalClause_cons, evalClause_nil, eval_pos, eval_neg,
        Bool.or_false, hbNext', hbStart, hbLit]
      cases evalLiteral a l <;> cases evalClause a c <;> rfl
    simp [chainEnd, evalCNF_append, hbTail, himp]

theorem chainClause_complete (n : Nat) (c : Clause) (a : Assignment)
    (hc : ClauseBelow n c) (ha : evalClause a c = true) :
    ∃ b, AgreesBelow n a b ∧ evalCNF b (chainClause n c) = true := by
  obtain ⟨b, hab, hb, hs⟩ := chainEnd_complete n c a hc
  refine ⟨b, hab, ?_⟩
  simp [chainClause, evalCNF_append, hs, hb, ha]

theorem chainCNF_below (n : Nat) (f : CNF) (hf : CNFBelow n f) :
    CNFBelow (n + formulaSize f) (chainCNF n f) := by
  induction f generalizing n with
  | nil => simp [chainCNF, CNFBelow]
  | cons c rest ih =>
    have hc : ClauseBelow n c := hf c (by simp)
    have ht : CNFBelow (n + c.length + 1) rest := by
      intro d hd l hl
      have hh := hf d (by simp [hd]) l hl
      omega
    have htail := ih (n + c.length + 1) ht
    have hhead := chainClause_below n c hc
    intro d hd l hl
    simp only [chainCNF, List.mem_append] at hd
    rcases hd with hd | hd
    · have hh := htail d hd l hl
      simp only [formulaSize]
      omega
    · have hh := hhead d hd l hl
      simp only [formulaSize]
      omega

theorem chainCNF_sound (n : Nat) (f : CNF) (a : Assignment)
    (hs : evalCNF a (chainCNF n f) = true) : evalCNF a f = true := by
  induction f generalizing n with
  | nil => rfl
  | cons c rest ih =>
    have hh : evalCNF a (chainCNF (n + c.length + 1) rest) = true ∧
        evalCNF a (chainClause n c) = true := by
      simpa [chainCNF, evalCNF_append, Bool.and_eq_true] using hs
    simp only [evalCNF_cons, Bool.and_eq_true]
    exact ⟨chainClause_sound n c a hh.2, ih _ hh.1⟩

theorem chainCNF_complete (n : Nat) (f : CNF) (a : Assignment)
    (hf : CNFBelow n f) (ha : evalCNF a f = true) :
    ∃ b, AgreesBelow n a b ∧ evalCNF b (chainCNF n f) = true := by
  induction f generalizing n a with
  | nil => exact ⟨a, by intro i hi; rfl, rfl⟩
  | cons c rest ih =>
    have hc : ClauseBelow n c := hf c (by simp)
    have hr : CNFBelow n rest := by intro d hd; exact hf d (by simp [hd])
    have hp : evalClause a c = true ∧ evalCNF a rest = true := by
      simpa only [evalCNF_cons, Bool.and_eq_true] using ha
    obtain ⟨b, hab, hb⟩ := chainClause_complete n c a hc hp.1
    have hrest : evalCNF b rest = true := by
      rw [← evalCNF_agrees hr hab]
      exact hp.2
    have hrnext : CNFBelow (n + c.length + 1) rest := by
      intro d hd l hl
      have hh := hr d hd l hl
      omega
    obtain ⟨d, hbd, hd⟩ := ih (n + c.length + 1) b hrnext hrest
    refine ⟨d, ?_, ?_⟩
    · intro i hi
      exact (hab i hi).trans (hbd i (by omega))
    · have hhead : evalCNF d (chainClause n c) = true := by
        rw [← evalCNF_agrees (chainClause_below n c hc) hbd]
        exact hb
      simp [chainCNF, evalCNF_append, hd, hhead]

theorem chainCNF_equisatisfiable (n : Nat) (f : CNF) (hf : CNFBelow n f) :
    Satisfiable (chainCNF n f) ↔ Satisfiable f := by
  constructor
  · intro ⟨a, ha⟩
    exact ⟨a, chainCNF_sound n f a ha⟩
  · intro ⟨a, ha⟩
    obtain ⟨b, _, hb⟩ := chainCNF_complete n f a hf ha
    exact ⟨b, hb⟩

theorem decoded_below_length {input : Word} {f : CNF} (hd : decode input = some f) :
    CNFBelow input.length f := by
  have hin := (Complexity.SAT.decode_eq_some_iff input f).mp hd
  have hb := SATBounds.variableBound_le_encode_length f
  rw [hin]
  intro c hc l hl
  have hv := input_below_bound f c hc l hl
  omega

/-- Runtime allocates fresh variables beginning at the entire encoded input length. -/
def reduceWord (input : Word) : Word :=
  match decode input with
  | none => encode [[]]
  | some f => encode (chainCNF input.length f)

theorem reduceWord_correct (input : Word) :
    SAT input ↔ SAT.ThreeSAT (reduceWord input) := by
  cases hd : decode input with
  | none =>
    simp [SAT_iff_decode, hd, reduceWord, Satisfiable, evalCNF, evalClause]
  | some f =>
    have hs := chainCNF_equisatisfiable input.length f (decoded_below_length hd)
    simp [SAT_iff_decode, hd, reduceWord, ThreeSAT_encode_iff, chainCNF_three, hs]

theorem formula_length_le_size (f : CNF) : f.length ≤ formulaSize f := by
  induction f with
  | nil => exact Nat.le_refl 0
  | cons c f ih => simp only [List.length_cons, formulaSize]; omega

/-- The concrete unary serialization has a quadratic output-size bound. -/
theorem reduceWord_length (input : Word) :
    (reduceWord input).length ≤ (6 * input.length + 8) * (2 * input.length) + 3 := by
  cases hd : decode input with
  | none => simp [reduceWord, hd, encode, encodeClause, writeList, writeValues, writeNat]
  | some f =>
    have hin := (Complexity.SAT.decode_eq_some_iff input f).mp hd
    have hsize : formulaSize f ≤ input.length := by
      rw [hin]
      exact SATBounds.formulaSize_le_encode_length f
    have hcount := formula_length_le_size f
    have hout := SATBounds.encode_three_length_le (input.length + formulaSize f)
      (chainCNF input.length f) (chainCNF_below input.length f (decoded_below_length hd))
      (chainCNF_three input.length f)
    rw [chainCNF_length] at hout
    have hp := Nat.mul_le_mul (show 3 * (input.length + formulaSize f) + 8 ≤ 6 * input.length + 8 by omega)
      (show formulaSize f + f.length ≤ 2 * input.length by omega)
    simp only [reduceWord, hd]
    omega

end Complexity.ChainThreeSAT
