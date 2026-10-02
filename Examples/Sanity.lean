module

public import Complexity

/-!
# Sanity checks on the definitions of the statement

Checked facts about the definitions used in `Challenge.lean`: the encoding of
formulas is concrete and unambiguous, malformed words and trailing data are
rejected, 3-SAT is a proper restriction of SAT, and NP-hardness is not vacuous,
since an NP-hard language has both members and nonmembers. These are tests of
the statement, not steps of the proof.
-/

@[expose] public section

namespace Examples.Sanity

open Complexity Complexity.SAT

/-! ## The encoding -/

/-- The clause `¬ x 1` is coded as the length `1` (`10`), then the clause: its
length `1` (`10`), then the literal: sign `0`, index `1` (`10`). -/
example : encode [[⟨1, false⟩]] = [true, false, true, false, false, true, false] := rfl

/-- The encoding is injective, and `decode` inverts it exactly. -/
example (f g : CNF) (h : encode f = encode g) : f = g := encode_injective f g h

example (input : Complexity.Word) (f : CNF) : decode input = some f ↔ input = encode f :=
  decode_eq_some_iff input f

/-- The membership condition through the parser agrees with the definition. -/
example (input : Complexity.Word) : SAT input ↔ ∃ f, decode input = some f ∧ Satisfiable f :=
  SAT_iff_decode input

/-! ## Members and nonmembers -/

/-- `x 0 ∧ (¬ x 0 ∨ x 1)` is satisfiable. -/
example : SAT (encode [[⟨0, true⟩], [⟨0, false⟩, ⟨1, true⟩]]) :=
  (SAT_encode_iff _).mpr ⟨fun _ => true, rfl⟩

/-- `x 0 ∧ ¬ x 0` is not. -/
example : ¬ SAT (encode [[⟨0, true⟩], [⟨0, false⟩]]) := by
  rw [SAT_encode_iff]
  rintro ⟨a, h⟩
  cases ha : a 0 <;> simp [evalCNF, evalClause, evalLiteral, ha] at h

/-- The empty formula is true, and a formula with an empty clause is false. -/
example : SAT (encode []) ∧ ¬ SAT (encode [[]]) :=
  ⟨(SAT_encode_iff _).mpr satisfiable_empty,
    fun h => not_satisfiable_empty_clause [] ((SAT_encode_iff _).mp h)⟩

/-- Malformed words are rejected: the empty word codes no formula. -/
example : ¬ SAT [] := by
  rintro ⟨f, hf, -⟩
  have := congrArg List.length hf
  simp [encode, writeList] at this

/-- Trailing data is rejected. -/
example : ¬ SAT (encode [] ++ [false]) := by
  rintro ⟨f, hf, -⟩
  exact List.cons_ne_nil false [] (encode_prefix_free hf.symm).2

/-- A satisfiable clause with four literals is in SAT but not in 3-SAT. -/
example :
    SAT (encode [[⟨0, true⟩, ⟨1, true⟩, ⟨2, true⟩, ⟨3, true⟩]]) ∧
      ¬ ThreeSAT (encode [[⟨0, true⟩, ⟨1, true⟩, ⟨2, true⟩, ⟨3, true⟩]]) := by
  refine ⟨(SAT_encode_iff _).mpr ⟨fun _ => true, rfl⟩, ?_⟩
  rw [ThreeSAT_encode_iff]
  rintro ⟨h3, -⟩
  have := h3 _ (List.mem_singleton_self _)
  simp at this

/-! ## Machines and the complexity classes -/

/-- The pairing of an instance and a certificate. -/
example : pairWords [true] [false] = [true, false, true, false] := rfl

/-- A machine that halts at once accepts every input, in one step. -/
example (input : Complexity.Word) : Accepts identityMachine input := ⟨1, _, rfl⟩

/-- The identity function is computable in polynomial time. -/
example : PolyTime (fun input => input) := polyTime_id

/-- NP-hardness is not vacuous: an NP-hard language has a member and a
nonmember, because SAT reduces to it. -/
theorem NPHard.exists_mem_and_not_mem {L : Language} (h : NPHard L) :
    (∃ x, L x) ∧ ∃ x, ¬ L x := by
  obtain ⟨f, -, hf⟩ := h SAT.SAT sat_inNP
  refine ⟨⟨f (encode []), (hf _).mp ((SAT_encode_iff _).mpr satisfiable_empty)⟩,
    ⟨f (encode [[]]), fun hx => ?_⟩⟩
  exact not_satisfiable_empty_clause [] ((SAT_encode_iff _).mp ((hf _).mpr hx))

/-- In particular the empty language is not NP-hard. -/
example : ¬ NPHard (fun _ => False) := fun h => by
  obtain ⟨⟨_, hx⟩, -⟩ := NPHard.exists_mem_and_not_mem h
  exact hx

/-- Nor is the language of all words. -/
example : ¬ NPHard (fun _ => True) := fun h => by
  obtain ⟨-, ⟨_, hx⟩⟩ := NPHard.exists_mem_and_not_mem h
  exact hx trivial

end Examples.Sanity
