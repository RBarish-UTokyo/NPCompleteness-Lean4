module

public import Complexity.Restricted.Occurrence
public import Complexity.Restricted.Counting
public import Complexity.StackTableauMachineBounds
public import Complexity.NPCompleteness

/-!
# Every NP language reduces to (≤1,≤2)-SAT

The occurrence transformation `occFull` of a program without empty and unit clauses emits a
(≤1,≤2) formula: clauses have two or three literals, and every variable occurs at most once
positively and at most twice negatively (`Complexity.Restricted.output_counts`).
-/

@[expose] public section

namespace Complexity.Restricted

open Complexity.SAT StackTableauEmitter

theorem occFull_leOneLeTwo (P : ClauseProgram 1) (input : Word)
    (hlen : ∀ c ∈ P.emit input (CookLevinEmitter.inputEnv input), 2 ≤ c.length) :
    IsLeOneLeTwoCNF ((occFull P).emit input (CookLevinEmitter.inputEnv input)) := by
  constructor
  · intro c hc
    rcases (occFull_shape P input hlen c hc).1 with h | h <;> omega
  · intro v
    rw [filter_pos_count, filter_neg_count, occFull_emit]
    exact output_counts (entries_WF P input hlen) (two_le_slotCount P input) v

/-- A (≤1,≤2) program equisatisfiable with `P`. -/
def leProgram (P : ClauseProgram 1) : ClauseProgram 1 := occFull (unitFree P)

theorem leProgram_correct (P : ClauseProgram 1) (input : Word) :
    IsLeOneLeTwoCNF ((leProgram P).emit input (CookLevinEmitter.inputEnv input)) ∧
      (Satisfiable ((leProgram P).emit input (CookLevinEmitter.inputEnv input)) ↔
        Satisfiable (P.emit input (CookLevinEmitter.inputEnv input))) := by
  have hlen := unitFree_length P input (CookLevinEmitter.inputEnv input)
  refine ⟨occFull_leOneLeTwo _ input hlen, ?_⟩
  rw [leProgram, occFull_satisfiable_iff _ _ hlen, unitFree_satisfiable_iff]

theorem polyRed_leOneLeTwoSAT {L : Language} (hL : InNP L) : PolyRed L SAT.LeOneLeTwoSAT := by
  obtain ⟨P, hP⟩ := CookLevinEmitter.inNP_emitter hL
  refine ⟨fun input => SAT.encode ((leProgram P).emit input (CookLevinEmitter.inputEnv input)),
    StackTableauEmitter.polyTime_emitter (leProgram P), ?_⟩
  intro input
  obtain ⟨hle, hsat⟩ := leProgram_correct P input
  rw [hP input, SAT.SAT_encode_iff, ← hsat]
  constructor
  · intro hs
    exact ⟨_, rfl, hle, hs⟩
  · rintro ⟨f, hf, _, hs⟩
    rwa [SAT.encode_injective _ _ hf] at hs

end Complexity.Restricted
