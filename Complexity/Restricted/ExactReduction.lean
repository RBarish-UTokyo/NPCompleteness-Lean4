module

public import Complexity.Restricted.Occurrence
public import Complexity.StackTableauMachineBounds
public import Complexity.NPCompleteness

/-!
# Every NP language reduces to exactly-3-SAT

Cook–Levin gives, for every NP language, a first-order clause program emitting an
equisatisfiable CNF formula; `exactProgram` turns it into a program emitting an exactly-3
CNF formula, and the verified emitter compiler makes the reduction polynomial-time.
-/

@[expose] public section

namespace Complexity.Restricted

open StackTableauEmitter

theorem polyRed_exactThreeSAT {L : Language} (hL : InNP L) : PolyRed L SAT.ExactThreeSAT := by
  obtain ⟨P, hP⟩ := CookLevinEmitter.inNP_emitter hL
  refine ⟨fun input => SAT.encode ((exactProgram P).emit input (CookLevinEmitter.inputEnv input)),
    StackTableauEmitter.polyTime_emitter (exactProgram P), ?_⟩
  intro input
  obtain ⟨h3, hsat⟩ := exactProgram_correct P input
  rw [hP input, SAT.SAT_encode_iff, ← hsat]
  constructor
  · intro hs
    exact ⟨_, rfl, h3, hs⟩
  · rintro ⟨f, hf, _, hs⟩
    rwa [SAT.encode_injective _ _ hf] at hs

end Complexity.Restricted
