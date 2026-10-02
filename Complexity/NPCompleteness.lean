module

public import Complexity.CookLevinEmitter
public import Complexity.StackTableauMachineBounds
public import Complexity.StackThreeSATReduction
public import Complexity.Membership
public import Complexity.Reductions

/-!
Cook–Levin and 3-SAT completeness for the concrete binary-word languages.
The reduction computes an explicit finite computation tableau using the
verified polynomial-time emitter compiler. Membership and all reductions use
the original finite single-tape machine model in `Complexity.Classes`.
-/

@[expose] public section

namespace Complexity

/-- Every machine-defined NP language admits a total polynomial-time
many-one reduction to the specified encoding of CNF satisfiability. -/
theorem InNP.polyRed_sat {L : Language} (hL : InNP L) : PolyRed L SAT.SAT := by
  obtain ⟨program, hprogram⟩ := CookLevinEmitter.inNP_emitter hL
  refine ⟨fun input => SAT.encode (program.emit input (fun _ => input.length)),
    StackTableauEmitter.polyTime_emitter program, ?_⟩
  intro input
  exact hprogram input

/-- Cook–Levin hardness, with actual polynomial-time tableau construction. -/
theorem sat_np_hard : NPHard SAT.SAT := by
  intro L hL
  exact hL.polyRed_sat

/-- Encoded CNF satisfiability is NP-complete. -/
theorem sat_np_complete : NPComplete SAT.SAT :=
  ⟨sat_inNP, sat_np_hard⟩

/-- Every machine-defined NP language reduces in polynomial time to encoded
3-CNF satisfiability, with clauses containing at most three literals. -/
theorem InNP.polyRed_threeSAT {L : Language} (hL : InNP L) :
    PolyRed L SAT.ThreeSAT :=
  hL.polyRed_sat.trans sat_polyRed_threeSAT

theorem threeSAT_np_hard : NPHard SAT.ThreeSAT := by
  intro L hL
  exact hL.polyRed_threeSAT

/-- Encoded 3-CNF satisfiability is NP-complete. -/
theorem threeSAT_np_complete : NPComplete SAT.ThreeSAT :=
  ⟨threeSAT_inNP, threeSAT_np_hard⟩

/-- A polynomial-time reduction from SAT proves hardness of its destination. -/
theorem npHard_of_sat_reduction {L : Language} (h : PolyRed SAT.SAT L) :
    NPHard L :=
  sat_np_hard.of_reduction h

/-- SAT provides a reusable source problem for downstream completeness proofs. -/
theorem npComplete_of_sat_reduction {L : Language} (hL : InNP L)
    (h : PolyRed SAT.SAT L) : NPComplete L :=
  sat_np_complete.transfer h hL

/-- A polynomial-time reduction from 3-SAT proves hardness of its destination. -/
theorem npHard_of_threeSAT_reduction {L : Language} (h : PolyRed SAT.ThreeSAT L) :
    NPHard L :=
  threeSAT_np_hard.of_reduction h

/-- 3-SAT provides a reusable source problem for downstream completeness proofs. -/
theorem npComplete_of_threeSAT_reduction {L : Language} (hL : InNP L)
    (h : PolyRed SAT.ThreeSAT L) : NPComplete L :=
  threeSAT_np_complete.transfer h hL

end Complexity
