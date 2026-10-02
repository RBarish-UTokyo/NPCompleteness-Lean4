module

public import Complexity

/-!
Small downstream applications of the completed development. A new problem
must supply its own NP verifier and its own polynomial-time reduction. Those
are explicit hypotheses here, rather than proof holes or axioms.
-/

@[expose] public section

namespace Examples

open Complexity

/-- The standard SAT-based route to completeness of a new language. -/
theorem complete_from_sat (target : Language) (hmem : InNP target)
    (hred : PolyRed SAT.SAT target) : NPComplete target :=
  npComplete_of_sat_reduction hmem hred

/-- The same route, using 3-SAT as the source problem. -/
theorem complete_from_threeSAT (target : Language) (hmem : InNP target)
    (hred : PolyRed SAT.ThreeSAT target) : NPComplete target :=
  npComplete_of_threeSAT_reduction hmem hred

/-- Hardness alone needs no membership proof for the target. -/
theorem hard_from_threeSAT (target : Language)
    (hred : PolyRed SAT.ThreeSAT target) : NPHard target :=
  npHard_of_threeSAT_reduction hred

/-- A fully instantiated application: both obligations come from verified
machine constructions in this development. -/
theorem threeSAT_complete_from_sat : NPComplete SAT.ThreeSAT :=
  complete_from_sat SAT.ThreeSAT threeSAT_inNP sat_polyRed_threeSAT

/-- Cook–Levin supplies a reduction from any separately verified NP language. -/
theorem reduce_an_np_language (source : Language) (hmem : InNP source) :
    PolyRed source SAT.ThreeSAT :=
  hmem.polyRed_threeSAT

end Examples
