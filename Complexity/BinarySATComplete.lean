module

public import Complexity.Binary.ReductionSemantics
public import Complexity.Binary.VerifierMachine
public import Complexity.NPCompleteness

/-!
# SAT with binary variable indices is NP-complete

* Membership: a certificate has one bit per literal occurrence. A finite stack-machine
  verifier, compiled to a single-tape machine, parses the formula, checks that every clause
  has an occurrence whose bit agrees with its sign, and checks that occurrences naming the
  same variable (equal digit lists after removing trailing zeros) carry equal bits
  (`Complexity.Binary.VerifierMachine`).
* Hardness: a polynomial-time transducer rewrites every unary variable index in binary
  (`Complexity.Binary.ReductionSemantics`), so SAT reduces to binary SAT.
-/

@[expose] public section

namespace Complexity

/-- Binary SAT is in NP. -/
theorem binarySAT_inNP : InNP SAT.BinarySAT := Binary.binarySAT_inNP

/-- SAT reduces to binary SAT in polynomial time. -/
theorem sat_polyRed_binarySAT : PolyRed SAT.SAT SAT.BinarySAT := Binary.sat_polyRed_binarySAT

/-- Binary SAT is NP-complete. -/
theorem binarySAT_np_complete : NPComplete SAT.BinarySAT :=
  NPComplete.of_reduction sat_np_hard sat_polyRed_binarySAT binarySAT_inNP

end Complexity
