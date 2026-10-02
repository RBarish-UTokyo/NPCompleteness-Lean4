module

public import Complexity.Restricted.ExactMembership
public import Complexity.Restricted.ExactReduction
public import Complexity.Restricted.LeMembership
public import Complexity.Restricted.LeReduction

/-!
# NP-completeness of exactly-3-SAT and (≤1,≤2)-SAT

Membership: a verifier first checks the syntactic restriction with a stack program working
on a copy of the input (`Complexity.Restricted.exactCheck`, `Complexity.Restricted.leCheck`)
and then runs the 3-SAT verifier (`Complexity.Restricted.inNP_of_check`).

Hardness: Cook–Levin gives, for 3-SAT and for exactly-3-SAT, a first-order clause program
emitting an equisatisfiable CNF formula. A syntactic transformation of that program
(`Complexity.Restricted.occFull`) replaces every literal occurrence by its own copy variable,
splits long clauses by implication chains, and adds, for every variable, a cycle of
two-literal implications through all its copies. The result is a (≤1,≤2) formula; padding its
two-literal clauses gives an exactly-3 formula (`Complexity.Restricted.exactProgram`). The
verified emitter compiler makes both reductions polynomial-time.
-/

@[expose] public section

namespace Complexity

theorem exactThreeSAT_inNP : InNP SAT.ExactThreeSAT :=
  Restricted.exactThreeSAT_inNP

theorem threeSAT_polyRed_exactThreeSAT : PolyRed SAT.ThreeSAT SAT.ExactThreeSAT :=
  Restricted.polyRed_exactThreeSAT threeSAT_inNP

theorem exactThreeSAT_np_complete : NPComplete SAT.ExactThreeSAT :=
  NPComplete.of_reduction threeSAT_np_hard threeSAT_polyRed_exactThreeSAT exactThreeSAT_inNP

theorem leOneLeTwoSAT_inNP : InNP SAT.LeOneLeTwoSAT :=
  Restricted.leOneLeTwoSAT_inNP

theorem exactThreeSAT_polyRed_leOneLeTwoSAT : PolyRed SAT.ExactThreeSAT SAT.LeOneLeTwoSAT :=
  Restricted.polyRed_leOneLeTwoSAT exactThreeSAT_inNP

theorem leOneLeTwoSAT_np_complete : NPComplete SAT.LeOneLeTwoSAT :=
  NPComplete.of_reduction exactThreeSAT_np_complete.npHard exactThreeSAT_polyRed_leOneLeTwoSAT
    leOneLeTwoSAT_inNP

end Complexity
