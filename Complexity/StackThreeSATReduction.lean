module

public import Complexity.StackCompile
public import Complexity.StackThreeSATSemantics

/-! A total polynomial-time Karp reduction from SAT to 3-SAT, implemented by
an explicit finite one-tape transducer through the checked stack compiler. -/

@[expose] public section
namespace Complexity

/-- Polynomial runtime of the complete finite reduction program, on every word. -/
theorem stackThreeSAT_polyTime : PolyTime StackThreeSAT.reduceWord := by
  apply StackCompile.polyTime_of_stack StackThreeSAT.machine (powerBound 4096 4)
    (PolynomialBound.power 4096 4)
  intro input
  obtain ⟨out, hr, ho⟩ := StackThreeSAT.machine_runs input
  exact ⟨4096 * (input.length + 1) ^ 4, out, Nat.le_refl _, hr, ho⟩

/-- The independent implication-chain function is computed in polynomial time. -/
theorem chainThreeSAT_polyTime : PolyTime ChainThreeSAT.reduceWord :=
  polyTime_congr StackThreeSATSemantics.reduceWord_eq stackThreeSAT_polyTime

/-- A total Karp reduction, including all malformed encodings. -/
theorem sat_polyRed_threeSAT : PolyRed SAT.SAT SAT.ThreeSAT :=
  ⟨ChainThreeSAT.reduceWord, chainThreeSAT_polyTime, ChainThreeSAT.reduceWord_correct⟩

end Complexity
