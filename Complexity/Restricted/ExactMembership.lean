module

public import Complexity.Restricted.CheckedVerifier

/-!
# Exactly-3-SAT is in NP

The verifier checks the exactly-3 shape with `exactCheck` and then runs the 3-SAT verifier.
-/

@[expose] public section

namespace Complexity.Restricted

theorem exactCheck_checkSpec : CheckSpec exactCheck exactModel 250 where
  writes_low := exactCheck_writes
  runs := by
    intro r hr
    obtain ⟨t, r', e, ht, _⟩ := exactCheck_spec r hr
    refine ⟨t, r', e, Nat.le_trans ht (Nat.mul_le_mul_left 250 ?_)⟩
    exact Nat.pow_le_pow_right (by omega) (by decide)

theorem exactThreeSAT_inNP : InNP SAT.ExactThreeSAT := by
  apply inNP_of_check exactCheck_checkSpec
  · rintro x hm ⟨f, rfl, _, hs⟩
    exact ⟨f, rfl, (exactModel_encode f).mp hm, hs⟩
  · rintro x ⟨f, rfl, hex, hs⟩
    refine ⟨(exactModel_encode f).mpr hex, f, rfl, ?_, hs⟩
    intro c hc
    rw [(hex c hc).1]
    exact Nat.le_refl 3

end Complexity.Restricted
