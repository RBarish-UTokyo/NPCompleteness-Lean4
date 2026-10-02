module

public import Complexity.PlanarSAT
public import Complexity.Planar.VerifierMain
public import Complexity.Planar.Reduction

/-!
# Planar 3-SAT and Lichtenstein's planar 3-SAT

NP-completeness of `SAT.PlanarThreeSAT` and `SAT.CyclePlanarThreeSAT`.

* Membership: the verifier (`Complexity.Planar.Vf.program`) receives a certificate made of
  parsing tables for the input code, a satisfying assignment and a local description of a
  planar embedding of the incidence graph (with the variable cycle for the cyclic version).
* Hardness: every NP language reduces, by two composed polynomial-time formula emitters, to a
  grid formula in Lichtenstein's style (`Complexity.Planar.Emit.cyclePlanarThreeSAT_npHard`):
  a column of crossover cells per clause along the spine, copies of the variables joined by
  nested rainbows; for the plain version the variable cycle is added as subdivided edges
  (`Complexity.Planar.Emit.planarThreeSAT_npHard`).  See `Complexity/Planar/`.
-/

@[expose] public section

namespace Complexity

open SAT

theorem planarThreeSAT_inNP : InNP SAT.PlanarThreeSAT := by
  have h : SAT.PlanarThreeSAT = fun x => ∃ f, encode f = x ∧ IsThreeCNF f ∧ Satisfiable f ∧
      PlanarGraph (Planar.targetGraph false f) := by
    funext x
    apply propext
    constructor
    · rintro ⟨f, h1, ⟨h2, h3⟩, h4⟩
      exact ⟨f, h1, h2, h4, by simpa [Planar.targetGraph] using h3⟩
    · rintro ⟨f, h1, h2, h4, h3⟩
      exact ⟨f, h1, ⟨h2, by simpa [Planar.targetGraph] using h3⟩, h4⟩
  rw [h]
  exact Planar.Vf.inNP_target false

theorem cyclePlanarThreeSAT_inNP : InNP SAT.CyclePlanarThreeSAT := by
  have h : SAT.CyclePlanarThreeSAT = fun x => ∃ f, encode f = x ∧ IsThreeCNF f ∧
      Satisfiable f ∧ PlanarGraph (Planar.targetGraph true f) := by
    funext x
    apply propext
    constructor
    · rintro ⟨f, h1, ⟨h2, h3⟩, h4⟩
      exact ⟨f, h1, h2, h4, by simpa [Planar.targetGraph] using h3⟩
    · rintro ⟨f, h1, h2, h4, h3⟩
      exact ⟨f, h1, ⟨h2, by simpa [Planar.targetGraph] using h3⟩, h4⟩
  rw [h]
  exact Planar.Vf.inNP_target true

theorem planarThreeSAT_np_complete : NPComplete SAT.PlanarThreeSAT :=
  ⟨planarThreeSAT_inNP, Planar.Emit.planarThreeSAT_npHard⟩

theorem cyclePlanarThreeSAT_np_complete : NPComplete SAT.CyclePlanarThreeSAT :=
  ⟨cyclePlanarThreeSAT_inNP, Planar.Emit.cyclePlanarThreeSAT_npHard⟩

end Complexity
