module

public import Complexity.NPCompleteness
public import Complexity.RestrictedSATComplete
public import Complexity.BinarySATComplete
public import Complexity.NondeterministicEquiv
public import Complexity.PlanarSATComplete

/-!
Completed solution, loaded separately from Challenge.lean.

The imported modules prove the public targets `Complexity.sat_np_complete`,
`Complexity.threeSAT_np_complete`, `Complexity.exactThreeSAT_np_complete`,
`Complexity.leOneLeTwoSAT_np_complete`, `Complexity.binarySAT_np_complete`,
`Complexity.planarThreeSAT_np_complete`, `Complexity.cyclePlanarThreeSAT_np_complete` and
`Complexity.inNP_iff_nondeterministicPolyTime`, with exactly the statements of
Challenge.lean. Solution does not import Challenge.lean or its intentional holes.
-/
