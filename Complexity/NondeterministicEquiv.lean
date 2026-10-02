module

public import Complexity.NTM.Verifier
public import Complexity.NTM.Guesser

/-!
# NP by verifiers equals NP by nondeterministic machines

`InNP` (polynomial-time verifiers with polynomially bounded certificates) and
`NondeterministicPolyTime` (nondeterministic machines all of whose computation paths halt
within a polynomial bound) define the same class of languages.

* `NTM.inNP_of_nondeterministicPolyTime`: the verifier simulates the nondeterministic
  machine on Boolean stacks, taking its choices from the certificate.
* `NTM.nondeterministicPolyTime_of_inNP`: the nondeterministic machine computes a unary
  clock, guesses a word of that length and runs the verifier on the decoded certificate.
-/

@[expose] public section

namespace Complexity

theorem inNP_iff_nondeterministicPolyTime (L : Language) :
    InNP L ↔ NondeterministicPolyTime L :=
  ⟨NTM.nondeterministicPolyTime_of_inNP, NTM.inNP_of_nondeterministicPolyTime⟩

end Complexity
