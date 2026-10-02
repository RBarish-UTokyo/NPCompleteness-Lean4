module

public import Complexity.NTM.Core
public import Complexity.StackPair
public import Complexity.StackCompile
public import Complexity.Clock
import Lean.Elab.Tactic.Omega

/-!
# From nondeterministic machines to verifiers

The verifier for a nondeterministic machine `M` decodes its input `pairWords x w`, writes
`x` on a simulated tape and simulates `M` on `x`, taking the `i`-th choice from the
certificate `w` and the choice `false` once `w` is exhausted. It accepts iff the simulated
run executes `halt true`.

No step counter is needed: if every choice list of length `p |x|` makes `M` halt, then the
simulated run halts within `p |x|` simulated steps, whatever the certificate.
-/

@[expose] public section

namespace Complexity.NTM

open StackProgram
open StackMachine (Registers set)

/-- Decode the pair, expand `x` into the right tape half, then simulate `M` with the
certificate (register 1) as choice register. -/
def verifierProgram (M : NMachine) :=
  StackProgram.seq StackPair.unpack (StackProgram.seq (StackWords.transfer (k := 6) 0 2)
    (StackProgram.seq (expand (k := 6) 2 3) (core M (k := 6) 1 4 3)))

def verifierEncoding (M : NMachine) :=
  StackPair.unpackEncoding.sum ((Encoding.fin 3).sum ((Encoding.fin 5).sum (labelEncoding M)))

def verifierStack (M : NMachine) : StackMachine.Machine :=
  compile (verifierProgram M) (verifierEncoding M)

/-- The verifier as a single-tape machine. -/
def verifierMachine (M : NMachine) : Machine := StackCompile.compile (verifierStack M)

/-- The time bound of the stack verifier for a machine whose paths all halt within
`bound`. -/
def verifierTime (bound : Nat → Nat) (n : Nat) : Nat := 9 * n + 14 + 5 * bound n

theorem verifier_stack_runs (M : NMachine) (bound : Nat → Nat)
    (hmono : ∀ n m, n ≤ m → bound n ≤ bound m)
    (htotal : ∀ x y : List Bool, ∃ b out, runD M (bound x.length) y M.start (Tape.ofInput x) =
      some (b, out))
    (word : List Bool) :
    ∃ time decision registers, time ≤ verifierTime bound word.length ∧
      StackMachine.runInput (verifierStack M) time word = some (decision, registers) ∧
      ∀ x y, word = pairWords x y →
        (decision = true ↔
          ∃ tape, runD M (bound x.length) y M.start (Tape.ofInput x) = some (true, tape)) := by
  obtain ⟨t, out, ht, he, hout⟩ := StackPair.unpack_runs word
  cases hp : StackPair.decodePair word with
  | none =>
    rw [hp] at he
    have hf := exec_seq_failure StackPair.unpack
      (StackProgram.seq (StackWords.transfer (k := 6) 0 2)
        (StackProgram.seq (expand (k := 6) 2 3) (core M (k := 6) 1 4 3)))
      he
    refine ⟨t, false, out, ?_, compile_exec (verifierEncoding M) hf, ?_⟩
    · unfold verifierTime; omega
    · intro x y hxy
      rw [hxy, StackPair.decodePair_pairWords] at hp
      cases hp
  | some pair =>
    obtain ⟨x, y⟩ := pair
    rw [hp] at he
    have hword : word = pairWords x y := (StackPair.decodePair_eq_some_iff word x y).mp hp
    have hlen : x.length ≤ word.length := by
      rw [hword, pairWords_length]; omega
    rw [hout x y hp] at he
    have htr := StackWords.exec_transfer (k := 6) 0 2 (by decide) (StackPair.unpacked x y)
    let r₁ := set (set (StackPair.unpacked x y) 0 []) 2
      ((StackPair.unpacked x y 0).reverse ++ StackPair.unpacked x y 2)
    have hr₁ : r₁ 2 = x.reverse := by
      simp [r₁, StackPair.unpacked, StackPair.input, StackPair.certificate]
    have hex := exec_expand (k := 6) 2 3 (by decide) x.reverse r₁ hr₁
    let r₂ := set (set r₁ 2 []) 3
      (TapeToStacks.symbols (x.reverse.reverse.map Symbol.bit) ++ r₁ 3)
    obtain ⟨b, final, hrun⟩ := htotal x y
    obtain ⟨time, r', htime, hcore⟩ := core_runs M (k := 6) 1 4 3 (by decide) (by decide)
      (by decide) (bound x.length) y x b final hrun r₂
      (by simp [r₂, r₁, StackPair.unpacked, StackPair.input, StackPair.certificate])
      (by simp [r₂, r₁, StackPair.unpacked, StackPair.input, StackPair.certificate])
      (by simp [r₂, r₁, StackPair.unpacked, StackPair.input, StackPair.certificate])
    have hall := exec_seq _ _ he (exec_seq _ _ htr (exec_seq _ _ hex hcore))
    refine ⟨_, b, r', ?_, compile_exec (verifierEncoding M) hall, ?_⟩
    · have hb := hmono _ _ hlen
      have hx : (StackPair.unpacked x y 0).length = x.length := by
        simp [StackPair.unpacked, StackPair.input]
      rw [hx]
      simp only [List.length_reverse]
      unfold verifierTime
      omega
    · intro x' y' hxy
      rw [hxy, StackPair.decodePair_pairWords] at hp
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hp)
      constructor
      · intro hb
        subst hb
        exact ⟨final, hrun⟩
      · rintro ⟨tape, htape⟩
        rw [hrun] at htape
        exact (Prod.mk.inj (Option.some.inj htape)).1

theorem polynomialBound_verifierTime (c k : Nat) :
    PolynomialBound (verifierTime (powerBound c k)) := by
  have h := ((((PolynomialBound.constant 9).mul PolynomialBound.identity).add
    (PolynomialBound.constant 14)).add ((PolynomialBound.constant 5).mul
      (PolynomialBound.power c k)))
  exact h.weaken (fun n => by unfold verifierTime; exact Nat.le_refl _)

/-- The verifier of a nondeterministic polynomial-time machine runs in polynomial time and
accepts `pairWords x w` iff the run along `w`, padded by `false`, accepts. -/
theorem verifierMachine_spec (M : NMachine) (c k : Nat)
    (htotal : ∀ input : Word, ∀ choices : List Bool,
      choices.length = powerBound c k input.length →
        M.run choices M.start (Tape.ofInput input) ≠ none) :
    PolynomialTimeMachine (verifierMachine M) ∧
      ∀ x y, Accepts (verifierMachine M) (pairWords x y) ↔
        ∃ tape, M.run (padChoices (powerBound c k x.length) y) M.start (Tape.ofInput x) =
          some (true, tape) := by
  have htotal' : ∀ x y : List Bool, ∃ b out,
      runD M (powerBound c k x.length) y M.start (Tape.ofInput x) = some (b, out) := by
    intro x y
    rw [runD_eq_run]
    cases hr : M.run (padChoices (powerBound c k x.length) y) M.start (Tape.ofInput x) with
    | none => exact absurd hr (htotal x _ (padChoices_length _ _))
    | some result => exact ⟨result.1, result.2, rfl⟩
  have hruns := verifier_stack_runs M (powerBound c k) (fun n m h => powerBound_mono c k h)
    htotal'
  constructor
  · apply StackCompile.polynomialTimeMachine_of_stack (verifierStack M)
      (verifierTime (powerBound c k)) (polynomialBound_verifierTime c k)
    intro word
    obtain ⟨time, decision, registers, ht, hr, _⟩ := hruns word
    exact ⟨time, decision, registers, ht, hr⟩
  · intro x y
    obtain ⟨time, decision, registers, _, hr, hspec⟩ := hruns (pairWords x y)
    unfold verifierMachine
    rw [StackCompile.accepts_iff (verifierStack M) (pairWords x y)
      ⟨time, decision, registers, hr⟩]
    rw [← runD_eq_run]
    rw [← hspec x y rfl]
    constructor
    · rintro ⟨time', registers', hr'⟩
      have heq := StackMachine.run_deterministic (verifierStack M) _ hr hr'
      exact (Prod.mk.inj heq).1
    · intro hd
      subst hd
      exact ⟨time, registers, hr⟩

/-- Nondeterministic polynomial time is contained in NP (certificate form). -/
theorem inNP_of_nondeterministicPolyTime {L : Language} (h : NondeterministicPolyTime L) :
    InNP L := by
  obtain ⟨M, c, k, hM⟩ := h
  have htotal : ∀ input : Word, ∀ choices : List Bool,
      choices.length = powerBound c k input.length →
        M.run choices M.start (Tape.ofInput input) ≠ none := fun input => (hM input).1
  obtain ⟨hpoly, hacc⟩ := verifierMachine_spec M c k htotal
  refine ⟨verifierMachine M, c, k, hpoly, ?_⟩
  intro x
  rw [(hM x).2]
  constructor
  · rintro ⟨choices, tape, hrun⟩
    let p := powerBound c k x.length
    refine ⟨choices.take p, List.length_take_le _ _, (hacc x _).mpr ?_⟩
    by_cases hle : choices.length ≤ p
    · refine ⟨tape, ?_⟩
      rw [padChoices_eq, List.take_take, Nat.min_self, List.take_of_length_le hle]
      exact run_append M _ _ _ _ _ hrun
    · have hpad : padChoices p (choices.take p) = choices.take p := by
        rw [padChoices_eq, List.take_take, Nat.min_self, List.length_take]
        have : p - min p choices.length = 0 := by omega
        simp [this]
      rw [hpad]
      cases hr : M.run (choices.take p) M.start (Tape.ofInput x) with
      | none => exact absurd hr (htotal x _ (by simp [p]; omega))
      | some result =>
        have hall := run_append M (choices.take p) (choices.drop p) _ _ result hr
        rw [List.take_append_drop, hrun] at hall
        exact ⟨tape, hall.symm⟩
  · rintro ⟨w, _, haccept⟩
    obtain ⟨tape, hrun⟩ := (hacc x w).mp haccept
    exact ⟨_, tape, hrun⟩

end Complexity.NTM
