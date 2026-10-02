module

public import Complexity.Tableau
public import Complexity.InitialWord
public import Complexity.ThreeSAT
public import Complexity.Clock
import Lean.Elab.Tactic.Omega

/-!
Machine computation tableaux, using explicit finite transition trees and the
proved finite-domain CSP-to-CNF translation. These theorems connect generated
CNF satisfiability to actual bounded runs of the concrete Turing machine.
Polynomial-time implementation of the generator is a separate obligation.
-/

@[expose] public section

namespace Complexity.CookLevin

open CSPSAT LocalConstraint

def transitionSystem (M : Machine) (width : Nat) (hwidth : 0 < width) :
    Tableau.System (2 * width) (M.states + 3) :=
  FiniteRows.transitionTree M width hwidth

theorem next_encode (M : Machine) (width : Nat) (hwidth : 0 < width) (s : Status M)
    (hl : s.tape.left.length ≤ width) (hr : s.tape.right.length ≤ width) :
    Tableau.next (transitionSystem M width hwidth) (FiniteRows.encode M width s) =
      FiniteRows.encode M width (tickWindow M width s) := by
  funext i
  exact FiniteRows.eval_transitionTree M width hwidth s i hl hr

/-- The concrete finite transition trees simulate every step of the windowed
machine, not an abstract or assumed transition relation. -/
theorem iterate_encode (M : Machine) (width : Nat) (hwidth : 0 < width)
    (steps : Nat) (s : Status M)
    (hl : s.tape.left.length = width) (hr : s.tape.right.length = width) :
    Tableau.iterate (transitionSystem M width hwidth) steps (FiniteRows.encode M width s) =
      FiniteRows.encode M width (evolveWindow M width steps s) := by
  induction steps with
  | zero => rfl
  | succ steps ih =>
      rw [Tableau.iterate, ih, evolveWindow_succ_eq_tickWindow]
      have hlen := evolveWindow_lengths M width steps s ⟨hl, hr⟩
      exact next_encode M width hwidth _ (Nat.le_of_eq hlen.1) (Nat.le_of_eq hlen.2)

def initialRow (M : Machine) (width : Nat) (input : List Bool) :
    FiniteRows.Row M width :=
  FiniteRows.encode M width ((Status.running (initial M input)).window width)

theorem iterate_initialRow (M : Machine) (width : Nat) (hwidth : 0 < width)
    (steps : Nat) (input : List Bool) :
    Tableau.iterate (transitionSystem M width hwidth) steps (initialRow M width input) =
      FiniteRows.encode M width (boundedRun M width steps input) := by
  exact iterate_encode M width hwidth steps _ (by simp) (by simp)

def accepting (M : Machine) (width : Nat) : Instance (2 * width + 1) (M.states + 3) :=
  InitialWord.pin (FiniteRows.stateSlot width) (FiniteRows.decisionValue M true)

theorem accepting_correct (M : Machine) (width : Nat) (s : Status M) :
    Satisfied (FiniteRows.encode M width s) (accepting M width) ↔ s.Accepted := by
  rw [accepting, InitialWord.pin_correct, FiniteRows.encode_accepted_iff]

theorem iterate_initialRow_accepted_iff (M : Machine) (width : Nat) (hwidth : 0 < width)
    (steps : Nat) (input : List Bool) (hsize : input.length + 2 * steps ≤ width) :
    Satisfied (Tableau.iterate (transitionSystem M width hwidth) steps
      (initialRow M width input)) (accepting M width) ↔
      ∃ tape, runInput M steps input = some (true, tape) := by
  rw [iterate_initialRow, accepting_correct]
  exact boundedRun_accepted_iff M width steps input hsize

/-- Constrain an entire finite row to a specified value. -/
def pinRow {m d : Nat} (row : Valuation m d) : Instance m d :=
  (List.finRange m).flatMap (fun slot => InitialWord.pin slot (row slot))

theorem pinRow_correct {m d : Nat} (row value : Valuation m d) :
    Satisfied value (pinRow row) ↔ value = row := by
  simp only [pinRow, satisfied_flatMap_iff, List.mem_finRange, true_implies,
    InitialWord.pin_correct]
  constructor
  · exact fun h => funext h
  · intro h i
    exact congrFun h i

/-- The CNF for one fully specified binary input and an instruction horizon. -/
def fixedInputFormula (M : Machine) (width steps : Nat) (hwidth : 0 < width)
    (input : List Bool) : SAT.CNF :=
  CSPSAT.encode (Tableau.problem (transitionSystem M width hwidth) steps
    (pinRow (initialRow M width input)) (accepting M width))

theorem fixedInputFormula_correct (M : Machine) (width steps : Nat) (hwidth : 0 < width)
    (input : List Bool) (hsize : input.length + 2 * steps ≤ width) :
    SAT.Satisfiable (fixedInputFormula M width steps hwidth input) ↔
      ∃ tape, runInput M steps input = some (true, tape) := by
  rw [fixedInputFormula, Tableau.satisfiable_encode_iff]
  constructor
  · rintro ⟨row, hi, hf⟩
    have heq := (pinRow_correct _ _).mp hi
    subst row
    exact (iterate_initialRow_accepted_iff M width hwidth steps input hsize).mp hf
  · intro h
    exact ⟨initialRow M width input, (pinRow_correct _ _).mpr rfl,
      (iterate_initialRow_accepted_iff M width hwidth steps input hsize).mpr h⟩

/-- The actual verifier tableau allows an arbitrary bounded binary certificate
after a fixed prefix; its validity is enforced by explicit initial-row clauses. -/
def formula (M : Machine) (width steps : Nat) (hwidth : 0 < width)
    (pfx : List Bool) (bound : Nat) (fit : pfx.length + bound ≤ width) : SAT.CNF :=
  CSPSAT.encode (Tableau.problem (transitionSystem M width hwidth) steps
    (InitialWord.problem M width pfx bound fit) (accepting M width))

/-- Correctness of the certificate-guessing tableau, with an explicit tape
window large enough for every permitted certificate and every counted step. -/
theorem formula_correct (M : Machine) (width steps : Nat) (hwidth : 0 < width)
    (pfx : List Bool) (bound : Nat) (fit : pfx.length + bound ≤ width)
    (hsize : pfx.length + bound + 2 * steps ≤ width) :
    SAT.Satisfiable (formula M width steps hwidth pfx bound fit) ↔
      ∃ witness : List Bool, witness.length ≤ bound ∧
        ∃ tape, runInput M steps (pfx ++ witness) = some (true, tape) := by
  rw [formula, Tableau.satisfiable_encode_iff]
  constructor
  · rintro ⟨row, hi, hf⟩
    obtain ⟨witness, hw, hrow⟩ := (InitialWord.problem_iff M width pfx bound fit row).mp hi
    change row = initialRow M width (pfx ++ witness) at hrow
    subst row
    have hinput : (pfx ++ witness).length + 2 * steps ≤ width := by
      simp only [List.length_append]
      omega
    exact ⟨witness, hw,
      (iterate_initialRow_accepted_iff M width hwidth steps _ hinput).mp hf⟩
  · rintro ⟨witness, hw, tape, hrun⟩
    have hinput : (pfx ++ witness).length + 2 * steps ≤ width := by
      simp only [List.length_append]
      omega
    refine ⟨initialRow M width (pfx ++ witness), ?_, ?_⟩
    · exact (InitialWord.problem_iff M width pfx bound fit _).mpr ⟨witness, hw, rfl⟩
    · exact (iterate_initialRow_accepted_iff M width hwidth steps _ hinput).mpr ⟨tape, hrun⟩

def windowWidth (steps : Nat) (pfx : List Bool) (bound : Nat) : Nat :=
  pfx.length + bound + 2 * steps + 1

/-- A total, concrete CNF generator for bounded certificate verification. -/
def compile (M : Machine) (steps : Nat) (pfx : List Bool) (bound : Nat) : SAT.CNF :=
  formula M (windowWidth steps pfx bound) steps (by unfold windowWidth; omega)
    pfx bound (by unfold windowWidth; omega)

theorem compile_correct (M : Machine) (steps : Nat) (pfx : List Bool) (bound : Nat) :
    SAT.Satisfiable (compile M steps pfx bound) ↔
      ∃ witness : List Bool, witness.length ≤ bound ∧
        ∃ tape, runInput M steps (pfx ++ witness) = some (true, tape) := by
  apply formula_correct
  unfold windowWidth
  omega

def reduceToSAT (M : Machine) (steps : Nat) (pfx : List Bool) (bound : Nat) : SAT.Word :=
  SAT.encode (compile M steps pfx bound)

theorem reduceToSAT_correct (M : Machine) (steps : Nat) (pfx : List Bool) (bound : Nat) :
    SAT.SAT (reduceToSAT M steps pfx bound) ↔
      ∃ witness : List Bool, witness.length ≤ bound ∧
        ∃ tape, runInput M steps (pfx ++ witness) = some (true, tape) := by
  rw [reduceToSAT, SAT.SAT_encode_iff, compile_correct]

def reduceToThreeSAT (M : Machine) (steps : Nat) (pfx : List Bool) (bound : Nat) : SAT.Word :=
  SAT.encode (ThreeSAT.toThreeCNF (compile M steps pfx bound))

theorem reduceToThreeSAT_correct (M : Machine) (steps : Nat) (pfx : List Bool) (bound : Nat) :
    SAT.ThreeSAT (reduceToThreeSAT M steps pfx bound) ↔
      ∃ witness : List Bool, witness.length ≤ bound ∧
        ∃ tape, runInput M steps (pfx ++ witness) = some (true, tape) := by
  simp only [reduceToThreeSAT, SAT.ThreeSAT_encode_iff, ThreeSAT.toThreeCNF_three,
    true_and, ThreeSAT.toThreeCNF_equisatisfiable, compile_correct]

/-- The portion of the standard pair encoding that precedes its certificate. -/
def verifierPrefix (input : Word) : Word :=
  List.replicate input.length true ++ false :: input

theorem verifierPrefix_append (input witness : Word) :
    verifierPrefix input ++ witness = pairWords input witness := by
  simp [verifierPrefix, pairWords, List.append_assoc]

@[simp] theorem verifierPrefix_length (input : Word) :
    (verifierPrefix input).length = 2 * input.length + 1 := by
  simp [verifierPrefix]
  omega

def verifierSAT (M : Machine) (wc wk rc rk : Nat) (input : Word) : Word :=
  reduceToSAT M (powerBound rc rk input.length) (verifierPrefix input)
    (powerBound wc wk input.length)

def verifierThreeSAT (M : Machine) (wc wk rc rk : Nat) (input : Word) : Word :=
  reduceToThreeSAT M (powerBound rc rk input.length) (verifierPrefix input)
    (powerBound wc wk input.length)

theorem verifierSAT_correct (M : Machine) (wc wk rc rk : Nat) (input : Word) :
    SAT.SAT (verifierSAT M wc wk rc rk input) ↔
      ∃ witness : Word, witness.length ≤ powerBound wc wk input.length ∧
        ∃ tape, runInput M (powerBound rc rk input.length)
          (pairWords input witness) = some (true, tape) := by
  simp only [verifierSAT, reduceToSAT_correct, verifierPrefix_append]

theorem verifierThreeSAT_correct (M : Machine) (wc wk rc rk : Nat) (input : Word) :
    SAT.ThreeSAT (verifierThreeSAT M wc wk rc rk input) ↔
      ∃ witness : Word, witness.length ≤ powerBound wc wk input.length ∧
        ∃ tape, runInput M (powerBound rc rk input.length)
          (pairWords input witness) = some (true, tape) := by
  simp only [verifierThreeSAT, reduceToThreeSAT_correct, verifierPrefix_append]

/-- Every machine-based NP language has the correct SAT and 3-SAT instances
under these explicit tableau generators. This is a semantic result; it does not
claim polynomial-time reducibility before generator runtimes are proved. -/
theorem inNP_semantic_reductions {L : Language} (hL : InNP L) :
    ∃ M : Machine, ∃ wc wk rc rk,
      (∀ input, L input ↔ SAT.SAT (verifierSAT M wc wk rc rk input)) ∧
      (∀ input, L input ↔ SAT.ThreeSAT (verifierThreeSAT M wc wk rc rk input)) := by
  obtain ⟨M, wc, wk, tc, tk, hclock⟩ := inNP_clocked hL
  refine ⟨M, wc, wk, tc * (wc + 4) ^ tk, (wk + 1) * tk, ?_, ?_⟩
  · intro input
    exact (hclock input).trans (verifierSAT_correct M wc wk _ _ input).symm
  · intro input
    exact (hclock input).trans (verifierThreeSAT_correct M wc wk _ _ input).symm

theorem transitionSystem_leaves_le (M : Machine) (width : Nat) (hwidth : 0 < width) :
    Tableau.systemLeaves (transitionSystem M width hwidth) ≤
      (2 * width + 1) * (M.states + 4) ^ 3 := by
  have h := FiniteRows.sum_map_le_constant (List.finRange (2 * width + 1))
    (fun i => (FiniteRows.transitionTree M width hwidth i).leaves) ((M.states + 4) ^ 3)
    (fun i _ => FiniteRows.transitionTree_leaves_le M width hwidth i)
  simpa [Tableau.systemLeaves, transitionSystem] using h

end Complexity.CookLevin
