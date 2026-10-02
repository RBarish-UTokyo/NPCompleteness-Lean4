module

public import Complexity.OneHotEmitter
public import Complexity.InitialEmitter
public import Complexity.TransitionEmitter
public import Complexity.FinalEmitter
public import Complexity.CookLevin

/-!
A fixed first-order clause program for every polynomially clocked verifier.
This assembles one-hot, initial, local-transition and accepting constraints.
The immutable syntax is suitable for the verified finite-stack compiler.
-/

@[expose] public section

namespace Complexity.CookLevinEmitter

open StackTableauEmitter

def program {n : Nat} (M : Machine) (width inputLength bound steps : NumExpr n) :
    ClauseProgram n :=
  .seq (OneHotEmitter.program (M.states + 3) ((steps + 1) * (2 * width + 1)))
    (.seq (InitialEmitter.program M width inputLength bound)
      (.seq (TransitionEmitter.program M width steps) (FinalEmitter.program M width steps)))


theorem program_correct {n : Nat} (M : Machine)
    (width inputLength bound steps : NumExpr n) (input : Word) (env : Env n)
    (hN : inputLength.eval env = input.length) (hw : 0 < width.eval env)
    (fit : (CookLevin.verifierPrefix input).length + bound.eval env ≤ width.eval env) :
    Equivalent ((program M width inputLength bound steps).emit input env)
      (CookLevin.formula M (width.eval env) (steps.eval env) hw
        (CookLevin.verifierPrefix input) (bound.eval env) fit) := by
  have ho := OneHotEmitter.program_correct (M.states + 3)
    ((steps + 1) * (2 * width + 1)) input env
  have hi := InitialEmitter.program_correct M width inputLength bound input env hN fit
  have ht := TransitionEmitter.emit_program M width steps input env hw rfl rfl
  have hf : Equivalent ((FinalEmitter.program M width steps).emit input env)
      ((Tableau.mapInstance (Tableau.cell (Fin.last (steps.eval env)))
        (CookLevin.accepting M (width.eval env))).map CSPSAT.forbiddenClause) := by
    rw [FinalEmitter.program_correct]
    exact Equivalent.refl _
  simpa only [program, ClauseProgram.emit_seq, NumExpr.eval, CookLevin.formula,
    CSPSAT.encode, Tableau.problem, List.map_append, forbiddenClauses_mapInstance_zero,
    CookLevin.transitionSystem] using ho.append (hi.append (ht.append hf))

def powerExpr {n : Nat} (base : NumExpr n) : Nat → NumExpr n
  | 0 => .const 1
  | k + 1 => .mul (powerExpr base k) base

@[simp] theorem eval_powerExpr {n : Nat} (base : NumExpr n) (k : Nat) (env : Env n) :
    (powerExpr base k).eval env = base.eval env ^ k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [powerExpr, NumExpr.eval, Nat.pow_succ, ih]

def boundExpr (coefficient exponent : Nat) : NumExpr 1 :=
  .mul (.const coefficient) (powerExpr (.add (.var 0) (.const 1)) exponent)

@[simp] theorem eval_boundExpr (coefficient exponent : Nat) (env : Env 1) :
    (boundExpr coefficient exponent).eval env = powerBound coefficient exponent (env 0) := by
  simp [boundExpr, NumExpr.eval, powerBound_eq]

def widthExpr (wc wk rc rk : Nat) : NumExpr 1 :=
  (2 * .var 0 + 1) + boundExpr wc wk + 2 * boundExpr rc rk + 1

def verifierProgram (M : Machine) (wc wk rc rk : Nat) : ClauseProgram 1 :=
  program M (widthExpr wc wk rc rk) (.var 0) (boundExpr wc wk) (boundExpr rc rk)

def inputEnv (input : Word) : Env 1 := fun _ => input.length

def verifierWord (M : Machine) (wc wk rc rk : Nat) (input : Word) : Word :=
  SAT.encode ((verifierProgram M wc wk rc rk).emit input (inputEnv input))

@[simp] theorem eval_widthExpr (wc wk rc rk : Nat) (input : Word) :
    (widthExpr wc wk rc rk).eval (inputEnv input) =
      CookLevin.windowWidth (powerBound rc rk input.length)
        (CookLevin.verifierPrefix input) (powerBound wc wk input.length) := by
  simp [widthExpr, NumExpr.eval, inputEnv, CookLevin.windowWidth]


theorem verifierProgram_correct (M : Machine) (wc wk rc rk : Nat) (input : Word) :
    Equivalent ((verifierProgram M wc wk rc rk).emit input (inputEnv input))
      (CookLevin.compile M (powerBound rc rk input.length) (CookLevin.verifierPrefix input)
        (powerBound wc wk input.length)) := by
  have hw : 0 < (widthExpr wc wk rc rk).eval (inputEnv input) := by
    rw [eval_widthExpr]
    unfold CookLevin.windowWidth
    omega
  have hfit : (CookLevin.verifierPrefix input).length +
      (boundExpr wc wk).eval (inputEnv input) ≤ (widthExpr wc wk rc rk).eval (inputEnv input) := by
    simp only [eval_widthExpr, eval_boundExpr, inputEnv, CookLevin.windowWidth]
    omega
  have h := program_correct M (widthExpr wc wk rc rk) (.var 0) (boundExpr wc wk)
    (boundExpr rc rk) input (inputEnv input) rfl hw hfit
  simpa only [verifierProgram, eval_widthExpr, eval_boundExpr, inputEnv, CookLevin.compile] using h

/-- The emitted instance is correct for the original bounded machine verifier.
The emitter syntax is fixed by the machine and polynomial constants. -/
theorem verifierWord_correct (M : Machine) (wc wk rc rk : Nat) (input : Word) :
    SAT.SAT (verifierWord M wc wk rc rk input) ↔
      ∃ witness : Word, witness.length ≤ powerBound wc wk input.length ∧
        ∃ tape, runInput M (powerBound rc rk input.length)
          (pairWords input witness) = some (true, tape) := by
  rw [verifierWord, SAT.SAT_encode_iff,
    (verifierProgram_correct M wc wk rc rk input).satisfiable_iff,
    CookLevin.compile_correct]
  simp only [CookLevin.verifierPrefix_append]

/-- A concrete first-order emitter exists for each machine-defined NP language.
Polynomial machine execution of this syntax is supplied by the compiler. -/
theorem inNP_emitter {L : Language} (hL : InNP L) :
    ∃ program : ClauseProgram 1, ∀ input,
      L input ↔ SAT.SAT (SAT.encode (program.emit input (inputEnv input))) := by
  obtain ⟨M, wc, wk, tc, tk, hclock⟩ := inNP_clocked hL
  refine ⟨verifierProgram M wc wk (tc * (wc + 4) ^ tk) ((wk + 1) * tk), ?_⟩
  intro input
  exact (hclock input).trans (verifierWord_correct M wc wk _ _ input).symm

end Complexity.CookLevinEmitter
