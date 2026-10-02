module

public import Complexity.Restricted.Transform
public import Complexity.SATVariants
import Lean.Elab.Tactic.Omega

/-!
# The occurrence transformation of a clause program

`occFull P` emits, on every input, the formula `output` of
`Complexity.Restricted.Copies` for the annotated emission of `P`. Provided every clause
emitted by `P` has at least two literals, the result is equisatisfiable with the formula
emitted by `P`, and its clauses have two or three literals on distinct variables.

`exactProgram P` first removes empty and unit clauses, applies `occFull`, and pads the
two-literal clauses; it emits an exactly-3 CNF formula equisatisfiable with that of `P`.
-/

@[expose] public section

namespace Complexity.Restricted

open Complexity.SAT StackTableauEmitter

def boundExpr (P : ClauseProgram 1) : NumExpr 1 := .add (loopSum ctx0 P) (.const 2)

def slotExpr (P : ClauseProgram 1) : NumExpr 1 :=
  CookLevinEmitter.powerExpr (boundExpr P) (depth P + 1)

def varExpr (P : ClauseProgram 1) : NumExpr 1 := .add (varSum ctx0 P) (.const 1)

/-- Copies, chains and cycles for the whole program. -/
def occFull (P : ClauseProgram 1) : ClauseProgram 1 :=
  .seq (occ (width P) (depth P + 1) (boundExpr P) (slotExpr P) (.const 0) P 0 0)
    (cycleProg (width P) (signAt P) (varExpr P) (slotExpr P))

theorem occFull_emit (P : ClauseProgram 1) (input : Word) :
    (occFull P).emit input (CookLevinEmitter.inputEnv input) =
      output (width P) (slotCount P input) (varCount P input) (signAt P) (entries P input) := by
  have hB : (boundExpr P).eval (CookLevinEmitter.inputEnv input) = loopBound P input := rfl
  have hR : (slotExpr P).eval (CookLevinEmitter.inputEnv input) = slotCount P input := by
    simp [slotExpr, slotCount, hB]
  have hN : (varExpr P).eval (CookLevinEmitter.inputEnv input) = varCount P input := rfl
  simp only [occFull, ClauseProgram.emit_seq, occ_emit, emit_cycleProg, hB, hR, hN, output,
    entries]
  rfl

theorem evalCNF_iff_forall (a : Assignment) (F : CNF) :
    evalCNF a F = true ↔ ∀ c ∈ F, evalClause a c = true := by
  simp [evalCNF, List.all_eq_true]

theorem occFull_satisfiable_iff (P : ClauseProgram 1) (input : Word)
    (hlen : ∀ c ∈ P.emit input (CookLevinEmitter.inputEnv input), 2 ≤ c.length) :
    Satisfiable ((occFull P).emit input (CookLevinEmitter.inputEnv input)) ↔
      Satisfiable (P.emit input (CookLevinEmitter.inputEnv input)) := by
  have hWF := entries_WF P input hlen
  have hR : 0 < slotCount P input := Nat.lt_of_lt_of_le (by decide) (two_le_slotCount P input)
  rw [occFull_emit, ← entries_map]
  constructor
  · rintro ⟨a', ha'⟩
    refine ⟨lowerAssign (width P) (slotCount P input) (signAt P) a', ?_⟩
    rw [evalCNF_iff_forall] at ha' ⊢
    intro c hc
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hc
    exact output_sound hWF hR a' ha' e he
  · rintro ⟨a, ha⟩
    refine ⟨liftAssign (width P) (slotCount P input) (signAt P) (entries P input) a, ?_⟩
    rw [evalCNF_iff_forall] at ha ⊢
    exact output_complete hWF hR a (fun e he => ha e.2.2 (List.mem_map.mpr ⟨e, he, rfl⟩))

theorem occFull_shape (P : ClauseProgram 1) (input : Word)
    (hlen : ∀ c ∈ P.emit input (CookLevinEmitter.inputEnv input), 2 ≤ c.length) :
    ∀ c ∈ (occFull P).emit input (CookLevinEmitter.inputEnv input),
      (c.length = 2 ∨ c.length = 3) ∧ (c.map Literal.var).Nodup := by
  rw [occFull_emit]
  exact output_shape (entries_WF P input hlen) (two_le_slotCount P input)

/-- Programs without empty and unit clauses. -/
def unitFree (P : ClauseProgram 1) : ClauseProgram 1 := mapClauses unitG P

theorem unitFree_emit (P : ClauseProgram 1) (input : Word) (env : Env 1) :
    (unitFree P).emit input env = (P.emit input env).flatMap unitVal :=
  emit_mapClauses unitG unitVal unitG_emit input P env

theorem unitFree_length (P : ClauseProgram 1) (input : Word) (env : Env 1) :
    ∀ c ∈ (unitFree P).emit input env, 2 ≤ c.length := by
  intro c hc
  rw [unitFree_emit] at hc
  obtain ⟨c0, _, hc⟩ := List.mem_flatMap.mp hc
  exact unitVal_length c0 c hc

theorem unitFree_satisfiable_iff (P : ClauseProgram 1) (input : Word) (env : Env 1) :
    Satisfiable ((unitFree P).emit input env) ↔ Satisfiable (P.emit input env) := by
  rw [unitFree_emit]
  exact satisfiable_flatMap_iff unitVal unitVal_eval _

/-- An exactly-3 CNF program equisatisfiable with `P`. -/
def exactProgram (P : ClauseProgram 1) : ClauseProgram 1 :=
  mapClauses pad2G (occFull (unitFree P))

theorem exactProgram_correct (P : ClauseProgram 1) (input : Word) :
    IsExactThreeCNF ((exactProgram P).emit input (CookLevinEmitter.inputEnv input)) ∧
      (Satisfiable ((exactProgram P).emit input (CookLevinEmitter.inputEnv input)) ↔
        Satisfiable (P.emit input (CookLevinEmitter.inputEnv input))) := by
  have hemit := emit_mapClauses pad2G pad2Val pad2G_emit input (occFull (unitFree P))
    (CookLevinEmitter.inputEnv input)
  have hlen := unitFree_length P input (CookLevinEmitter.inputEnv input)
  constructor
  · intro c hc
    rw [exactProgram, hemit] at hc
    obtain ⟨c0, hc0, hc⟩ := List.mem_flatMap.mp hc
    exact pad2Val_shape c0 (occFull_shape (unitFree P) input hlen c0 hc0) c hc
  · rw [exactProgram, hemit, satisfiable_flatMap_iff pad2Val pad2Val_eval,
      occFull_satisfiable_iff _ _ hlen, unitFree_satisfiable_iff]

end Complexity.Restricted
