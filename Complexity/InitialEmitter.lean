module

public import Complexity.EmitterTools
public import Complexity.CookLevin
import Lean.Elab.Tactic.Omega

/-!
First-order clause generation for the standard verifier input prefix and its
bounded certificate. Input bits are inspected individually by `ifInput`.
-/

@[expose] public section

namespace Complexity.InitialEmitter

open StackTableauEmitter

set_option backward.isDefEq.respectTransparency false

local instance {n : Nat} : Add (NumExpr n) := ⟨NumExpr.add⟩
local instance {n : Nat} : Mul (NumExpr n) := ⟨NumExpr.mul⟩
local instance {n : Nat} : Sub (NumExpr n) := ⟨NumExpr.sub⟩
local instance {n k : Nat} : OfNat (NumExpr n) k := ⟨NumExpr.const k⟩

def rightIndex {n : Nat} (width i : NumExpr n) : NumExpr n := width + i + 1

def pin {n : Nat} (M : Machine) (slot : NumExpr n) (value : FiniteRows.Value M) :
    ClauseProgram n := (ConstraintEmitter.Tree.value value).program slot

def allow {n : Nat} (M : Machine) (slot : NumExpr n) : ClauseProgram n :=
  ConstraintEmitter.sequence
    (((List.finRange (M.states + 4)).filter (fun v => !(InitialWord.witnessValues M).contains v)).map
      (fun v => .clause [ConstraintEmitter.negative (M.states + 3) slot v.val]))

def rightCell {n : Nat} (M : Machine) (width inputLength bound i : NumExpr n) : ClauseProgram n :=
  let slot := rightIndex width i
  let blank := pin M slot (FiniteRows.symbolValue M .blank)
  let zero := pin M slot (FiniteRows.symbolValue M (.bit false))
  let one := pin M slot (FiniteRows.symbolValue M (.bit true))
  .ifLe (i + 1) inputLength one
    (.ifLe i inputLength zero
      (.ifLe (i + 1) (2 * inputLength + 1)
        (.ifInput (i - (inputLength + 1)) blank zero one)
        (.ifLe (i + 1) (2 * inputLength + 1 + bound) (allow M slot) blank)))

def blankCell {n : Nat} (M : Machine) (width inputLength bound i : NumExpr n) : ClauseProgram n :=
  .ifLe (2 * inputLength + 1) i
    (.ifLe (i + 2) (2 * inputLength + 1 + bound)
      ((ConstraintEmitter.Tree.value (FiniteRows.symbolValue M .blank)).programWith
        (rightIndex width (i + 1))
        [ConstraintEmitter.negative (M.states + 3) (rightIndex width i)
          (FiniteRows.symbolValue M .blank).val])
      .skip)
    .skip

def program {n : Nat} (M : Machine) (width inputLength bound : NumExpr n) : ClauseProgram n :=
  .seq (.seq (.seq (pin M 0 (FiniteRows.stateValue M M.start))
    (.forDown width (pin M (.var 0 + 1) (FiniteRows.symbolValue M .blank))))
    (.forDown width (rightCell M width.lift inputLength.lift bound.lift (.var 0))))
    (.forDown width (blankCell M width.lift inputLength.lift bound.lift (.var 0)))

theorem emit_pin {n m : Nat} (M : Machine) (slot : NumExpr n) (value : FiniteRows.Value M)
    (input : Word) (env : Env n) (finiteSlot : Fin m) (hslot : slot.eval env = finiteSlot.val) :
    (pin M slot value).emit input env =
      (InitialWord.pin finiteSlot value).map CSPSAT.forbiddenClause := by
  rw [pin, ConstraintEmitter.Tree.emit_program]
  change (RawConstraint.Tree.value value).encode (slot.eval env) = _
  rw [hslot]
  exact RawConstraint.encode_ofTree_val (.value value) finiteSlot

theorem emit_allow {n m : Nat} (M : Machine) (slot : NumExpr n)
    (input : Word) (env : Env n) (finiteSlot : Fin m) (hslot : slot.eval env = finiteSlot.val) :
    (allow M slot).emit input env =
      (InitialWord.allow finiteSlot (InitialWord.witnessValues M)).map CSPSAT.forbiddenClause := by
  simp [allow, ConstraintEmitter.emit_sequence, List.flatMap_map, ← List.map_eq_flatMap,
    InitialWord.allow, List.map_map, CSPSAT.forbiddenClause, ConstraintEmitter.eval_negative,
    hslot, RawConstraint.literal, CSPSAT.atomIndex]

theorem prefix_before (input : Word) (i : Nat) (hi : i < input.length) :
    ((CookLevin.verifierPrefix input).map Symbol.bit).getD i .blank = .bit true := by
  simp only [CookLevin.verifierPrefix, List.map_append, List.map_replicate, List.map_cons]
  rw [InitialWord.getD_append_left (by simpa using hi)]
  simp [List.getD, hi]

theorem prefix_separator (input : Word) :
    ((CookLevin.verifierPrefix input).map Symbol.bit).getD input.length .blank = .bit false := by
  simp only [CookLevin.verifierPrefix, List.map_append, List.map_replicate, List.map_cons]
  rw [InitialWord.getD_append_right (by simp)]
  simp

theorem prefix_after (input : Word) (i : Nat) (hi : input.length < i) :
    ((CookLevin.verifierPrefix input).map Symbol.bit).getD i .blank =
      (input[i - (input.length + 1)]?.map Symbol.bit).getD .blank := by
  simp only [CookLevin.verifierPrefix, List.map_append, List.map_replicate, List.map_cons]
  rw [InitialWord.getD_append_right (by simp; omega)]
  have heq : i - input.length = (i - (input.length + 1)) + 1 := by omega
  simp only [List.length_replicate, heq, List.getD, List.getElem?_cons_succ, List.getElem?_map]

theorem emit_input_pin {n : Nat} (M : Machine) (slot index : NumExpr n)
    (input : Word) (env : Env n) :
    (ClauseProgram.ifInput index (pin M slot (FiniteRows.symbolValue M .blank))
      (pin M slot (FiniteRows.symbolValue M (.bit false)))
      (pin M slot (FiniteRows.symbolValue M (.bit true)))).emit input env =
      (pin M slot (FiniteRows.symbolValue M
        ((input[index.eval env]?.map Symbol.bit).getD .blank))).emit input env := by
  cases h : input[index.eval env]? with
  | none => simp [ClauseProgram.emit, h]
  | some b => cases b <;> simp [ClauseProgram.emit, h]

theorem emit_rightCell {n W : Nat} (M : Machine) (width inputLength bound i : NumExpr n)
    (input : Word) (env : Env n) (j : Fin W)
    (hW : width.eval env = W) (hN : inputLength.eval env = input.length) (hi : i.eval env = j.val) :
    (rightCell M width inputLength bound i).emit input env =
      (InitialWord.rightCell M W (CookLevin.verifierPrefix input) (bound.eval env) j).map
        CSPSAT.forbiddenClause := by
  have hslot : (rightIndex width i).eval env = (FiniteRows.rightSlot W j).val := by
    simp [rightIndex, NumExpr.eval, hW, hi, FiniteRows.rightSlot]
  have hp (a : Symbol) := emit_pin M (rightIndex width i) (FiniteRows.symbolValue M a)
    input env (FiniteRows.rightSlot W j) hslot
  by_cases hfirst : j.val < input.length
  · have ha : j.val + 1 ≤ input.length := by omega
    have hb : j.val < 2 * input.length + 1 := by omega
    simpa only [rightCell, ClauseProgram.emit, NumExpr.eval, hN, hi, ha,
      InitialWord.rightCell, CookLevin.verifierPrefix_length, hb, ↓reduceIte, prefix_before input j.val hfirst]
      using hp (.bit true)
  · by_cases heq : j.val = input.length
    · have ha : ¬ j.val + 1 ≤ input.length := by omega
      have hb : j.val ≤ input.length := by omega
      have hc : j.val < 2 * input.length + 1 := by omega
      have hsep := prefix_separator input
      have hsep' : ((CookLevin.verifierPrefix input).map Symbol.bit).getD j.val .blank = .bit false := by
        simpa only [heq] using hsep
      simpa only [rightCell, ClauseProgram.emit, NumExpr.eval, hN, hi, ha, hb, ↓reduceIte,
        InitialWord.rightCell, CookLevin.verifierPrefix_length, hc, hsep']
        using hp (.bit false)
    · have ha : ¬ j.val + 1 ≤ input.length := by omega
      have hb : ¬ j.val ≤ input.length := by omega
      have hn : input.length < j.val := by omega
      by_cases hprefix : j.val < 2 * input.length + 1
      · have hc : j.val + 1 ≤ 2 * input.length + 1 := by omega
        simp only [rightCell, ClauseProgram.emit, NumExpr.eval, hN, hi, ha, hb, hc,
          ↓reduceIte, InitialWord.rightCell, CookLevin.verifierPrefix_length, hprefix,
          prefix_after input j.val hn]
        have hip := emit_input_pin M (rightIndex width i) (i - (inputLength + 1)) input env
        have hx : (i - (inputLength + 1)).eval env = j.val - (input.length + 1) := by
          change i.eval env - (inputLength.eval env + 1) = _
          rw [hN, hi]
        rw [hx] at hip
        exact hip.trans (hp _)
      · have hc : ¬ j.val + 1 ≤ 2 * input.length + 1 := by omega
        by_cases hwitness : j.val < 2 * input.length + 1 + bound.eval env
        · have hd : j.val + 1 ≤ 2 * input.length + 1 + bound.eval env := by omega
          simpa only [rightCell, ClauseProgram.emit, NumExpr.eval, hN, hi, ha, hb, hc, hd,
            InitialWord.rightCell, CookLevin.verifierPrefix_length, hprefix, hwitness, ↓reduceIte]
            using emit_allow M (rightIndex width i) input env (FiniteRows.rightSlot W j) hslot
        · have hd : ¬ j.val + 1 ≤ 2 * input.length + 1 + bound.eval env := by omega
          simpa only [rightCell, ClauseProgram.emit, NumExpr.eval, hN, hi, ha, hb, hc, hd,
            InitialWord.rightCell, CookLevin.verifierPrefix_length, hprefix, hwitness, ↓reduceIte]
            using hp .blank

theorem emit_guardPin {n m : Nat} (M : Machine) (slot target : NumExpr n)
    (guardValue value : FiniteRows.Value M) (input : Word) (env : Env n)
    (finiteSlot finiteTarget : Fin m)
    (hslot : slot.eval env = finiteSlot.val) (htarget : target.eval env = finiteTarget.val) :
    ((ConstraintEmitter.Tree.value value).programWith target
      [ConstraintEmitter.negative (M.states + 3) slot guardValue.val]).emit input env =
      (LocalConstraint.guard (finiteSlot, guardValue)
        (InitialWord.pin finiteTarget value)).map CSPSAT.forbiddenClause := by
  rw [ConstraintEmitter.Tree.emit_programWith]
  have hg := RawConstraint.map_guard Fin.val (finiteSlot, guardValue)
    (InitialWord.pin finiteTarget value)
  change (LocalConstraint.guard (finiteSlot, guardValue) (InitialWord.pin finiteTarget value)).map
      CSPSAT.forbiddenClause =
    ((InitialWord.pin finiteTarget value).map CSPSAT.forbiddenClause).map
      (List.cons (RawConstraint.literal (M.states + 3) finiteSlot.val guardValue.val)) at hg
  rw [hg]
  have hp := RawConstraint.encode_ofTree_val (LocalConstraint.Tree.value value) finiteTarget
  change (RawConstraint.Tree.value value).encode finiteTarget.val =
    (InitialWord.pin finiteTarget value).map CSPSAT.forbiddenClause at hp
  rw [← hp]
  simp [ConstraintEmitter.Tree.eval, htarget, hslot, RawConstraint.literal]

theorem emit_blankCell {n W : Nat} (M : Machine) (width inputLength bound i : NumExpr n)
    (input : Word) (env : Env n) (j : Fin W)
    (hW : width.eval env = W) (hN : inputLength.eval env = input.length) (hi : i.eval env = j.val)
    (fit : (CookLevin.verifierPrefix input).length + bound.eval env ≤ W) :
    (blankCell M width inputLength bound i).emit input env =
      (InitialWord.blankCell M W (CookLevin.verifierPrefix input) (bound.eval env) fit j).map
        CSPSAT.forbiddenClause := by
  by_cases hc : (CookLevin.verifierPrefix input).length ≤ j.val ∧
      j.val + 1 < (CookLevin.verifierPrefix input).length + bound.eval env
  · rw [InitialWord.blankCell, dite_eq_left hc]
    have ha : 2 * input.length + 1 ≤ j.val := by simpa using hc.1
    have hb : j.val + 2 ≤ 2 * input.length + 1 + bound.eval env := by
      have h := hc.2
      rw [CookLevin.verifierPrefix_length] at h
      omega
    have hj : j.val + 1 < W := by omega
    have hs : (rightIndex width i).eval env = (FiniteRows.rightSlot W j).val := by
      simp [rightIndex, NumExpr.eval, hW, hi, FiniteRows.rightSlot]
    have ht : (rightIndex width (i + 1)).eval env =
        (FiniteRows.rightSlot W ⟨j.val + 1, hj⟩).val := by
      simp [rightIndex, NumExpr.eval, hW, hi, FiniteRows.rightSlot]
    simpa only [blankCell, ClauseProgram.emit, NumExpr.eval, hN, hi, ha, hb, ↓reduceIte,
      ] using
      emit_guardPin M (rightIndex width i) (rightIndex width (i + 1))
        (FiniteRows.symbolValue M .blank) (FiniteRows.symbolValue M .blank)
        input env (FiniteRows.rightSlot W j) (FiniteRows.rightSlot W ⟨j.val + 1, hj⟩) hs ht
  · rw [InitialWord.blankCell, dite_eq_right hc]
    have hn : ¬ (2 * input.length + 1 ≤ j.val ∧
        j.val + 2 ≤ 2 * input.length + 1 + bound.eval env) := by
      simp only [CookLevin.verifierPrefix_length] at hc
      omega
    by_cases ha : 2 * input.length + 1 ≤ j.val
    · have hb : ¬ j.val + 2 ≤ 2 * input.length + 1 + bound.eval env := by omega
      simp [blankCell, ClauseProgram.emit, NumExpr.eval, hN, hi, ha, hb,
        ClauseProgram.skip]
    · simp [blankCell, ClauseProgram.emit, NumExpr.eval, hN, hi, ha,
        ClauseProgram.skip]

/-- The executable initial-row emitter gives precisely the verified initial
constraints, up to the harmless reversal of the clauses from counted loops. -/
theorem program_correct {n : Nat} (M : Machine) (width inputLength bound : NumExpr n)
    (input : Word) (env : Env n) (hN : inputLength.eval env = input.length)
    (fit : (CookLevin.verifierPrefix input).length + bound.eval env ≤ width.eval env) :
    Equivalent ((program M width inputLength bound).emit input env)
      ((InitialWord.problem M (width.eval env) (CookLevin.verifierPrefix input)
        (bound.eval env) fit).map CSPSAT.forbiddenClause) := by
  simp only [program, ClauseProgram.emit, InitialWord.problem, List.map_append,
    List.map_flatMap]
  apply Equivalent.append
  · apply Equivalent.append
    · apply Equivalent.append
      · rw [emit_pin M 0 (FiniteRows.stateValue M M.start) input env
          (FiniteRows.stateSlot (width.eval env)) rfl]
        exact Equivalent.refl _
      · apply equivalent_flatMap_finRange
        intro j
        have h := emit_pin M ((NumExpr.var 0 : NumExpr (n + 1)) + 1)
          (FiniteRows.symbolValue M .blank) input (extend j.val env)
          (FiniteRows.leftSlot (width.eval env) j) rfl
        rw [h]
        exact Equivalent.refl _
    · apply equivalent_flatMap_finRange
      intro j
      have h := emit_rightCell M width.lift inputLength.lift bound.lift (.var 0)
        input (extend j.val env) j
        (NumExpr.eval_lift width j.val env)
        ((NumExpr.eval_lift inputLength j.val env).trans hN) rfl
      simp only [NumExpr.eval_lift] at h
      rw [h]
      exact Equivalent.refl _
  · apply equivalent_flatMap_finRange
    intro j
    have fit' : (CookLevin.verifierPrefix input).length +
        bound.lift.eval (extend j.val env) ≤ width.eval env := by simpa using fit
    have h := emit_blankCell M width.lift inputLength.lift bound.lift (.var 0)
      input (extend j.val env) j
      (NumExpr.eval_lift width j.val env)
      ((NumExpr.eval_lift inputLength j.val env).trans hN) rfl fit'
    simp only [NumExpr.eval_lift] at h
    rw [h]
    exact Equivalent.refl _

end Complexity.InitialEmitter
