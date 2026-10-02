module

public import Complexity.StackCompile
import Lean.Elab.Tactic.Omega

/-!
# Compiled stack machines with their complete final tape

`StackSimulation.controller_simulates` records only the decision and the output of the
compiled controller. Composing a compiled machine with a further tape machine requires the
complete final tape: it is the home-tape encoding of the final registers, with the head moved
one cell right. The proof is the one of `controller_simulates`, with this stronger
postcondition.
-/

@[expose] public section

namespace Complexity.NTM

open StackCompiler StackSimulation

/-- The decision agrees and the final tape represents all final registers. -/
def TapeMatches {stacks : Nat} (source : Bool × StackMachine.Registers stacks)
    (target : Bool × Tape) : Prop :=
  target.1 = source.1 ∧
    ((StackEncoding.homeTape source.2).move .right).Equivalent target.2

/-- Full bounded simulation of the finite stack controller, retaining the final tape. -/
theorem controller_simulates_tape (M : StackMachine.Machine) (fuel : Nat)
    (c : StackMachine.Config M) (result : Bool × StackMachine.Registers M.stacks)
    (hrun : StackMachine.run M fuel c = some result) (capacity : Nat)
    (hroom : Room c.registers fuel capacity) (actual : Tape)
    (hi : (StackEncoding.homeTape c.registers).Equivalent actual) :
    HaltsWithin (compiledController M) (fuel * instructionBudget M capacity)
      ((controlEncoding M).encode (.main c.state)) actual (TapeMatches result) := by
  induction fuel generalizing c actual with
  | zero => simp [StackMachine.run] at hrun
  | succ fuel ih =>
    have hlength := StackEncoding.encodeRegisters_length_le c.registers capacity hroom.bound
    have hcost : 4 * (StackEncoding.encodeRegisters c.registers).length + 13 ≤
        instructionBudget M capacity :=
      Nat.add_le_add_right (Nat.mul_le_mul_left 4 hlength) 13
    cases hc : M.code c.state with
    | halt b =>
      have he : (b, c.registers) = result := by simpa [StackMachine.run, hc] using hrun
      rw [← he]
      have hh := controller_halt M c.state b hc (StackEncoding.homeTape c.registers)
        actual hi (by simp)
      have hh' := hh.post (fun out hout => show TapeMatches (b, c.registers) out from
        ⟨hout.1, hout.2⟩)
      apply hh'.mono
      rw [Nat.succ_mul fuel (instructionBudget M capacity)]
      omega
    | goto next =>
      simp only [StackMachine.run, hc] at hrun
      have hn := ih ⟨next, c.registers⟩ hrun hroom.next actual hi
      have hh := controller_goto M c.state next hc actual
        (by rw [← hi.read]; simp) (fuel * instructionBudget M capacity) _ hn
      apply hh.mono
      rw [Nat.succ_mul fuel (instructionBudget M capacity)]
      omega
    | push k b next =>
      simp only [StackMachine.run, hc] at hrun
      have hsplit := encodeRegisters_split_length c.registers k
      have hin : (regionTape (StackEncoding.before c.registers k)
          (StackEncoding.suffix c.registers k)).Equivalent actual := by
        rw [← homeTape_region]
        exact hi
      have hn : ∀ t, (regionTape (StackEncoding.before c.registers k)
          (.bit b :: StackEncoding.suffix c.registers k)).Equivalent t →
          HaltsWithin (compiledController M) (fuel * instructionBudget M capacity)
            ((controlEncoding M).encode (.main next)) t (TapeMatches result) := by
        intro t ht
        apply ih ⟨next, StackMachine.set c.registers k (b :: c.registers k)⟩
          hrun (hroom.push k b) t
        rw [homeTape_set_region]
        simpa only [List.map_cons, List.cons_append, StackEncoding.suffix] using ht
      have hh := controller_push M c.state next k b hc (StackEncoding.before c.registers k)
        (StackEncoding.before_length ..) (StackEncoding.suffix c.registers k)
        (StackEncoding.suffix_nonblank c.registers k) (StackEncoding.suffix_ne_nil c.registers k)
        actual hin (fuel * instructionBudget M capacity) _ hn
      apply hh.mono
      rw [Nat.succ_mul fuel (instructionBudget M capacity)]
      omega
    | peek k e z o =>
      simp only [StackMachine.run, hc] at hrun
      have hsplit := encodeRegisters_split_length c.registers k
      obtain ⟨head, rest, hs⟩ : ∃ head rest,
          StackEncoding.suffix c.registers k = head :: rest := by
        cases hs : StackEncoding.suffix c.registers k with
        | nil => exact False.elim (StackEncoding.suffix_ne_nil c.registers k hs)
        | cons a xs => exact ⟨a, xs, rfl⟩
      have hhhead : head ≠ .blank :=
        StackEncoding.suffix_nonblank c.registers k head (by simp [hs])
      have hb : readBranch head e z o = StackMachine.branch (c.registers k) e z o := by
        simpa [hs] using readBranch_suffix c.registers k e z o
      have hin : (regionTape (StackEncoding.before c.registers k) (head :: rest)).Equivalent actual := by
        rw [← hs, ← homeTape_region]
        exact hi
      have hn : ∀ t, (regionTape (StackEncoding.before c.registers k) (head :: rest)).Equivalent t →
          HaltsWithin (compiledController M) (fuel * instructionBudget M capacity)
            ((controlEncoding M).encode (.main (readBranch head e z o))) t (TapeMatches result) := by
        intro t ht
        rw [hb]
        apply ih ⟨StackMachine.branch (c.registers k) e z o, c.registers⟩ hrun hroom.next t
        rw [homeTape_region c.registers k, hs]
        exact ht
      have hh := controller_peek M c.state e z o k hc (StackEncoding.before c.registers k)
        (StackEncoding.before_length ..) head rest hhhead actual hin
        (fuel * instructionBudget M capacity) _ hn
      apply hh.mono
      rw [Nat.succ_mul fuel (instructionBudget M capacity)]
      omega
    | pop k e z o =>
      simp only [StackMachine.run, hc] at hrun
      have hsplit := encodeRegisters_split_length c.registers k
      cases hx : c.registers k with
      | nil =>
        have hset : StackMachine.set c.registers k [] = c.registers := by
          rw [← hx]
          exact set_current c.registers k
        have hr : StackMachine.run M fuel ⟨e, c.registers⟩ = some result := by
          simpa only [hx, StackMachine.branch, List.tail_nil, hset] using hrun
        obtain ⟨rest, htail⟩ := StackEncoding.tail_eq_cons c.registers k
        have hs : StackEncoding.suffix c.registers k = .sep :: rest := by
          simp [StackEncoding.suffix, hx, htail]
        have hin : (regionTape (StackEncoding.before c.registers k) (.sep :: rest)).Equivalent actual := by
          rw [← hs, ← homeTape_region]
          exact hi
        have hn : ∀ t, (regionTape (StackEncoding.before c.registers k) (.sep :: rest)).Equivalent t →
            HaltsWithin (compiledController M) (fuel * instructionBudget M capacity)
              ((controlEncoding M).encode (.main e)) t (TapeMatches result) := by
          intro t ht
          apply ih ⟨e, c.registers⟩ hr hroom.next t
          rw [homeTape_region c.registers k, hs]
          exact ht
        have hh := controller_pop_empty M c.state e z o k hc (StackEncoding.before c.registers k)
          (StackEncoding.before_length ..) rest actual hin (fuel * instructionBudget M capacity) _ hn
        apply hh.mono
        rw [Nat.succ_mul fuel (instructionBudget M capacity)]
        omega
      | cons b rest =>
        let remaining := rest.map Symbol.bit ++ StackEncoding.tail c.registers k
        have hs : StackEncoding.suffix c.registers k = .bit b :: remaining := by
          simp only [StackEncoding.suffix, hx, List.map_cons, List.cons_append, remaining]
        have hr : StackMachine.run M fuel
            ⟨if b then o else z, StackMachine.set c.registers k rest⟩ = some result := by
          cases b <;> simpa only [hx, StackMachine.branch, List.tail_cons, Bool.false_eq_true,
            ↓reduceIte] using hrun
        have hroom' : Room (StackMachine.set c.registers k rest) fuel capacity := by
          simpa only [hx, List.tail_cons] using hroom.pop k
        have hremaining : ∀ a ∈ remaining, a ≠ .blank := by
          intro a ha
          exact StackEncoding.suffix_nonblank c.registers k a (by simp [hs, ha])
        have hin : (regionTape (StackEncoding.before c.registers k) (.bit b :: remaining)).Equivalent actual := by
          rw [← hs, ← homeTape_region]
          exact hi
        have hn : ∀ t, (regionTape (StackEncoding.before c.registers k) remaining).Equivalent t →
            HaltsWithin (compiledController M) (fuel * instructionBudget M capacity)
              ((controlEncoding M).encode (.main (if b then o else z))) t (TapeMatches result) := by
          intro t ht
          apply ih ⟨if b then o else z, StackMachine.set c.registers k rest⟩ hr hroom' t
          rw [homeTape_set_region]
          exact ht
        have hh := controller_pop_bit M c.state e z o k hc (StackEncoding.before c.registers k)
          (StackEncoding.before_length ..) b remaining hremaining actual hin
          (fuel * instructionBudget M capacity) _ hn
        apply hh.mono
        have hslen : (StackEncoding.suffix c.registers k).length = remaining.length + 1 := by
          rw [hs]
          rfl
        rw [Nat.succ_mul fuel (instructionBudget M capacity)]
        omega

/-- The compiled machine (initialization and controller) on raw input, retaining the final
tape. -/
theorem compile_simulate_tape (S : StackMachine.Machine) (fuel : Nat) (input : Word)
    (result : Bool × StackMachine.Registers S.stacks)
    (hrun : StackMachine.runInput S fuel input = some result) :
    ∃ time tape, time ≤ StackCompile.budget S input.length fuel ∧
      runInput (StackCompile.compile S) time input = some (result.1, tape) ∧
      ((StackEncoding.homeTape result.2).move .right).Equivalent tape := by
  have hroom : Room (StackMachine.initial S input).registers fuel (input.length + fuel) := by
    intro k
    by_cases hk : k = 0 <;> simp [StackMachine.initial, hk]
  have hi : (StackEncoding.homeTape (StackMachine.initial S input).registers).Equivalent
      (StackInit.initialTape S.stacks input) := by
    rw [StackEncoding.homeTape_initial]
    exact Tape.Equivalent.refl _
  obtain ⟨time, ⟨decision, tape⟩, ht, hr, hp⟩ :=
    controller_simulates_tape S fuel (StackMachine.initial S input) result hrun
      (input.length + fuel) hroom (StackInit.initialTape S.stacks input) hi
  have hb : decision = result.1 := hp.1
  subst decision
  have hseq := sequence_run (StackInit.initMachine S.stacks) (compiledController S)
    (StackInit.initBudget S.stacks input.length) time
    (initial (StackInit.initMachine S.stacks) input) (StackInit.initialTape S.stacks input)
    (result.1, tape) (StackInit.initMachine_run S.stacks input)
    (by simp [StackInit.initialTape]) hr
  refine ⟨StackInit.initBudget S.stacks input.length + time, tape,
    Nat.add_le_add_left ht _, ?_, hp.2⟩
  exact hseq

end Complexity.NTM
