module

public import Complexity.TapeEquiv
import Lean.Elab.Tactic.Omega

/-!
An execution status includes both running and halted configurations. Its total
one-instruction transition stutters after halting, which allows a computation to
be represented by a rectangular tableau with a predetermined number of rows.
-/

@[expose] public section

namespace Complexity

/-- A running configuration, or a halted decision together with its final tape. -/
inductive Status (M : Machine) where
  | running (config : Config M)
  | halted (decision : Bool) (tape : Tape)

/-- The tape in either kind of execution status. -/
def Status.tape {M : Machine} : Status M → Tape
  | .running c => c.tape
  | .halted _ t => t

/-- Acceptance is an actual halt with decision `true`. -/
def Status.Accepted {M : Machine} : Status M → Prop
  | .running _ => False
  | .halted b _ => b = true

/-- Execute one instruction, with halted statuses remaining unchanged. -/
def tick (M : Machine) : Status M → Status M
  | .halted b t => .halted b t
  | .running c =>
    match step M c with
    | .inl (b, t) => .halted b t
    | .inr next => .running next

/-- Iterate the concrete instruction transition exactly the given number of
times. Later ticks stutter if the machine has already halted. -/
def evolve (M : Machine) : Nat → Status M → Status M
  | 0, s => s
  | n + 1, s => evolve M n (tick M s)

@[simp] theorem evolve_halted (M : Machine) (n : Nat) (b : Bool) (t : Tape) :
    evolve M n (.halted b t) = .halted b t := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih

/-- Either recurrence order describes the same consecutive instruction ticks. -/
theorem evolve_succ_eq_tick (M : Machine) (n : Nat) (s : Status M) :
    evolve M (n + 1) s = tick M (evolve M n s) := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih => exact ih (tick M s)

theorem evolve_add (M : Machine) (m n : Nat) (s : Status M) :
    evolve M (m + n) s = evolve M n (evolve M m s) := by
  induction m generalizing s with
  | zero => simp [evolve]
  | succ m ih => simpa only [Nat.succ_add, evolve] using ih (tick M s)

/-- The status transition and the fuel interpreter are two presentations of
the same bounded computation, including its entire final tape. -/
theorem evolve_running_halted_iff (M : Machine) (n : Nat) (c : Config M)
    (b : Bool) (t : Tape) :
    evolve M n (.running c) = .halted b t ↔ run M n c = some (b, t) := by
  induction n generalizing c with
  | zero => simp [evolve, run]
  | succ n ih =>
    cases hcode : M.code c.state c.tape.read with
    | halt decision =>
      simp [evolve, tick, step, run, hcode]
    | step a d q =>
      simpa only [evolve, tick, step, run, hcode] using
        ih ⟨q, (c.tape.write a).move d⟩

theorem accepted_iff_halted_true (M : Machine) (s : Status M) :
    s.Accepted ↔ ∃ t, s = .halted true t := by
  cases s with
  | running c => simp [Status.Accepted]
  | halted b t =>
    cases b <;> simp [Status.Accepted]

/-- Acceptance at the last row is equivalent to acceptance by the fuel bound. -/
theorem evolve_accepted_iff (M : Machine) (n : Nat) (c : Config M) :
    (evolve M n (.running c)).Accepted ↔
      ∃ t, run M n c = some (true, t) := by
  rw [accepted_iff_halted_true]
  exact exists_congr fun t => evolve_running_halted_iff M n c true t

/-- At most two previously implicit cells are materialized by one instruction. -/
theorem tick_size_le (M : Machine) (s : Status M) :
    (tick M s).tape.size ≤ s.tape.size + 2 := by
  cases s with
  | halted b t => simp [tick, Status.tape]
  | running c =>
    cases hcode : M.code c.state c.tape.read with
    | halt b => simp [tick, step, hcode, Status.tape]
    | step a d q =>
      simpa only [tick, step, hcode, Status.tape] using c.tape.move_write_size_le a d

/-- All rows, including rows of a computation that has not halted, have a
linear bound on the amount of explicitly represented tape. -/
theorem evolve_size_le (M : Machine) (n : Nat) (s : Status M) :
    (evolve M n s).tape.size ≤ s.tape.size + 2 * n := by
  induction n generalizing s with
  | zero => simp [evolve]
  | succ n ih =>
    have hs := tick_size_le M s
    have ht := ih (tick M s)
    change (evolve M n (tick M s)).tape.size ≤ s.tape.size + 2 * (n + 1)
    omega

theorem evolve_initial_size_le (M : Machine) (n : Nat) (input : List Bool) :
    (evolve M n (.running (initial M input))).tape.size ≤ input.length + 2 * n := by
  simpa only [Status.tape, initial, Tape.size_ofInput] using
    evolve_size_le M n (.running (initial M input))

/-- Equal finite control and blank-padded tapes describe the same status. -/
def Status.Equivalent {M : Machine} : Status M → Status M → Prop
  | .running c, .running c' => c.state = c'.state ∧ c.tape.Equivalent c'.tape
  | .halted b t, .halted b' t' => b = b' ∧ t.Equivalent t'
  | _, _ => False

namespace Status.Equivalent

theorem refl (M : Machine) (s : Status M) : s.Equivalent s := by
  cases s <;> exact ⟨rfl, Tape.Equivalent.refl _⟩

theorem symm {M : Machine} {s s' : Status M} (h : s.Equivalent s') :
    s'.Equivalent s := by
  cases s <;> cases s' <;>
    simp only [Status.Equivalent] at * <;> exact ⟨h.1.symm, h.2.symm⟩

theorem tape {M : Machine} {s s' : Status M} (h : s.Equivalent s') :
    s.tape.Equivalent s'.tape := by
  cases s <;> cases s' <;>
    simp only [Status.Equivalent, Status.tape] at * <;> exact h.2

theorem accepted {M : Machine} {s s' : Status M} (h : s.Equivalent s') :
    s.Accepted ↔ s'.Accepted := by
  cases s <;> cases s' <;>
    simp only [Status.Equivalent, Status.Accepted] at *
  rw [h.1]

end Status.Equivalent

/-- The instruction transition is independent of redundant stored blanks. -/
theorem tick_equivalent (M : Machine) (s s' : Status M) (h : s.Equivalent s') :
    (tick M s).Equivalent (tick M s') := by
  cases s with
  | halted b t =>
    cases s' with
    | halted b' t' => exact h
    | running c' => exact False.elim h
  | running c =>
    cases s' with
    | halted b' t' => exact False.elim h
    | running c' =>
      obtain ⟨q, t⟩ := c
      obtain ⟨q', t'⟩ := c'
      obtain ⟨rfl, ht⟩ := h
      simp only [tick, step]
      rw [← ht.read]
      cases hcode : M.code q t.read with
      | halt b => exact ⟨rfl, ht⟩
      | step a d q' => exact ⟨rfl, (ht.write a).move d⟩

theorem evolve_equivalent (M : Machine) (n : Nat) (s s' : Status M)
    (h : s.Equivalent s') : (evolve M n s).Equivalent (evolve M n s') := by
  induction n generalizing s s' with
  | zero => exact h
  | succ n ih => exact ih _ _ (tick_equivalent M s s' h)

end Complexity
