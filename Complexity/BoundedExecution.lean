module

public import Complexity.Execution
import Lean.Elab.Tactic.Omega

/-!
Finite tape windows for bounded computations. Every tape half has exactly the
chosen width. The finite transition pads with blanks and discards cells outside
the window; the simulation theorem proves that the discarded cells cannot affect
the computation within the stated horizon.
-/

@[expose] public section

namespace Complexity

/-- A list window padded with blanks to exactly `width` symbols. -/
def symbolWindow (xs : List Symbol) (width : Nat) : List Symbol :=
  (xs ++ List.replicate width Symbol.blank).take width

@[simp] theorem symbolWindow_length (xs : List Symbol) (width : Nat) :
    (symbolWindow xs width).length = width := by
  simp only [symbolWindow, List.length_take, List.length_append, List.length_replicate]
  apply Nat.min_eq_left
  omega

theorem symbolWindow_getD_lt (xs : List Symbol) (width i : Nat) (hi : i < width) :
    (symbolWindow xs width).getD i .blank = xs.getD i .blank := by
  simp only [symbolWindow, List.getD, List.getElem?_take, ite_eq_left hi]
  exact BlankEq.append_blanks xs width i

theorem symbolWindow_getD_ge (xs : List Symbol) (width i : Nat) (hi : width ≤ i) :
    (symbolWindow xs width).getD i .blank = .blank := by
  simp [symbolWindow, List.getD, show ¬ i < width by omega]

namespace BlankEq

/-- Truncating an equivalent representation is safe when the reference list
has no stored cells beyond the truncation point. -/
theorem take_of_length_le {xs ys : List Symbol} (h : BlankEq xs ys)
    (width : Nat) (hy : ys.length ≤ width) : BlankEq (xs.take width) ys := by
  intro n
  simp only [List.getD, List.getElem?_take]
  by_cases hn : n < width
  · rw [ite_eq_left hn]
    exact h n
  · rw [ite_eq_right hn, List.getElem?_eq_none (show ys.length ≤ n by omega)]

theorem window {xs ys : List Symbol} (h : BlankEq xs ys)
    (width : Nat) (hy : ys.length ≤ width) : BlankEq (symbolWindow xs width) ys :=
  ((append_blanks xs width).trans h).take_of_length_le width hy

end BlankEq

namespace Tape

theorem read_eq_getD (t : Tape) : t.read = t.right.getD 0 .blank := by
  exact List.headD_eq_getD

theorem write_left_getD (t : Tape) (a : Symbol) (i : Nat) :
    (t.write a).left.getD i .blank = t.left.getD i .blank := rfl

theorem write_right_getD_zero (t : Tape) (a : Symbol) :
    (t.write a).right.getD 0 .blank = a := rfl

theorem write_right_getD_succ (t : Tape) (a : Symbol) (i : Nat) :
    (t.write a).right.getD (i + 1) .blank = t.right.getD (i + 1) .blank := by
  cases t with
  | mk left right => cases right <;> simp [write]

theorem getD_drop_one (xs : List Symbol) (i : Nat) :
    (xs.drop 1).getD i .blank = xs.getD (i + 1) .blank := by
  cases xs <;> simp

theorem move_left_left_getD (t : Tape) (i : Nat) :
    (t.move .left).left.getD i .blank = t.left.getD (i + 1) .blank := by
  rw [move_left_eq]
  exact getD_drop_one _ _

theorem move_left_right_getD_zero (t : Tape) :
    (t.move .left).right.getD 0 .blank = t.left.getD 0 .blank := by
  rw [move_left_eq]
  exact List.headD_eq_getD

theorem move_left_right_getD_succ (t : Tape) (i : Nat) :
    (t.move .left).right.getD (i + 1) .blank = t.right.getD i .blank := by
  rw [move_left_eq]
  exact List.getD_cons_succ

theorem move_right_left_getD_zero (t : Tape) :
    (t.move .right).left.getD 0 .blank = t.right.getD 0 .blank := by
  rw [move_right_eq]
  exact List.headD_eq_getD

theorem move_right_left_getD_succ (t : Tape) (i : Nat) :
    (t.move .right).left.getD (i + 1) .blank = t.left.getD i .blank := by
  rw [move_right_eq]
  exact List.getD_cons_succ

theorem move_right_right_getD (t : Tape) (i : Nat) :
    (t.move .right).right.getD i .blank = t.right.getD (i + 1) .blank := by
  rw [move_right_eq]
  exact getD_drop_one _ _

/-- Store exactly `width` cells on each side of the head, including the cell
under the head on the right side. -/
def window (t : Tape) (width : Nat) : Tape :=
  ⟨symbolWindow t.left width, symbolWindow t.right width⟩

@[simp] theorem window_left_length (t : Tape) (width : Nat) :
    (t.window width).left.length = width := symbolWindow_length _ _

@[simp] theorem window_right_length (t : Tape) (width : Nat) :
    (t.window width).right.length = width := symbolWindow_length _ _

theorem window_left_getD_lt (t : Tape) (width i : Nat) (hi : i < width) :
    (t.window width).left.getD i .blank = t.left.getD i .blank :=
  symbolWindow_getD_lt _ _ _ hi

theorem window_right_getD_lt (t : Tape) (width i : Nat) (hi : i < width) :
    (t.window width).right.getD i .blank = t.right.getD i .blank :=
  symbolWindow_getD_lt _ _ _ hi

/-- Windowing a representation is sound whenever the reference tape fits. -/
theorem Equivalent.window {t u : Tape} (h : t.Equivalent u)
    (width : Nat) (hu : u.size ≤ width) : (t.window width).Equivalent u := by
  have hl : u.left.length ≤ width := by simp only [size] at hu; omega
  have hr : u.right.length ≤ width := by simp only [size] at hu; omega
  exact ⟨h.1.window width hl, h.2.window width hr⟩

theorem window_equivalent (t : Tape) (width : Nat) (h : t.size ≤ width) :
    (t.window width).Equivalent t := (Equivalent.refl t).window width h

end Tape

/-- Window the tape, preserving finite control and the halting decision. -/
def Status.window {M : Machine} (s : Status M) (width : Nat) : Status M :=
  match s with
  | .running c => .running ⟨c.state, c.tape.window width⟩
  | .halted b t => .halted b (t.window width)

@[simp] theorem Status.window_tape {M : Machine} (s : Status M) (width : Nat) :
    (s.window width).tape = s.tape.window width := by cases s <;> rfl

theorem Status.Equivalent.window {M : Machine} {s s' : Status M}
    (h : s.Equivalent s') (width : Nat) (hsize : s'.tape.size ≤ width) :
    (s.window width).Equivalent s' := by
  cases s <;> cases s' <;>
    simp only [Status.Equivalent, Status.window, Status.tape] at * <;>
    exact ⟨h.1, h.2.window width hsize⟩

/-- The finite-row transition: execute one local instruction, then maintain
exactly the prescribed number of cells on each side of the head. -/
def tickWindow (M : Machine) (width : Nat) (s : Status M) : Status M :=
  (tick M s).window width

/-- Iteration of the finite-row transition. -/
def evolveWindow (M : Machine) (width : Nat) : Nat → Status M → Status M
  | 0, s => s
  | n + 1, s => evolveWindow M width n (tickWindow M width s)

theorem evolveWindow_succ_eq_tickWindow (M : Machine) (width n : Nat) (s : Status M) :
    evolveWindow M width (n + 1) s = tickWindow M width (evolveWindow M width n s) := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih => exact ih (tickWindow M width s)

/-- Finite windows preserve the full execution semantics through the requested
horizon. The bound is on the actual reference computation, not its padding. -/
theorem evolveWindow_equivalent (M : Machine) (width n : Nat) (s s' : Status M)
    (h : s.Equivalent s') (hsize : s'.tape.size + 2 * n ≤ width) :
    (evolveWindow M width n s).Equivalent (evolve M n s') := by
  induction n generalizing s s' with
  | zero => exact h
  | succ n ih =>
    have hs := tick_size_le M s'
    have hnext : (tickWindow M width s).Equivalent (tick M s') :=
      (tick_equivalent M s s' h).window width (by omega)
    have hbound : (tick M s').tape.size + 2 * n ≤ width := by omega
    exact ih _ _ hnext hbound

theorem evolveWindow_start_equivalent (M : Machine) (width n : Nat) (s : Status M)
    (hsize : s.tape.size + 2 * n ≤ width) :
    (evolveWindow M width n (s.window width)).Equivalent (evolve M n s) := by
  apply evolveWindow_equivalent
  · exact (Status.Equivalent.refl M s).window width (by omega)
  · exact hsize

/-- Start the finite computation with a padded binary input. -/
def boundedRun (M : Machine) (width n : Nat) (input : List Bool) : Status M :=
  evolveWindow M width n ((Status.running (initial M input)).window width)

/-- A finite-width tableau reaches an accepting status exactly when the
original infinite-tape machine accepts within the same instruction bound. -/
theorem boundedRun_accepted_iff (M : Machine) (width n : Nat) (input : List Bool)
    (hsize : input.length + 2 * n ≤ width) :
    (boundedRun M width n input).Accepted ↔
      ∃ t, runInput M n input = some (true, t) := by
  have h := evolveWindow_start_equivalent M width n (.running (initial M input))
    (by simpa only [Status.tape, initial, Tape.size_ofInput] using hsize)
  exact h.accepted.trans (evolve_accepted_iff M n (initial M input))

theorem evolveWindow_lengths (M : Machine) (width n : Nat) (s : Status M)
    (h : s.tape.left.length = width ∧ s.tape.right.length = width) :
    (evolveWindow M width n s).tape.left.length = width ∧
    (evolveWindow M width n s).tape.right.length = width := by
  induction n generalizing s with
  | zero => exact h
  | succ n ih =>
    apply ih
    simp [tickWindow]

theorem boundedRun_lengths (M : Machine) (width n : Nat) (input : List Bool) :
    (boundedRun M width n input).tape.left.length = width ∧
    (boundedRun M width n input).tape.right.length = width := by
  apply evolveWindow_lengths
  simp

end Complexity
