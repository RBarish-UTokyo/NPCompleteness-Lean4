module

public import Complexity.BoundedExecution
public import Complexity.LocalConstraint
import Lean.Elab.Tactic.Omega

/-!
Finite encodings of computation rows and explicit local transition trees. A row
has one finite-control value and two head-relative tape windows. Each output
cell consults at most the control, scanned symbol, and one neighboring cell.
-/

@[expose] public section

namespace Complexity.FiniteRows

open LocalConstraint

abbrev Value (M : Machine) := Fin (M.states + 4)
abbrev Slot (width : Nat) := Fin (2 * width + 1)
abbrev Row (M : Machine) (width : Nat) := Slot width → Value M

def stateSlot (width : Nat) : Slot width := ⟨0, by omega⟩
def leftSlot (width : Nat) (i : Fin width) : Slot width := ⟨i.val + 1, by omega⟩
def rightSlot (width : Nat) (i : Fin width) : Slot width := ⟨width + i.val + 1, by omega⟩

inductive Cell (width : Nat) where
  | state
  | left (i : Fin width)
  | right (i : Fin width)

def Cell.slot {width : Nat} : Cell width → Slot width
  | .state => stateSlot width
  | .left i => leftSlot width i
  | .right i => rightSlot width i

def coordinate (width : Nat) (slot : Slot width) : Cell width :=
  if h0 : slot.val = 0 then .state
  else if hl : slot.val ≤ width then .left ⟨slot.val - 1, by omega⟩
  else .right ⟨slot.val - width - 1, by omega⟩

@[simp] theorem coordinate_slot {width : Nat} (c : Cell width) :
    coordinate width c.slot = c := by
  cases c with
  | state => simp [Cell.slot, stateSlot, coordinate]
  | left i =>
    have hl : i.val + 1 ≤ width := by omega
    simp [Cell.slot, leftSlot, coordinate, hl]
  | right i =>
    have hl : ¬ width + i.val + 1 ≤ width := by omega
    simp only [Cell.slot, rightSlot, coordinate, Nat.add_eq_zero_iff,
      Nat.one_ne_zero, and_false, ↓reduceDIte, hl, Cell.right.injEq]
    apply Fin.ext
    change width + i.val + 1 - width - 1 = i.val
    omega

@[simp] theorem slot_coordinate {width : Nat} (i : Slot width) :
    (coordinate width i).slot = i := by
  simp only [coordinate]
  split
  · apply Fin.ext
    simp only [Cell.slot, stateSlot]
    omega
  · split <;> apply Fin.ext <;> simp only [Cell.slot, leftSlot, rightSlot] <;> omega

theorem slot_cases {width : Nat} (i : Slot width) :
    i = stateSlot width ∨ (∃ j, i = leftSlot width j) ∨ ∃ j, i = rightSlot width j := by
  have h := slot_coordinate i
  cases hc : coordinate width i with
  | state => exact Or.inl (by simpa only [hc, Cell.slot] using h.symm)
  | left j => exact Or.inr (Or.inl ⟨j, by simpa only [hc, Cell.slot] using h.symm⟩)
  | right j => exact Or.inr (Or.inr ⟨j, by simpa only [hc, Cell.slot] using h.symm⟩)

/-- Symbol codes are blank=0, false=1, true=2, separator=3. -/
def symbolValue (M : Machine) : Symbol → Value M
  | .blank => ⟨0, by omega⟩
  | .bit false => ⟨1, by omega⟩
  | .bit true => ⟨2, by omega⟩
  | .sep => ⟨3, by omega⟩

def decodeSymbol (M : Machine) (v : Value M) : Symbol :=
  match v.val with
  | 1 => .bit false
  | 2 => .bit true
  | 3 => .sep
  | _ => .blank

@[simp] theorem decodeSymbol_symbolValue (M : Machine) (s : Symbol) :
    decodeSymbol M (symbolValue M s) = s := by
  cases s with
  | blank => rfl
  | sep => rfl
  | bit b => cases b <;> rfl

theorem symbolValue_injective (M : Machine) {s t : Symbol}
    (h : symbolValue M s = symbolValue M t) : s = t := by
  have hh := congrArg (decodeSymbol M) h
  simpa using hh

inductive Control (M : Machine) where
  | halted (decision : Bool)
  | running (state : Fin (M.states + 1))

def decisionValue (M : Machine) (b : Bool) : Value M :=
  ⟨if b then 1 else 0, by cases b <;> simp⟩

def stateValue (M : Machine) (q : Fin (M.states + 1)) : Value M :=
  ⟨q.val + 2, by omega⟩

def controlValue (M : Machine) : Control M → Value M
  | .halted b => decisionValue M b
  | .running q => stateValue M q

def decodeControl (M : Machine) (v : Value M) : Control M :=
  if v.val < 2 then .halted (v.val == 1)
  else if h : v.val - 2 < M.states + 1 then .running ⟨v.val - 2, h⟩
  else .halted false

@[simp] theorem decodeControl_controlValue (M : Machine) (c : Control M) :
    decodeControl M (controlValue M c) = c := by
  cases c with
  | halted b => cases b <;> simp [controlValue, decisionValue, decodeControl]
  | running q =>
    have hl : ¬ q.val + 2 < 2 := by omega
    simp [controlValue, stateValue, decodeControl, hl, q.isLt]

theorem controlValue_injective (M : Machine) {c c' : Control M}
    (h : controlValue M c = controlValue M c') : c = c' := by
  have hh := congrArg (decodeControl M) h
  simpa using hh

def control {M : Machine} : Status M → Control M
  | .running c => .running c.state
  | .halted b _ => .halted b

def encodeCell (M : Machine) {width : Nat} (s : Status M) : Cell width → Value M
  | .state => controlValue M (control s)
  | .left i => symbolValue M (s.tape.left.getD i.val .blank)
  | .right i => symbolValue M (s.tape.right.getD i.val .blank)

def encode (M : Machine) (width : Nat) (s : Status M) : Row M width :=
  fun i => encodeCell M s (coordinate width i)

@[simp] theorem encode_slot (M : Machine) {width : Nat} (s : Status M) (c : Cell width) :
    encode M width s c.slot = encodeCell M s c := by simp [encode]

@[simp] theorem encode_state (M : Machine) (width : Nat) (s : Status M) :
    encode M width s (stateSlot width) = controlValue M (control s) :=
  encode_slot M s .state

@[simp] theorem encode_left (M : Machine) (width : Nat) (s : Status M) (i : Fin width) :
    encode M width s (leftSlot width i) = symbolValue M (s.tape.left.getD i.val .blank) :=
  encode_slot M s (.left i)

@[simp] theorem encode_right (M : Machine) (width : Nat) (s : Status M) (i : Fin width) :
    encode M width s (rightSlot width i) = symbolValue M (s.tape.right.getD i.val .blank) :=
  encode_slot M s (.right i)

theorem encode_accepted_iff (M : Machine) (width : Nat) (s : Status M) :
    encode M width s (stateSlot width) = decisionValue M true ↔ s.Accepted := by
  cases s with
  | halted b t => cases b <;> simp [control, controlValue, decisionValue, Status.Accepted]
  | running c =>
    simp only [encode_state, control, controlValue, stateValue, decisionValue,
      ↓reduceIte, Fin.mk.injEq, Status.Accepted, iff_false]
    omega

/-- One symbol may be a constant or a cell from either side of the old head. -/
inductive Source where
  | value (s : Symbol)
  | left (index : Nat)
  | right (index : Nat)

def Source.read (t : Tape) : Source → Symbol
  | .value a => a
  | .left i => t.left.getD i .blank
  | .right i => t.right.getD i .blank

/-- A single neighbor query, using an implicit blank outside the finite window. -/
def sourceTree (M : Machine) (width : Nat) : Source → Tree (2 * width + 1) (M.states + 3)
  | .value a => .value (symbolValue M a)
  | .left i =>
    if hi : i < width then .query (leftSlot width ⟨i, hi⟩) Tree.value
    else .value (symbolValue M .blank)
  | .right i =>
    if hi : i < width then .query (rightSlot width ⟨i, hi⟩) Tree.value
    else .value (symbolValue M .blank)

theorem sourceTree_eval (M : Machine) (width : Nat) (s : Status M) (src : Source)
    (hl : s.tape.left.length ≤ width) (hr : s.tape.right.length ≤ width) :
    (sourceTree M width src).eval (encode M width s) = symbolValue M (src.read s.tape) := by
  cases src with
  | value a => rfl
  | left i =>
    by_cases hi : i < width
    · simp [sourceTree, hi, Tree.eval, Source.read]
    · have hn : s.tape.left.length ≤ i := by omega
      simp [sourceTree, hi, Tree.eval, Source.read, List.getD, List.getElem?_eq_none hn]
  | right i =>
    by_cases hi : i < width
    · simp [sourceTree, hi, Tree.eval, Source.read]
    · have hn : s.tape.right.length ≤ i := by omega
      simp [sourceTree, hi, Tree.eval, Source.read, List.getD, List.getElem?_eq_none hn]

def leftSource (a : Symbol) (d : Move) (i : Nat) : Source :=
  match d with
  | .left => .left (i + 1)
  | .stay => .left i
  | .right => match i with
    | 0 => .value a
    | i + 1 => .left i

def rightSource (a : Symbol) (d : Move) (i : Nat) : Source :=
  match d with
  | .left => match i with
    | 0 => .left 0
    | 1 => .value a
    | i + 2 => .right (i + 1)
  | .stay => match i with
    | 0 => .value a
    | i + 1 => .right (i + 1)
  | .right => .right (i + 1)

theorem leftSource_read (t : Tape) (a : Symbol) (d : Move) (i : Nat) :
    (leftSource a d i).read t = ((t.write a).move d).left.getD i .blank := by
  cases d with
  | stay => rfl
  | left => rw [Tape.move_left_left_getD, Tape.write_left_getD]; rfl
  | right =>
    cases i with
    | zero => rw [Tape.move_right_left_getD_zero, Tape.write_right_getD_zero]; rfl
    | succ i => rw [Tape.move_right_left_getD_succ, Tape.write_left_getD]; rfl

theorem rightSource_read (t : Tape) (a : Symbol) (d : Move) (i : Nat) :
    (rightSource a d i).read t = ((t.write a).move d).right.getD i .blank := by
  cases d with
  | right => rw [Tape.move_right_right_getD, Tape.write_right_getD_succ]; rfl
  | stay =>
    cases i with
    | zero => rfl
    | succ i =>
      change t.right.getD (i + 1) .blank = (t.write a).right.getD (i + 1) .blank
      exact (Tape.write_right_getD_succ t a i).symm
  | left =>
    cases i with
    | zero => rw [Tape.move_left_right_getD_zero, Tape.write_left_getD]; rfl
    | succ i =>
      cases i with
      | zero => rw [Tape.move_left_right_getD_succ, Tape.write_right_getD_zero]; rfl
      | succ i => rw [Tape.move_left_right_getD_succ, Tape.write_right_getD_succ]; rfl

def haltTree (M : Machine) (width : Nat) (b : Bool) :
    Cell width → Tree (2 * width + 1) (M.states + 3)
  | .state => .value (decisionValue M b)
  | .left i => sourceTree M width (.left i.val)
  | .right i => sourceTree M width (.right i.val)

/-- A finite tree for one output cell of one decoded machine instruction. -/
def instructionTree (M : Machine) (width : Nat) :
    Instruction (M.states + 1) → Cell width → Tree (2 * width + 1) (M.states + 3)
  | .halt b, c => haltTree M width b c
  | .step _ _ q, .state => .value (stateValue M q)
  | .step a d _, .left i => sourceTree M width (leftSource a d i.val)
  | .step a d _, .right i => sourceTree M width (rightSource a d i.val)

/-- The status obtained by executing a specified single local instruction. -/
def instructionStatus (M : Machine) (t : Tape) : Instruction (M.states + 1) → Status M
  | .halt b => .halted b t
  | .step a d q => .running ⟨q, (t.write a).move d⟩

theorem haltTree_eval (M : Machine) (width : Nat) (s : Status M) (b : Bool)
    (c : Cell width) (hl : s.tape.left.length ≤ width) (hr : s.tape.right.length ≤ width) :
    (haltTree M width b c).eval (encode M width s) =
      encodeCell M (.halted b s.tape) c := by
  cases c with
  | state => rfl
  | left i => exact sourceTree_eval M width s (.left i.val) hl hr
  | right i => exact sourceTree_eval M width s (.right i.val) hl hr

theorem instructionTree_eval (M : Machine) (width : Nat) (s : Status M)
    (instruction : Instruction (M.states + 1)) (c : Cell width)
    (hl : s.tape.left.length ≤ width) (hr : s.tape.right.length ≤ width) :
    (instructionTree M width instruction c).eval (encode M width s) =
      encodeCell M (instructionStatus M s.tape instruction) c := by
  cases instruction with
  | halt b => exact haltTree_eval M width s b c hl hr
  | step a d q =>
    cases c with
    | state => rfl
    | left i =>
      rw [instructionTree, sourceTree_eval M width s _ hl hr]
      exact congrArg (symbolValue M) (leftSource_read s.tape a d i.val)
    | right i =>
      rw [instructionTree, sourceTree_eval M width s _ hl hr]
      exact congrArg (symbolValue M) (rightSource_read s.tape a d i.val)

@[simp] theorem control_window (M : Machine) (width : Nat) (s : Status M) :
    control (s.window width) = control s := by cases s <;> rfl

@[simp] theorem encodeCell_window (M : Machine) (width : Nat) (s : Status M)
    (c : Cell width) : encodeCell M (s.window width) c = encodeCell M s c := by
  cases c with
  | state => simp [encodeCell]
  | left i =>
    simp only [encodeCell, Status.window_tape, Tape.window_left_getD_lt _ _ _ i.isLt]
  | right i =>
    simp only [encodeCell, Status.window_tape, Tape.window_right_getD_lt _ _ _ i.isLt]

@[simp] theorem encode_window (M : Machine) (width : Nat) (s : Status M) :
    encode M width (s.window width) = encode M width s := by
  funext i
  exact encodeCell_window M width s (coordinate width i)

/-- Read finite control, then the scanned symbol if running, then at most one
neighbor. Every branch is a concrete finite tree of depth at most three. -/
def transitionTreeCell (M : Machine) (width : Nat) (hwidth : 0 < width)
    (c : Cell width) : Tree (2 * width + 1) (M.states + 3) :=
  .query (stateSlot width) fun v =>
    match decodeControl M v with
    | .halted b => haltTree M width b c
    | .running q => .query (rightSlot width ⟨0, hwidth⟩) fun scanned =>
      instructionTree M width (M.code q (decodeSymbol M scanned)) c

def transitionTree (M : Machine) (width : Nat) (hwidth : 0 < width)
    (i : Slot width) : Tree (2 * width + 1) (M.states + 3) :=
  transitionTreeCell M width hwidth (coordinate width i)

theorem eval_transitionTreeCell (M : Machine) (width : Nat) (hwidth : 0 < width)
    (s : Status M) (c : Cell width)
    (hl : s.tape.left.length ≤ width) (hr : s.tape.right.length ≤ width) :
    (transitionTreeCell M width hwidth c).eval (encode M width s) =
      encodeCell M (tickWindow M width s) c := by
  simp only [tickWindow, encodeCell_window]
  cases s with
  | halted b t =>
    simpa only [transitionTreeCell, Tree.eval, encode_state, control,
      decodeControl_controlValue, tick, Status.tape] using
        haltTree_eval M width (.halted b t) b c hl hr
  | running cfg =>
    simp only [transitionTreeCell, Tree.eval, encode_state, control,
      decodeControl_controlValue, encode_right, Status.tape, decodeSymbol_symbolValue]
    rw [← Tape.read_eq_getD]
    have h := instructionTree_eval M width (.running cfg)
      (M.code cfg.state cfg.tape.read) c hl hr
    cases hcode : M.code cfg.state cfg.tape.read <;>
      simpa only [hcode, instructionStatus, tick, step, Status.tape] using h

/-- Each cell of the finite successor row is exactly the result of its local
finite decision tree, on every well-sized encoded computation status. -/
theorem eval_transitionTree (M : Machine) (width : Nat) (hwidth : 0 < width)
    (s : Status M) (i : Slot width)
    (hl : s.tape.left.length ≤ width) (hr : s.tape.right.length ≤ width) :
    (transitionTree M width hwidth i).eval (encode M width s) =
      encode M width (tickWindow M width s) i :=
  eval_transitionTreeCell M width hwidth s (coordinate width i) hl hr

/-- A syntactic upper bound on the number of queries along every tree branch. -/
def QueriesAtMost {m d : Nat} : Nat → Tree m d → Prop
  | _, .value _ => True
  | 0, .query _ _ => False
  | n + 1, .query _ branches => ∀ v, QueriesAtMost n (branches v)

theorem sourceTree_queries (M : Machine) (width n : Nat) (src : Source) :
    QueriesAtMost (n + 1) (sourceTree M width src) := by
  cases src with
  | value a => trivial
  | left i => by_cases hi : i < width <;> simp [sourceTree, hi, QueriesAtMost]
  | right i => by_cases hi : i < width <;> simp [sourceTree, hi, QueriesAtMost]

theorem haltTree_queries (M : Machine) (width n : Nat) (b : Bool) (c : Cell width) :
    QueriesAtMost (n + 1) (haltTree M width b c) := by
  cases c with
  | state => trivial
  | left i => exact sourceTree_queries M width n (.left i.val)
  | right i => exact sourceTree_queries M width n (.right i.val)

theorem instructionTree_queries (M : Machine) (width n : Nat)
    (instruction : Instruction (M.states + 1)) (c : Cell width) :
    QueriesAtMost (n + 1) (instructionTree M width instruction c) := by
  cases instruction with
  | halt b => exact haltTree_queries M width n b c
  | step a d q =>
    cases c with
    | state => trivial
    | left i => exact sourceTree_queries M width n _
    | right i => exact sourceTree_queries M width n _

theorem transitionTree_queries (M : Machine) (width : Nat) (hwidth : 0 < width)
    (i : Slot width) : QueriesAtMost 3 (transitionTree M width hwidth i) := by
  intro v
  cases hc : decodeControl M v with
  | halted b => simpa only [hc] using haltTree_queries M width 1 b (coordinate width i)
  | running q =>
    simp only [hc, QueriesAtMost]
    intro scanned
    exact instructionTree_queries M width 0 _ _

theorem sum_map_le_constant {α : Type} (xs : List α) (f : α → Nat) (bound : Nat)
    (h : ∀ x ∈ xs, f x ≤ bound) : (xs.map f).sum ≤ xs.length * bound := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.succ_mul]
    have hx := h x List.mem_cons_self
    have hs := ih (fun y hy => h y (List.mem_cons_of_mem x hy))
    omega

theorem leaves_le_of_queries {m d : Nat} (n : Nat) (tree : Tree m d)
    (h : QueriesAtMost n tree) : tree.leaves ≤ (d + 1) ^ n := by
  induction n generalizing tree with
  | zero =>
    cases tree with
    | value v => simp [Tree.leaves]
    | query slot branches => exact False.elim h
  | succ n ih =>
    cases tree with
    | value v =>
      simp only [Tree.leaves]
      exact Nat.one_le_pow _ _ (by omega)
    | query slot branches =>
      have hs := sum_map_le_constant (List.finRange (d + 1))
        (fun v => (branches v).leaves) ((d + 1) ^ n) (fun v _ => ih _ (h v))
      simpa only [Tree.leaves, List.length_finRange, Nat.pow_succ, Nat.mul_comm] using hs

theorem transitionTree_leaves_le (M : Machine) (width : Nat) (hwidth : 0 < width)
    (i : Slot width) : (transitionTree M width hwidth i).leaves ≤ (M.states + 4) ^ 3 :=
  leaves_le_of_queries 3 _ (transitionTree_queries M width hwidth i)

/-- Each successor-cell constraint contains at most `D^4` forbidden tuples,
where `D` is the fixed finite-control/symbol domain of this machine. -/
theorem transitionTree_encode_length_le (M : Machine) (width : Nat) (hwidth : 0 < width)
    (i target : Slot width) :
    ((transitionTree M width hwidth i).encode target).length ≤ (M.states + 4) ^ 4 := by
  have he := LocalConstraint.encode_length_le (transitionTree M width hwidth i) target
  have hl := Nat.mul_le_mul_left (M.states + 4) (transitionTree_leaves_le M width hwidth i)
  have hp : (M.states + 4) * (M.states + 4) ^ 3 = (M.states + 4) ^ 4 := by
    calc
      (M.states + 4) * (M.states + 4) ^ 3 = (M.states + 4) ^ 3 * (M.states + 4) :=
        Nat.mul_comm _ _
      _ = (M.states + 4) ^ 4 := (Nat.pow_succ _ 3).symm
  rw [hp] at hl
  exact Nat.le_trans he hl

end Complexity.FiniteRows
