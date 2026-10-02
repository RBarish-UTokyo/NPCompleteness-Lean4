module

public import Complexity.NTM.Basic
import Lean.Elab.Tactic.Omega

/-!
# A small guessing machine

`guessMachine` overwrites every bit cell from the head rightwards with a guessed bit (one
choice per cell). At the first non-bit cell it turns around, walks back over the guessed
bits and halts, accepting, on the cell just left of them.

Started on a separator-delimited block of `m` bit cells, it executes exactly `2 * m + 1`
non-halting instructions, whatever the choices, and the guessed word is the first `m`
choices.
-/

@[expose] public section

namespace Complexity.NTM

def guessMachine : NMachine where
  states := 1
  start := 0
  code c q a :=
    if q = 0 then
      match a with
      | .bit _ => .step (.bit c) .right 0
      | _ => .step a .left 1
    else
      match a with
      | .bit _ => .step a .left 1
      | _ => .halt true

theorem guess_code_bit0 (c b : Bool) :
    guessMachine.code c 0 (.bit b) = .step (.bit c) .right 0 := rfl

theorem guess_code_sep0 (c : Bool) : guessMachine.code c 0 .sep = .step .sep .left 1 := rfl

theorem guess_code_bit1 (c b : Bool) :
    guessMachine.code c 1 (.bit b) = .step (.bit b) .left 1 := rfl

theorem guess_code_sep1 (c : Bool) : guessMachine.code c 1 .sep = .halt true := rfl

theorem guess_forward (R : List Symbol) : ∀ (tokens : List Bool) (acc : List Symbol)
    (gs : List Bool), gs.length = tokens.length →
    Steps guessMachine 0 ⟨acc, tokens.map Symbol.bit ++ R⟩ gs 0
      ⟨(gs.map Symbol.bit).reverse ++ acc, R⟩
  | [], acc, gs, h => by
    have hg : gs = [] := List.length_eq_zero_iff.mp (by simpa using h)
    subst hg
    exact .refl _ _
  | t :: ts, acc, gs, h => by
    cases gs with
    | nil => simp at h
    | cons g gs =>
      have hr := guess_forward R ts (.bit g :: acc) gs (by simpa using h)
      refine .step (a := .bit g) (d := .right) (q' := 0) (guess_code_bit0 g t) ?_
      simpa [Tape.write, Tape.move, List.reverse_cons, List.append_assoc] using hr

theorem guess_back (L : List Symbol) : ∀ (ys : List Bool) (h : Bool) (right : List Symbol)
    (cs : List Bool), cs.length = ys.length + 1 →
    Steps guessMachine 1 ⟨ys.map Symbol.bit ++ .sep :: L, .bit h :: right⟩ cs 1
      ⟨L, .sep :: (ys.reverse.map Symbol.bit ++ .bit h :: right)⟩
  | [], h, right, cs, hc => by
    match cs, hc with
    | [c], _ =>
      refine .step (a := .bit h) (d := .left) (q' := 1) (guess_code_bit1 c h) ?_
      simpa [Tape.write, Tape.move] using Steps.refl (N := guessMachine) 1
        ⟨L, .sep :: .bit h :: right⟩
  | y :: ys, h, right, cs, hc => by
    cases cs with
    | nil => simp at hc
    | cons c cs =>
      have hr := guess_back L ys y (.bit h :: right) cs (by simpa using hc)
      refine .step (a := .bit h) (d := .left) (q' := 1) (guess_code_bit1 c h) ?_
      simpa [Tape.write, Tape.move, List.reverse_cons, List.append_assoc] using hr

/-- The complete non-halting phase of the guessing machine on a block of `m` bit cells
delimited by separators. -/
theorem guess_phase (tokens : List Bool) (L R : List Symbol) (cs : List Bool)
    (hcs : cs.length = 2 * tokens.length + 1) :
    Steps guessMachine 0 ⟨.sep :: L, tokens.map Symbol.bit ++ .sep :: R⟩ cs 1
      ⟨L, .sep :: ((cs.take tokens.length).map Symbol.bit ++ .sep :: R)⟩ := by
  obtain ⟨gs, hgsdef⟩ : ∃ gs, cs.take tokens.length = gs := ⟨_, rfl⟩
  have hgs : gs.length = tokens.length := by rw [← hgsdef]; simp; omega
  obtain ⟨c, rest, hrest⟩ : ∃ c rest, cs.drop tokens.length = c :: rest := by
    cases h : cs.drop tokens.length with
    | nil =>
      have := congrArg List.length h
      simp at this; omega
    | cons c rest => exact ⟨c, rest, rfl⟩
  have hlen : rest.length = tokens.length := by
    have := congrArg List.length hrest
    simp at this; omega
  have hsplit : cs = gs ++ ([c] ++ rest) := by
    rw [← List.take_append_drop tokens.length cs, hrest, hgsdef]
    rfl
  rw [hgsdef, hsplit]
  refine (guess_forward (.sep :: R) tokens (.sep :: L) gs hgs).trans ?_
  refine Steps.trans (Steps.single (t := ⟨(gs.map Symbol.bit).reverse ++ .sep :: L, .sep :: R⟩)
    (guess_code_sep0 c)) ?_
  cases hrev : gs.reverse with
  | nil =>
    have hg : gs = [] := List.reverse_eq_nil_iff.mp hrev
    subst hg
    have hr : rest = [] := List.length_eq_zero_iff.mp (by rw [hlen, ← hgs]; rfl)
    subst hr
    simpa [Tape.write, Tape.move] using Steps.refl (N := guessMachine) 1 ⟨L, .sep :: .sep :: R⟩
  | cons g ys =>
    have hg : gs = ys.reverse ++ [g] := by
      rw [← List.reverse_reverse gs, hrev]; simp
    have hmap : (gs.map Symbol.bit).reverse = .bit g :: ys.map Symbol.bit := by
      rw [← List.map_reverse, hrev]; rfl
    have hb := guess_back L ys g (.sep :: R) rest (by
      have := congrArg List.length hg
      simp at this; omega)
    rw [hmap]
    rw [hg]
    simpa [Tape.write, Tape.move, List.append_assoc] using hb

theorem guess_halt (c : Bool) (t : Tape) (ht : t.read = .sep) :
    guessMachine.code c 1 t.read = .halt true := by
  rw [ht]; rfl

end Complexity.NTM
