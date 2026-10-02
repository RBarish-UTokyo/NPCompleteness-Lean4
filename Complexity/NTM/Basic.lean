module

public import Complexity.Nondeterministic
public import Complexity.TapeEquiv
public import Complexity.StackCompiler
import Lean.Elab.Tactic.Omega

/-!
# Elementary tools for nondeterministic machines

This module provides the basic vocabulary for reasoning about `NMachine.run`:

* `runD` runs a nondeterministic machine along a choice list that is extended by `false`
  once it is exhausted, and `padChoices` is the corresponding finite choice list;
* `lift` regards a deterministic machine as a nondeterministic one;
* `Steps` is the relation "from a configuration, the machine executes exactly the given
  choices without halting and reaches another configuration", with lemmas that turn such
  phases into statements about `NMachine.run`;
* `seq` runs one nondeterministic machine after another, as `sequenceMachine` does for
  deterministic machines.
-/

@[expose] public section

namespace Complexity.NTM

open StackCompiler (continueInstruction)

/-! ## Runs along padded choice lists -/

/-- Run along `choices`, using the choice `false` after the list is exhausted. -/
def runD (M : NMachine) :
    Nat → List Bool → Fin (M.states + 1) → Tape → Option (Bool × Tape)
  | 0, _, _, _ => none
  | fuel + 1, cs, q, t =>
    match M.code (cs.headD false) q t.read with
    | .halt b => some (b, t)
    | .step a d q' => runD M fuel cs.tail q' ((t.write a).move d)

/-- The first `n` choices of `cs` followed by infinitely many `false` choices. -/
def padChoices : Nat → List Bool → List Bool
  | 0, _ => []
  | n + 1, cs => cs.headD false :: padChoices n cs.tail

@[simp] theorem padChoices_length (n : Nat) (cs : List Bool) :
    (padChoices n cs).length = n := by
  induction n generalizing cs with
  | zero => rfl
  | succ n ih => simp [padChoices, ih]

theorem padChoices_eq (n : Nat) (cs : List Bool) :
    padChoices n cs = cs.take n ++ List.replicate (n - cs.length) false := by
  induction n generalizing cs with
  | zero => simp [padChoices]
  | succ n ih =>
    cases cs with
    | nil =>
      simp only [padChoices, List.headD_nil, List.tail_nil, ih, List.take_nil, List.nil_append,
        List.length_nil, Nat.sub_zero, List.replicate_succ]
    | cons c cs =>
      simp only [padChoices, List.headD_cons, List.tail_cons, ih, List.take_succ_cons,
        List.length_cons, List.cons_append, Nat.add_sub_add_right]

theorem runD_eq_run (M : NMachine) (fuel : Nat) (cs : List Bool) (q : Fin (M.states + 1))
    (t : Tape) : runD M fuel cs q t = M.run (padChoices fuel cs) q t := by
  induction fuel generalizing cs q t with
  | zero => rfl
  | succ fuel ih =>
    simp only [runD, padChoices, NMachine.run]
    cases M.code (cs.headD false) q t.read with
    | halt b => rfl
    | step a d q' => exact ih _ _ _

/-- A halting run is not affected by additional choices. -/
theorem run_append (M : NMachine) (cs ds : List Bool) (q : Fin (M.states + 1)) (t : Tape)
    (result : Bool × Tape) (h : M.run cs q t = some result) :
    M.run (cs ++ ds) q t = some result := by
  induction cs generalizing q t with
  | nil => simp [NMachine.run] at h
  | cons c cs ih =>
    simp only [NMachine.run, List.cons_append] at h ⊢
    cases hc : M.code c q t.read with
    | halt b => simpa [hc] using h
    | step a d q' =>
      rw [hc] at h
      exact ih _ _ h

/-! ## Deterministic machines -/

/-- A deterministic machine, ignoring every choice. -/
def lift (D : Machine) : NMachine := ⟨D.states, D.start, fun _ => D.code⟩

theorem lift_run (D : Machine) (cs : List Bool) (q : Fin (D.states + 1)) (t : Tape) :
    (lift D).run cs q t = Complexity.run D cs.length ⟨q, t⟩ := by
  induction cs generalizing q t with
  | nil => rfl
  | cons c cs ih =>
    simp only [NMachine.run, lift, List.length_cons, Complexity.run]
    cases D.code q t.read with
    | halt b => rfl
    | step a d q' => exact ih _ _

theorem runD_lift (D : Machine) (fuel : Nat) (cs : List Bool) (q : Fin (D.states + 1))
    (t : Tape) : runD (lift D) fuel cs q t = Complexity.run D fuel ⟨q, t⟩ := by
  induction fuel generalizing cs q t with
  | zero => rfl
  | succ fuel ih =>
    simp only [runD, lift, Complexity.run]
    cases D.code q t.read with
    | halt b => rfl
    | step a d q' => exact ih _ _ _

/-! ## Non-halting phases -/

/-- `Steps N q t cs q' t'`: from control state `q` and tape `t`, the machine executes one
non-halting instruction for each choice in `cs` and reaches `q'` and `t'`. -/
inductive Steps (N : NMachine) :
    Fin (N.states + 1) → Tape → List Bool → Fin (N.states + 1) → Tape → Prop where
  | refl (q : Fin (N.states + 1)) (t : Tape) : Steps N q t [] q t
  | step {c : Bool} {q : Fin (N.states + 1)} {t : Tape} {a : Symbol} {d : Move}
      {q' : Fin (N.states + 1)} {cs : List Bool} {q'' : Fin (N.states + 1)} {t'' : Tape}
      (hc : N.code c q t.read = .step a d q')
      (rest : Steps N q' ((t.write a).move d) cs q'' t'') : Steps N q t (c :: cs) q'' t''

namespace Steps

variable {N : NMachine}

theorem run {q : Fin (N.states + 1)} {t : Tape} {cs : List Bool} {q' : Fin (N.states + 1)}
    {t' : Tape} (h : Steps N q t cs q' t') (rest : List Bool) :
    N.run (cs ++ rest) q t = N.run rest q' t' := by
  induction h with
  | refl => rfl
  | step hc _ ih =>
    simp only [List.cons_append, NMachine.run, hc]
    exact ih

theorem trans {q : Fin (N.states + 1)} {t : Tape} {cs : List Bool} {q' : Fin (N.states + 1)}
    {t' : Tape} {ds : List Bool} {q'' : Fin (N.states + 1)} {t'' : Tape}
    (h : Steps N q t cs q' t') (h' : Steps N q' t' ds q'' t'') :
    Steps N q t (cs ++ ds) q'' t'' := by
  induction h with
  | refl => exact h'
  | step hc _ ih => exact .step hc (ih h')

theorem single {c : Bool} {q : Fin (N.states + 1)} {t : Tape} {a : Symbol} {d : Move}
    {q' : Fin (N.states + 1)} (hc : N.code c q t.read = .step a d q') :
    Steps N q t [c] q' ((t.write a).move d) := .step hc (.refl _ _)

/-- A run that stops inside a non-halting phase has not halted. -/
theorem run_prefix {q : Fin (N.states + 1)} {t : Tape} {cs : List Bool}
    {q' : Fin (N.states + 1)} {t' : Tape} (h : Steps N q t cs q' t') :
    ∀ pre suf : List Bool, cs = pre ++ suf → N.run pre q t = none := by
  induction h with
  | refl =>
    intro pre suf hcs
    cases pre with
    | nil => rfl
    | cons c pre => simp at hcs
  | step hc _ ih =>
    intro pre suf hcs
    cases pre with
    | nil => rfl
    | cons c' pre =>
      simp only [List.cons_append, List.cons.injEq] at hcs
      obtain ⟨rfl, hcs⟩ := hcs
      simp only [NMachine.run, hc]
      exact ih pre suf hcs

/-- Execution along an equivalent tape representation. -/
theorem equivalent {q : Fin (N.states + 1)} {t : Tape} {cs : List Bool}
    {q' : Fin (N.states + 1)} {t' : Tape} (h : Steps N q t cs q' t') :
    ∀ u : Tape, t.Equivalent u → ∃ u', Steps N q u cs q' u' ∧ t'.Equivalent u' := by
  induction h with
  | refl q t => exact fun u hu => ⟨u, .refl _ _, hu⟩
  | @step c q t a d q₁ cs q'' t'' hc _ ih =>
    intro u hu
    obtain ⟨u', hs, he⟩ := ih _ ((hu.write a).move d)
    refine ⟨u', .step (by rw [← hu.read]; exact hc) hs, he⟩

end Steps

/-- A phase of exactly `n` non-halting instructions, whatever the choices, splits every
sufficiently long run. -/
theorem run_phase_long {N : NMachine} {q : Fin (N.states + 1)} {t : Tape} {n : Nat}
    {P : List Bool → Fin (N.states + 1) → Tape → Prop}
    (h : ∀ cs : List Bool, cs.length = n →
      ∃ q' t', Steps N q t cs q' t' ∧ P cs q' t')
    (cs : List Bool) (hn : n ≤ cs.length) :
    ∃ q' t', P (cs.take n) q' t' ∧ N.run cs q t = N.run (cs.drop n) q' t' := by
  obtain ⟨q', t', hs, hp⟩ := h (cs.take n) (by simp [Nat.min_eq_left hn])
  refine ⟨q', t', hp, ?_⟩
  have hr := hs.run (cs.drop n)
  rwa [List.take_append_drop] at hr

theorem run_phase_short {N : NMachine} {q : Fin (N.states + 1)} {t : Tape} {n : Nat}
    (h : ∀ cs : List Bool, cs.length = n → ∃ q' t', Steps N q t cs q' t')
    (cs : List Bool) (hn : cs.length ≤ n) : N.run cs q t = none := by
  obtain ⟨q', t', hs⟩ := h (cs ++ List.replicate (n - cs.length) false) (by simp; omega)
  exact hs.run_prefix cs _ rfl

/-- A deterministic halting run consists of a choice-independent non-halting phase,
followed by the halting instruction. -/
theorem halt_steps (D : Machine) (fuel : Nat) (q : Fin (D.states + 1)) (t : Tape)
    (b : Bool) (t' : Tape) (h : Complexity.run D fuel ⟨q, t⟩ = some (b, t')) :
    ∃ n q', n < fuel ∧
      (∀ cs : List Bool, cs.length = n → Steps (lift D) q t cs q' t') ∧
      D.code q' t'.read = .halt b := by
  induction fuel generalizing q t with
  | zero => simp [Complexity.run] at h
  | succ fuel ih =>
    cases hc : D.code q t.read with
    | halt b' =>
      have heq : (b', t) = (b, t') := by simpa [Complexity.run, hc] using h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
      refine ⟨0, q, by omega, ?_, hc⟩
      intro cs hcs
      rw [List.length_eq_zero_iff.mp hcs]
      exact .refl _ _
    | step a d q₁ =>
      have h' : Complexity.run D fuel ⟨q₁, (t.write a).move d⟩ = some (b, t') := by
        simpa [Complexity.run, hc] using h
      obtain ⟨n, q', hn, hs, hq⟩ := ih q₁ _ h'
      refine ⟨n + 1, q', by omega, ?_, hq⟩
      intro cs hcs
      cases cs with
      | nil => simp at hcs
      | cons c cs => exact .step (N := lift D) hc (hs cs (by simpa using hcs))

/-! ## Sequential composition -/

def seqLeft (A B : NMachine) (q : Fin (A.states + 1)) : Fin (A.states + B.states + 1 + 1) :=
  ⟨q.val, by have := q.isLt; omega⟩

def seqRight (A B : NMachine) (q : Fin (B.states + 1)) : Fin (A.states + B.states + 1 + 1) :=
  ⟨A.states + 1 + q.val, by have := q.isLt; omega⟩

/-- Run `A`; when it accepts, continue with `B` on the same tape (one extra instruction);
when it rejects, reject. -/
def seq (A B : NMachine) : NMachine where
  states := A.states + B.states + 1
  start := seqLeft A B A.start
  code c q a :=
    if h : q.val < A.states + 1 then
      continueInstruction (seqLeft A B) (seqRight A B B.start) a (A.code c ⟨q.val, h⟩ a)
    else
      (B.code c ⟨q.val - (A.states + 1), by have := q.isLt; omega⟩ a).mapState (seqRight A B)

theorem seq_code_left (A B : NMachine) (c : Bool) (q : Fin (A.states + 1)) (a : Symbol) :
    (seq A B).code c (seqLeft A B q) a =
      continueInstruction (seqLeft A B) (seqRight A B B.start) a (A.code c q a) := by
  simp [seq, seqLeft, q.isLt]

theorem seq_code_right (A B : NMachine) (c : Bool) (q : Fin (B.states + 1)) (a : Symbol) :
    (seq A B).code c (seqRight A B q) a = (B.code c q a).mapState (seqRight A B) := by
  have h : ¬ A.states + 1 + q.val < A.states + 1 := by omega
  simp [seq, seqRight, h]

theorem Steps.seqLeft {A B : NMachine} {q : Fin (A.states + 1)} {t : Tape} {cs : List Bool}
    {q' : Fin (A.states + 1)} {t' : Tape} (h : Steps A q t cs q' t') :
    Steps (seq A B) (NTM.seqLeft A B q) t cs (NTM.seqLeft A B q') t' := by
  induction h with
  | refl => exact .refl _ _
  | step hc _ ih =>
    refine .step ?_ ih
    rw [seq_code_left, hc]
    rfl

theorem Steps.seqRight {A B : NMachine} {q : Fin (B.states + 1)} {t : Tape} {cs : List Bool}
    {q' : Fin (B.states + 1)} {t' : Tape} (h : Steps B q t cs q' t') :
    Steps (seq A B) (NTM.seqRight A B q) t cs (NTM.seqRight A B q') t' := by
  induction h with
  | refl => exact .refl _ _
  | step hc _ ih =>
    refine .step ?_ ih
    rw [seq_code_right, hc]
    rfl

/-- The accepting halt of the first machine becomes one instruction entering the second
machine; it rewrites the scanned symbol. -/
theorem steps_continue (A B : NMachine) (c : Bool) (q : Fin (A.states + 1)) (t : Tape)
    (hc : A.code c q t.read = .halt true) :
    Steps (seq A B) (seqLeft A B q) t [c] (seqRight A B B.start) (t.write t.read) := by
  have h := Steps.single (N := seq A B) (c := c) (q := seqLeft A B q) (t := t) (a := t.read)
    (d := .stay) (q' := seqRight A B B.start) (by rw [seq_code_left, hc]; rfl)
  simpa [Tape.move] using h

theorem run_seqRight (A B : NMachine) (cs : List Bool) (q : Fin (B.states + 1)) (t : Tape) :
    (seq A B).run cs (seqRight A B q) t = B.run cs q t := by
  induction cs generalizing q t with
  | nil => rfl
  | cons c cs ih =>
    simp only [NMachine.run, seq_code_right]
    cases B.code c q t.read with
    | halt b => rfl
    | step a d q' => exact ih _ _

theorem write_read_equivalent (t : Tape) : (t.write t.read).Equivalent t := by
  cases t with
  | mk left right =>
    cases right with
    | nil =>
      refine ⟨BlankEq.refl _, ?_⟩
      simpa [Tape.write, Tape.read] using BlankEq.replicate_blank 1
    | cons a rest => exact Tape.Equivalent.refl _

end Complexity.NTM
