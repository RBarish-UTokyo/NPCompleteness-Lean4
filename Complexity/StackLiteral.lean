module

public import Complexity.StackWords
public import Complexity.StackParse
public import Complexity.SATVerifier
import Lean.Elab.Tactic.Omega

/-! A literal parser/evaluator using only individual stack operations. -/

@[expose] public section

namespace Complexity.StackLiteral

open Complexity.StackProgram
open Complexity.StackMachine (Registers branch)
open Complexity.StackWords (set_overwrite set_unchanged)
open Complexity.SAT (Literal writeNat encodeLiteral)

inductive Label where
  | start | scan (positive : Bool) | drop (positive : Bool) | test (positive : Bool)
  | yes | success | failure
  deriving DecidableEq, Repr

def encoding : Encoding Label where
  states := 9
  encode := fun q => match q with
    | .start => 0 | .scan false => 1 | .scan true => 2
    | .drop false => 3 | .drop true => 4 | .test false => 5 | .test true => 6
    | .yes => 7 | .success => 8 | .failure => 9
  decode := fun q => if q = 0 then .start else if q = 1 then .scan false
    else if q = 2 then .scan true else if q = 3 then .drop false
    else if q = 4 then .drop true else if q = 5 then .test false
    else if q = 6 then .test true else if q = 7 then .yes
    else if q = 8 then .success else .failure
  decode_encode := by intro q; cases q with
    | start | yes | success | failure => rfl
    | scan b | drop b | test b => cases b <;> rfl

def value (positive : Bool) (word : List Bool) (index : Nat) : Bool :=
  Complexity.SAT.evalLiteral (Complexity.SATVerifier.assignment word) ⟨index, positive⟩

theorem value_tail (positive : Bool) (word : List Bool) (index : Nat) :
    value positive word.tail index = value positive word (index + 1) := by
  cases word <;> simp [value, Complexity.SAT.evalLiteral, Complexity.SATVerifier.assignment]

/-- The work register initially contains the finite assignment certificate. -/
def core {k : Nat} (input work flag : Fin (k + 1)) : Program k Label where
  start := .start
  code := fun q => match q with
    | .start => .pop input .failure (.scan false) (.scan true)
    | .scan positive => .pop input .failure (.test positive) (.drop positive)
    | .drop positive => .pop work (.scan positive) (.scan positive) (.scan positive)
    | .test positive => if positive then .peek work .success .success .yes
      else .peek work .yes .yes .success
    | .yes => .push flag true .success
    | .success => .halt true
    | .failure => .halt false

theorem exec_test {k : Nat} (input work flag : Fin (k + 1))
    (positive : Bool) (r : Registers k) :
    Exec (core input work flag) (.test positive) r
      (2 + if value positive (r work) 0 then 1 else 0)
      (true, StackMachine.set r flag
        (if value positive (r work) 0 then true :: r flag else r flag)) := by
  cases positive <;> cases hw : r work with
  | nil =>
    simp [value, Complexity.SAT.evalLiteral, Complexity.SATVerifier.assignment]
    first
    | exact .next (q' := .success) (r' := r)
        (by simp [StackProgram.step, core, hw, branch]) (.halt rfl)
    | exact .next (q' := .yes) (r' := r)
        (by simp [StackProgram.step, core, hw, branch])
        (.next (q' := .success) (r' := StackMachine.set r flag (true :: r flag)) rfl (.halt rfl))
  | cons b tail =>
    cases b <;>
      simp [value, Complexity.SAT.evalLiteral, Complexity.SATVerifier.assignment]
    all_goals first
    | exact .next (q' := .success) (r' := r)
        (by simp [StackProgram.step, core, hw, branch]) (.halt rfl)
    | exact .next (q' := .yes) (r' := r)
        (by simp [StackProgram.step, core, hw, branch])
        (.next (q' := .success) (r' := StackMachine.set r flag (true :: r flag)) rfl (.halt rfl))

def finish {k : Nat} (input work flag : Fin (k + 1)) (positive : Bool)
    (r : Registers k) (index : Nat) (rest : List Bool) : Registers k :=
  StackMachine.set (StackMachine.set (StackMachine.set r input rest) work ((r work).drop index)) flag
    (if value positive (r work) index then true :: r flag else r flag)

theorem finish_scan_step {k : Nat} (input work flag : Fin (k + 1))
    (_hiw : input ≠ work) (hif : input ≠ flag) (hwf : work ≠ flag)
    (positive : Bool) (r : Registers k) (index : Nat) (rest : List Bool) :
    finish input work flag positive
      (StackMachine.set (StackMachine.set r input (writeNat index ++ rest)) work (r work).tail)
      index rest = finish input work flag positive r (index + 1) rest := by
  funext a
  by_cases hf : a = flag
  · subst a
    simp [finish, Ne.symm hif, Ne.symm hwf, value_tail]
  · by_cases hw : a = work
    · subst a
      simp [finish, hf, List.drop_tail]
    · by_cases hi : a = input
      · subst a
        simp [finish, hf, hw]
      · simp [finish, StackMachine.set, hf, hw, hi]

theorem exec_scan_encoded {k : Nat} (input work flag : Fin (k + 1))
    (hiw : input ≠ work) (hif : input ≠ flag) (hwf : work ≠ flag)
    (positive : Bool) (index : Nat) (rest : List Bool) (r : Registers k)
    (hr : r input = writeNat index ++ rest) :
    Exec (core input work flag) (.scan positive) r
      (2 * index + 3 + if value positive (r work) index then 1 else 0)
      (true, finish input work flag positive r index rest) := by
  induction index generalizing r with
  | zero =>
    have hpop : StackProgram.step (core input work flag) (.scan positive) r =
        .inr (.test positive, StackMachine.set r input rest) := by
      simp [StackProgram.step, core, hr, writeNat, branch]
    have ht := exec_test input work flag positive (StackMachine.set r input rest)
    have hh := Exec.next hpop ht
    have hf : finish input work flag positive r 0 rest =
        StackMachine.set (StackMachine.set r input rest) flag
          (if value positive (r work) 0 then true :: r flag else r flag) := by
      have hsame : (StackMachine.set r input rest) work = r work := by simp [Ne.symm hiw]
      simp only [finish, List.drop_zero]
      rw [← hsame, set_unchanged]
    simp [Ne.symm hiw, Ne.symm hif] at hh
    rw [hf]
    have hcost : (2 + if value positive (r work) 0 then 1 else 0) + 1 =
        2 * 0 + 3 + (if value positive (r work) 0 then 1 else 0) := by omega
    rw [hcost] at hh
    exact hh
  | succ index ih =>
    let r' := StackMachine.set (StackMachine.set r input (writeNat index ++ rest)) work (r work).tail
    have hr' : r' input = writeNat index ++ rest := by simp [r', hiw]
    have ht := ih r' hr'
    have hpop : StackProgram.step (core input work flag) (.scan positive) r =
        .inr (.drop positive, StackMachine.set r input (writeNat index ++ rest)) := by
      simp [StackProgram.step, core, hr, writeNat, branch]
    have hdrop : StackProgram.step (core input work flag) (.drop positive)
        (StackMachine.set r input (writeNat index ++ rest)) = .inr (.scan positive, r') := by
      simp [StackProgram.step, core, r', Ne.symm hiw, branch]
      cases r work with
      | nil => rfl
      | cons b tail => cases b <;> rfl
    have hh := Exec.next hpop (Exec.next hdrop ht)
    have hfinish := finish_scan_step input work flag hiw hif hwf positive r index rest
    change finish input work flag positive r' index rest = _ at hfinish
    rw [hfinish] at hh
    have hvalue : value positive (r' work) index = value positive (r work) (index + 1) := by
      simp [r', value_tail]
    rw [hvalue] at hh
    have hcost : 2 * index + 3 + (if value positive (r work) (index + 1) then 1 else 0) + 1 + 1 =
        2 * (index + 1) + 3 + (if value positive (r work) (index + 1) then 1 else 0) := by omega
    rw [hcost] at hh
    exact hh

theorem exec_core_encoded {k : Nat} (input work flag : Fin (k + 1))
    (hiw : input ≠ work) (hif : input ≠ flag) (hwf : work ≠ flag)
    (literal : Literal) (rest : List Bool) (r : Registers k)
    (hr : r input = encodeLiteral literal ++ rest) :
    Exec (core input work flag) .start r
      (2 * literal.var + 4 + if value literal.positive (r work) literal.var then 1 else 0)
      (true, finish input work flag literal.positive r literal.var rest) := by
  let r' := StackMachine.set r input (writeNat literal.var ++ rest)
  have hs : StackProgram.step (core input work flag) .start r = .inr (.scan literal.positive, r') := by
    cases hp : literal.positive <;> simp [StackProgram.step, core, hr, encodeLiteral, hp, branch, r']
  have ht := exec_scan_encoded input work flag hiw hif hwf literal.positive literal.var rest r' (by simp [r'])
  have hh := Exec.next hs ht
  have hf : finish input work flag literal.positive r' literal.var rest =
      finish input work flag literal.positive r literal.var rest := by
    funext a
    by_cases ha : a = flag
    · subst a; simp [finish, r', Ne.symm hiw, Ne.symm hif]
    · by_cases hb : a = work
      · subst a; simp [finish, r', ha, Ne.symm hiw]
      · by_cases hc : a = input
        · subst a; simp [finish, r', ha, hb]
        · simp [finish, r', StackMachine.set, ha, hb, hc]
  rw [hf] at hh
  have hvalue : value literal.positive (r' work) literal.var = value literal.positive (r work) literal.var := by
    simp [r', Ne.symm hiw]
  rw [hvalue] at hh
  have hcost : 2 * literal.var + 3 + (if value literal.positive (r work) literal.var then 1 else 0) + 1 =
      2 * literal.var + 4 + (if value literal.positive (r work) literal.var then 1 else 0) := by omega
  rw [hcost] at hh
  exact hh

def failureFinish {k : Nat} (input work : Fin (k + 1)) (r : Registers k) (n : Nat) : Registers k :=
  StackMachine.set (StackMachine.set r input []) work ((r work).drop n)

theorem exec_scan_malformed {k : Nat} (input work flag : Fin (k + 1)) (hiw : input ≠ work)
    (positive : Bool) (n : Nat) (r : Registers k) (hr : r input = List.replicate n true) :
    Exec (core input work flag) (.scan positive) r (2 * n + 2)
      (false, failureFinish input work r n) := by
  induction n generalizing r with
  | zero =>
    have hf : failureFinish input work r 0 = StackMachine.set r input [] := by
      have hh : (StackMachine.set r input []) work = r work := by simp [Ne.symm hiw]
      simp only [failureFinish, List.drop_zero]
      rw [← hh, set_unchanged]
    rw [hf]
    apply Exec.next (q' := .failure) (r' := StackMachine.set r input [])
    · simp [StackProgram.step, core, hr, branch]
    · exact .halt rfl
  | succ n ih =>
    let r' := StackMachine.set (StackMachine.set r input (List.replicate n true)) work (r work).tail
    have ht := ih r' (by simp [r', hiw])
    have hpop : StackProgram.step (core input work flag) (.scan positive) r =
        .inr (.drop positive, StackMachine.set r input (List.replicate n true)) := by
      simp [StackProgram.step, core, hr, List.replicate_succ, branch]
    have hdrop : StackProgram.step (core input work flag) (.drop positive)
        (StackMachine.set r input (List.replicate n true)) = .inr (.scan positive, r') := by
      simp [StackProgram.step, core, r', Ne.symm hiw, branch]
      cases r work with
      | nil => rfl
      | cons b tail => cases b <;> rfl
    have hh := Exec.next hpop (Exec.next hdrop ht)
    have hf : failureFinish input work r' n = failureFinish input work r (n + 1) := by
      funext a
      by_cases hw : a = work
      · subst a; simp [failureFinish, r', List.drop_tail]
      · by_cases ha : a = input
        · subst a; simp [failureFinish, r', hw]
        · simp [failureFinish, r', StackMachine.set, hw, ha]
    rw [hf] at hh
    simpa [Nat.mul_add, Nat.add_assoc] using hh

theorem exec_core_empty {k : Nat} (input work flag : Fin (k + 1))
    (r : Registers k) (hr : r input = []) : Exec (core input work flag) .start r 2 (false, r) := by
  have hset : StackMachine.set r input [] = r := by rw [← hr, set_unchanged]
  apply Exec.next (q' := .failure) (r' := r)
  · simp [StackProgram.step, core, hr, branch, hset]
  · exact .halt rfl

theorem exec_core_malformed {k : Nat} (input work flag : Fin (k + 1)) (hiw : input ≠ work)
    (positive : Bool) (n : Nat) (r : Registers k)
    (hr : r input = positive :: List.replicate n true) :
    Exec (core input work flag) .start r (2 * n + 3) (false, failureFinish input work r n) := by
  let r' := StackMachine.set r input (List.replicate n true)
  have hs : StackProgram.step (core input work flag) .start r = .inr (.scan positive, r') := by
    cases positive <;> simp [StackProgram.step, core, hr, branch, r']
  have ht := exec_scan_malformed input work flag hiw positive n r' (by simp [r'])
  have hh := Exec.next hs ht
  have hf : failureFinish input work r' n = failureFinish input work r n := by
    funext a
    by_cases hw : a = work
    · subst a; simp [failureFinish, r', Ne.symm hiw]
    · by_cases ha : a = input
      · subst a; simp [failureFinish, r', hw]
      · simp [failureFinish, r', StackMachine.set, hw, ha]
  rw [hf] at hh
  simpa [Nat.add_assoc] using hh

theorem core_failure {k : Nat} (input work flag : Fin (k + 1)) (hiw : input ≠ work)
    (r : Registers k) (h : Complexity.SAT.readLiteral (r input) = none) :
    ∃ t out, t ≤ 2 * (r input).length + 5 ∧ Exec (core input work flag) .start r t (false, out) := by
  cases hr : r input with
  | nil => exact ⟨2, r, by simp, exec_core_empty input work flag r hr⟩
  | cons positive tail =>
    cases hn : Complexity.SAT.readNat tail with
    | none =>
      have hall := Complexity.StackParse.readNat_none_eq hn
      have hh := exec_core_malformed input work flag hiw positive tail.length r
        (by rw [hr]; exact congrArg (List.cons positive) hall)
      refine ⟨2 * tail.length + 3, _, ?_, hh⟩
      simp only [List.length_cons]
      omega
    | some result => simp [Complexity.SAT.readLiteral, hr, hn] at h

/-- Pairwise distinct register roles for one literal evaluation. -/
structure Valid {k : Nat} (input certificate work scratch flag : Fin (k + 1)) : Prop where
  input_certificate : input ≠ certificate
  input_work : input ≠ work
  input_scratch : input ≠ scratch
  input_flag : input ≠ flag
  certificate_work : certificate ≠ work
  certificate_scratch : certificate ≠ scratch
  certificate_flag : certificate ≠ flag
  work_scratch : work ≠ scratch
  work_flag : work ≠ flag
  scratch_flag : scratch ≠ flag

def literalBody {k : Nat} (input certificate work scratch flag : Fin (k + 1)) :=
  seq (Complexity.StackWords.copy certificate work scratch) (core input work flag)

def literalEncoding := Complexity.StackWords.copyMapEncoding.sum encoding

def bodyFinish {k : Nat} (input certificate work flag : Fin (k + 1)) (r : Registers k)
    (l : Literal) (rest : List Bool) : Registers k :=
  StackMachine.set (StackMachine.set (StackMachine.set r input rest) work ((r certificate).drop l.var)) flag
    (if Complexity.SAT.evalLiteral (Complexity.SATVerifier.assignment (r certificate)) l
      then true :: r flag else r flag)

theorem finish_copy {k : Nat} (input certificate work scratch flag : Fin (k + 1))
    (h : Valid input certificate work scratch flag) (r : Registers k) (l : Literal) (rest : List Bool) :
    finish input work flag l.positive (StackMachine.set r work (r certificate)) l.var rest =
      bodyFinish input certificate work flag r l rest := by
  cases l with
  | mk n positive =>
    funext a
    by_cases hf : a = flag
    · subst a
      simp [finish, bodyFinish, value, Ne.symm h.work_flag]
    · by_cases hw : a = work
      · subst a; simp [finish, bodyFinish, hf]
      · by_cases hi : a = input
        · subst a; simp [finish, bodyFinish, hf, hw]
        · simp [finish, bodyFinish, StackMachine.set, hf, hw, hi]

theorem literalBody_success {k : Nat} (input certificate work scratch flag : Fin (k + 1))
    (h : Valid input certificate work scratch flag) (r : Registers k) (hempty : r scratch = [])
    (l : Literal) (rest : List Bool) (hr : Complexity.SAT.readLiteral (r input) = some (l, rest)) :
    Exec (literalBody input certificate work scratch flag)
      (literalBody input certificate work scratch flag).start r
      ((r work).length + 5 * (r certificate).length + 6 +
        (2 * l.var + 4 + if Complexity.SAT.evalLiteral (Complexity.SATVerifier.assignment (r certificate)) l then 1 else 0))
      (true, bodyFinish input certificate work flag r l rest) := by
  let r' := StackMachine.set r work (r certificate)
  have hc := Complexity.StackWords.exec_copy certificate work scratch h.certificate_work
    h.certificate_scratch h.work_scratch r hempty
  have hi : r' input = encodeLiteral l ++ rest := by
    simp only [r', StackMachine.set_other r h.input_work]
    exact Complexity.SAT.readLiteral_eq_some hr
  have he := exec_core_encoded input work flag h.input_work h.input_flag h.work_flag l rest r' hi
  have hh := exec_seq (Complexity.StackWords.copy certificate work scratch) (core input work flag) hc he
  have hf := finish_copy input certificate work scratch flag h r l rest
  rw [hf] at hh
  have hv : value l.positive (r' work) l.var =
      Complexity.SAT.evalLiteral (Complexity.SATVerifier.assignment (r certificate)) l := by
    cases l
    simp [r', value]
  rw [hv] at hh
  exact hh

theorem literalBody_failure {k : Nat} (input certificate work scratch flag : Fin (k + 1))
    (h : Valid input certificate work scratch flag) (r : Registers k) (hempty : r scratch = [])
    (bound : Nat) (hi : (r input).length ≤ bound) (hc : (r certificate).length ≤ bound)
    (hw : (r work).length ≤ bound) (hr : Complexity.SAT.readLiteral (r input) = none) :
    ∃ t out, t ≤ 8 * bound + 12 ∧ Exec (literalBody input certificate work scratch flag)
      (literalBody input certificate work scratch flag).start r t (false, out) := by
  let r' := StackMachine.set r work (r certificate)
  have hcopy := Complexity.StackWords.exec_copy certificate work scratch h.certificate_work
    h.certificate_scratch h.work_scratch r hempty
  have hr' : Complexity.SAT.readLiteral (r' input) = none := by simpa [r', h.input_work] using hr
  obtain ⟨t, out, ht, he⟩ := core_failure input work flag h.input_work r' hr'
  have hh := exec_seq (Complexity.StackWords.copy certificate work scratch) (core input work flag) hcopy he
  refine ⟨(r work).length + 5 * (r certificate).length + 6 + t, out, ?_, hh⟩
  simp only [r', StackMachine.set_other r h.input_work] at ht
  omega

theorem literalBody_success_bound {k : Nat} (input certificate work scratch flag : Fin (k + 1))
    (h : Valid input certificate work scratch flag) (r : Registers k) (hempty : r scratch = [])
    (bound : Nat) (hi : (r input).length ≤ bound) (hc : (r certificate).length ≤ bound)
    (hw : (r work).length ≤ bound) (l : Literal) (rest : List Bool)
    (hr : Complexity.SAT.readLiteral (r input) = some (l, rest)) :
    ∃ t, t ≤ 8 * bound + 12 ∧ Exec (literalBody input certificate work scratch flag)
      (literalBody input certificate work scratch flag).start r t
      (true, bodyFinish input certificate work flag r l rest) := by
  have he := literalBody_success input certificate work scratch flag h r hempty l rest hr
  refine ⟨_, ?_, he⟩
  have hinput := Complexity.SAT.readLiteral_eq_some hr
  have hlen := congrArg List.length hinput
  simp only [List.length_append, Complexity.SATBounds.encodeLiteral_length] at hlen
  split <;> omega

theorem bodyFinish_input {k : Nat} (input certificate work scratch flag : Fin (k + 1))
    (h : Valid input certificate work scratch flag) (r : Registers k) (l : Literal) (rest : List Bool) :
    bodyFinish input certificate work flag r l rest input = rest := by
  simp [bodyFinish, h.input_flag, h.input_work]

theorem bodyFinish_work {k : Nat} (input certificate work scratch flag : Fin (k + 1))
    (h : Valid input certificate work scratch flag) (r : Registers k) (l : Literal) (rest : List Bool) :
    bodyFinish input certificate work flag r l rest work = (r certificate).drop l.var := by
  simp [bodyFinish, h.work_flag]

theorem bodyFinish_flag {k : Nat} (input certificate work flag : Fin (k + 1))
    (r : Registers k) (l : Literal) (rest : List Bool) :
    bodyFinish input certificate work flag r l rest flag =
      (if Complexity.SAT.evalLiteral (Complexity.SATVerifier.assignment (r certificate)) l
        then true :: r flag else r flag) := by simp [bodyFinish]

theorem bodyFinish_frame {k : Nat} (input certificate work flag a : Fin (k + 1))
    (hi : a ≠ input) (hw : a ≠ work) (hf : a ≠ flag)
    (r : Registers k) (l : Literal) (rest : List Bool) :
    bodyFinish input certificate work flag r l rest a = r a := by
  simp [bodyFinish, hi, hw, hf]

theorem bodyFinish_certificate {k : Nat} (input certificate work scratch flag : Fin (k + 1))
    (h : Valid input certificate work scratch flag) (r : Registers k) (l : Literal) (rest : List Bool) :
    bodyFinish input certificate work flag r l rest certificate = r certificate :=
  bodyFinish_frame input certificate work flag certificate (Ne.symm h.input_certificate)
    h.certificate_work h.certificate_flag r l rest

theorem bodyFinish_scratch {k : Nat} (input certificate work scratch flag : Fin (k + 1))
    (h : Valid input certificate work scratch flag) (r : Registers k) (l : Literal) (rest : List Bool) :
    bodyFinish input certificate work flag r l rest scratch = r scratch :=
  bodyFinish_frame input certificate work flag scratch (Ne.symm h.input_scratch)
    (Ne.symm h.work_scratch) h.scratch_flag r l rest

/-- A successful literal consumes at least two input bits and adds at most one flag bit. -/
theorem bodyFinish_measure {k : Nat} (input certificate work scratch flag : Fin (k + 1))
    (h : Valid input certificate work scratch flag) (r : Registers k) (l : Literal) (rest : List Bool)
    (hr : Complexity.SAT.readLiteral (r input) = some (l, rest)) :
    (bodyFinish input certificate work flag r l rest input).length +
      (bodyFinish input certificate work flag r l rest flag).length + 1 ≤
      (r input).length + (r flag).length := by
  rw [bodyFinish_input input certificate work scratch flag h, bodyFinish_flag]
  have hlen := congrArg List.length (Complexity.SAT.readLiteral_eq_some hr)
  simp only [List.length_append, Complexity.SATBounds.encodeLiteral_length] at hlen
  split
  · simp only [List.length_cons]
    omega
  · omega

theorem literalBody_runs {k : Nat} (input certificate work scratch flag : Fin (k + 1))
    (h : Valid input certificate work scratch flag) (r : Registers k) (hempty : r scratch = [])
    (bound : Nat) (hi : (r input).length ≤ bound) (hc : (r certificate).length ≤ bound)
    (hw : (r work).length ≤ bound) :
    ∃ t out, t ≤ 8 * bound + 12 ∧ Exec (literalBody input certificate work scratch flag)
      (literalBody input certificate work scratch flag).start r t
      ((Complexity.SAT.readLiteral (r input)).isSome, out) ∧
      ∀ l rest, Complexity.SAT.readLiteral (r input) = some (l, rest) →
        out = bodyFinish input certificate work flag r l rest := by
  cases hr : Complexity.SAT.readLiteral (r input) with
  | none =>
    obtain ⟨t, out, ht, he⟩ := literalBody_failure input certificate work scratch flag h r hempty bound hi hc hw hr
    exact ⟨t, out, ht, by simpa [hr] using he, by intro l rest hp; simp at hp⟩
  | some result =>
    obtain ⟨l, rest⟩ := result
    obtain ⟨t, ht, he⟩ := literalBody_success_bound input certificate work scratch flag h r hempty bound hi hc hw l rest hr
    refine ⟨t, _, ht, by simpa [hr] using he, ?_⟩
    intro l' rest' hp
    have heq : l = l' ∧ rest = rest' := by simpa [hr] using hp
    rcases heq with ⟨rfl, rfl⟩
    rfl

/-- A uniform linear bound in the actual compiled Boolean stack machine. -/
theorem compiled_literalBody_runs {k : Nat} (input certificate work scratch flag : Fin (k + 1))
    (h : Valid input certificate work scratch flag) (r : Registers k) (hempty : r scratch = [])
    (bound : Nat) (hi : (r input).length ≤ bound) (hc : (r certificate).length ≤ bound)
    (hw : (r work).length ≤ bound) :
    ∃ out, StackMachine.run (compile (literalBody input certificate work scratch flag) literalEncoding)
      (8 * bound + 12)
      ⟨(compile (literalBody input certificate work scratch flag) literalEncoding).start, r⟩ =
        some ((Complexity.SAT.readLiteral (r input)).isSome, out) ∧
      ∀ l rest, Complexity.SAT.readLiteral (r input) = some (l, rest) →
        out = bodyFinish input certificate work flag r l rest := by
  obtain ⟨t, out, ht, he, hout⟩ := literalBody_runs input certificate work scratch flag h r hempty bound hi hc hw
  refine ⟨out, ?_, hout⟩
  exact StackMachine.run_mono _ ht _ _ (compile_exec literalEncoding he)

end Complexity.StackLiteral
