module

public import Complexity.StackTableauArithmetic

/-!
A finite syntax for tableau-generator programs. Each command compiles to a
finite graph of elementary Boolean-stack instructions. The inductive execution
judgments expose full register contents and count the real primitive costs.
Arithmetic rules require distinct work registers and an empty scratch register;
those are proof obligations of clients, not assumed global invariants.
-/

@[expose] public section

namespace Complexity.StackTableauProgram

open StackMachine (Registers set)
open StackProgram (Program Encoding)
open StackTableauArithmetic

/-- Run a test and enter the branch selected by its halting decision. -/
def select {k : Nat} {A B C : Type} (test : Program k A) (yes : Program k B)
    (no : Program k C) : Program k (Sum A (Sum B C)) where
  start := .inl test.start
  code := fun q => match q with
    | .inl a => StackProgram.mapOp Sum.inl
        (fun b => .goto (if b then .inr (.inl yes.start) else .inr (.inr no.start))) (test.code a)
    | .inr (.inl b) => StackProgram.mapOp (fun x => .inr (.inl x)) StackProgram.Op.halt (yes.code b)
    | .inr (.inr c) => StackProgram.mapOp (fun x => .inr (.inr x)) StackProgram.Op.halt (no.code c)

theorem select_step_test {k : Nat} {A B C : Type} (test : Program k A)
    (yes : Program k B) (no : Program k C) (a : A) (r : Registers k) :
    StackProgram.step (select test yes no) (.inl a) r =
      match StackProgram.step test a r with
      | .inl (decision, out) =>
          .inr ((if decision then .inr (.inl yes.start) else .inr (.inr no.start)), out)
      | .inr (next, out) => .inr (.inl next, out) := by
  cases hc : test.code a <;>
    simp [StackProgram.step, select, StackProgram.mapOp, hc, StackProgram.branch_map]

theorem exec_select_yes {k : Nat} {A B C : Type} (test : Program k A)
    (yes : Program k B) (no : Program k C) {a r t middle s result}
    (ht : StackProgram.Exec test a r t (true, middle))
    (hy : StackProgram.Exec yes yes.start middle s result) :
    StackProgram.Exec (select test yes no) (.inl a) r (t + s) result := by
  apply StackProgram.exec_link test (select test yes no) Sum.inl ht
  · intro a r a' r' hs
    rw [select_step_test, hs]
  · intro a r hs
    apply StackProgram.Exec.next (q' := .inr (.inl yes.start)) (r' := middle)
    · simp [select_step_test, hs]
    · exact StackProgram.exec_embed yes (select test yes no)
        (fun b => .inr (.inl b)) (by intro b; rfl) hy

theorem exec_select_no {k : Nat} {A B C : Type} (test : Program k A)
    (yes : Program k B) (no : Program k C) {a r t middle s result}
    (ht : StackProgram.Exec test a r t (false, middle))
    (hn : StackProgram.Exec no no.start middle s result) :
    StackProgram.Exec (select test yes no) (.inl a) r (t + s) result := by
  apply StackProgram.exec_link test (select test yes no) Sum.inl ht
  · intro a r a' r' hs
    rw [select_step_test, hs]
  · intro a r hs
    apply StackProgram.Exec.next (q' := .inr (.inr no.start)) (r' := middle)
    · simp [select_step_test, hs]
    · exact StackProgram.exec_embed no (select test yes no)
        (fun c => .inr (.inr c)) (by intro c; rfl) hn

inductive Command (k : Nat) where
  | stop (decision : Bool)
  | push (register : Fin (k + 1)) (bit : Bool)
  | pop (register : Fin (k + 1))
  | clear (register : Fin (k + 1))
  | copy (src dst scratch : Fin (k + 1))
  | length (src dst scratch : Fin (k + 1))
  | add (src dst scratch : Fin (k + 1))
  | multiply (src factor dst counter scratch : Fin (k + 1))
  | prependNat (number output scratch : Fin (k + 1))
  | prependLiteral (number output scratch : Fin (k + 1)) (sign : Bool)
  | seq (first second : Command k)
  | ifThenElse (test yes no : Command k)
  | branch (register : Fin (k + 1)) (empty zero one : Command k)
  | repeat (counter : Fin (k + 1)) (body : Command k)

abbrev CopyLabel := Sum Bool (Sum (Fin 4) (Fin 6))

def Label {k : Nat} : Command k → Type
  | .stop _ => Unit
  | .push _ _ => Bool
  | .pop _ => Bool
  | .clear _ => Bool
  | .copy _ _ _ => CopyLabel
  | .length _ _ _ => CopyLabel
  | .add _ _ _ => AddLabel
  | .multiply _ _ _ _ _ => MultiplyLabel
  | .prependNat _ _ _ => PrependNatLabel
  | .prependLiteral _ _ _ _ => PrependLiteralLabel
  | .seq first second => Sum (Label first) (Label second)
  | .ifThenElse test yes no => Sum (Label test) (Sum (Label yes) (Label no))
  | .branch _ empty zero one => Sum Unit (Sum (Label empty) (Sum (Label zero) (Label one)))
  | .repeat _ body => Sum Bool (Label body)

def encoding {k : Nat} : (command : Command k) → Encoding (Label command)
  | .stop _ => Encoding.unit
  | .push _ _ => Encoding.bool
  | .pop _ => Encoding.bool
  | .clear _ => Encoding.bool
  | .copy _ _ _ => StackWords.copyMapEncoding
  | .length _ _ _ => StackWords.copyMapEncoding
  | .add _ _ _ => addEncoding
  | .multiply _ _ _ _ _ => multiplyEncoding
  | .prependNat _ _ _ => prependNatEncoding
  | .prependLiteral _ _ _ _ => prependLiteralEncoding
  | .seq first second => (encoding first).sum (encoding second)
  | .ifThenElse test yes no => (encoding test).sum ((encoding yes).sum (encoding no))
  | .branch _ empty zero one =>
      Encoding.unit.sum ((encoding empty).sum ((encoding zero).sum (encoding one)))
  | .repeat _ body => Encoding.bool.sum (encoding body)

def compile {k : Nat} : (command : Command k) → Program k (Label command)
  | .stop b => StackProgram.stop k b
  | .push j b => StackProgram.push j b
  | .pop j => StackProgram.pop j
  | .clear j => StackWords.clear j
  | .copy src dst scratch => StackWords.copy src dst scratch
  | .length src dst scratch => StackWords.length src dst scratch
  | .add src dst scratch => addLength src dst scratch
  | .multiply src factor dst counter scratch => multiply src factor dst counter scratch
  | .prependNat number output scratch => prependNat number output scratch
  | .prependLiteral number output scratch sign => prependLiteral number output scratch sign
  | .seq first second => StackProgram.seq (compile first) (compile second)
  | .ifThenElse test yes no => select (compile test) (compile yes) (compile no)
  | .branch j empty zero one => StackProgram.peekCase j (compile empty) (compile zero) (compile one)
  | .repeat j body => StackProgram.whileCounter j (compile body)

/-- The executable finite-control stack machine for this syntax. -/
def machine {k : Nat} (command : Command k) : StackMachine.Machine :=
  StackProgram.compile (compile command) (encoding command)

inductive Exec {k : Nat} : Command k → Registers k → Nat → (Bool × Registers k) → Prop where
  | stop (b : Bool) (r : Registers k) : Exec (.stop b) r 1 (b, r)
  | push (j : Fin (k + 1)) (b : Bool) (r : Registers k) :
      Exec (.push j b) r 2 (true, set r j (b :: r j))
  | pop (j : Fin (k + 1)) (r : Registers k) :
      Exec (.pop j) r 2 (true, set r j (r j).tail)
  | clear (j : Fin (k + 1)) (r : Registers k) :
      Exec (.clear j) r ((r j).length + 2) (true, set r j [])
  | copy {src dst scratch : Fin (k + 1)} {r : Registers k}
      (hsd : src ≠ dst) (hst : src ≠ scratch) (hdt : dst ≠ scratch) (hs : r scratch = []) :
      Exec (.copy src dst scratch) r ((r dst).length + 5 * (r src).length + 6)
        (true, set r dst (r src))
  | length {src dst scratch : Fin (k + 1)} {r : Registers k}
      (hsd : src ≠ dst) (hst : src ≠ scratch) (hdt : dst ≠ scratch) (hs : r scratch = []) :
      Exec (.length src dst scratch) r ((r dst).length + 5 * (r src).length + 6)
        (true, set r dst (List.replicate (r src).length true))
  | add {src dst scratch : Fin (k + 1)} {r : Registers k}
      (hsd : src ≠ dst) (hst : src ≠ scratch) (hdt : dst ≠ scratch) (hs : r scratch = []) :
      Exec (.add src dst scratch) r (5 * (r src).length + 4)
        (true, set r dst (List.replicate (r src).length true ++ r dst))
  | multiply {src factor dst counter scratch : Fin (k + 1)} {r : Registers k} {m : Nat}
      (hsd : src ≠ dst) (hst : src ≠ scratch) (hdt : dst ≠ scratch)
      (hcs : counter ≠ src) (hcd : counter ≠ dst) (hct : counter ≠ scratch)
      (hfc : factor ≠ counter) (hft : factor ≠ scratch) (hfd : factor ≠ dst)
      (hs : r scratch = []) (hm : r factor = List.replicate m true) :
      Exec (.multiply src factor dst counter scratch) r
        ((r dst).length + (r counter).length + 5 * m + m * (5 * (r src).length + 5) + 10)
        (true, set (set r counter []) dst (List.replicate (m * (r src).length) true))
  | prependNat {number output scratch : Fin (k + 1)} {r : Registers k}
      (hno : number ≠ output) (hns : number ≠ scratch) (hos : output ≠ scratch)
      (hs : r scratch = []) :
      Exec (.prependNat number output scratch) r (5 * (r number).length + 6)
        (true, set r output (SAT.writeNat (r number).length ++ r output))
  | prependLiteral {number output scratch : Fin (k + 1)} {sign : Bool} {r : Registers k}
      (hno : number ≠ output) (hns : number ≠ scratch) (hos : output ≠ scratch)
      (hs : r scratch = []) :
      Exec (.prependLiteral number output scratch sign) r (5 * (r number).length + 8)
        (true, set r output (SAT.encodeLiteral ⟨(r number).length, sign⟩ ++ r output))
  | seq {first second : Command k} {r middle : Registers k} {t s : Nat} {result}
      (hfirst : Exec first r t (true, middle)) (hsecond : Exec second middle s result) :
      Exec (.seq first second) r (t + s) result
  | seqFailure {first second : Command k} {r out : Registers k} {t : Nat}
      (hfirst : Exec first r t (false, out)) :
      Exec (.seq first second) r t (false, out)
  | ifTrue {test yes no : Command k} {r middle : Registers k} {t s : Nat} {result}
      (htest : Exec test r t (true, middle)) (hyes : Exec yes middle s result) :
      Exec (.ifThenElse test yes no) r (t + s) result
  | ifFalse {test yes no : Command k} {r middle : Registers k} {t s : Nat} {result}
      (htest : Exec test r t (false, middle)) (hno : Exec no middle s result) :
      Exec (.ifThenElse test yes no) r (t + s) result
  | branchEmpty {j : Fin (k + 1)} {empty zero one : Command k} {r : Registers k} {t : Nat} {result}
      (hr : r j = []) (h : Exec empty r t result) :
      Exec (.branch j empty zero one) r (t + 1) result
  | branchZero {j : Fin (k + 1)} {empty zero one : Command k} {r : Registers k} {tail}
      {t : Nat} {result} (hr : r j = false :: tail) (h : Exec zero r t result) :
      Exec (.branch j empty zero one) r (t + 1) result
  | branchOne {j : Fin (k + 1)} {empty zero one : Command k} {r : Registers k} {tail}
      {t : Nat} {result} (hr : r j = true :: tail) (h : Exec one r t result) :
      Exec (.branch j empty zero one) r (t + 1) result
  | repeatDone {j : Fin (k + 1)} {body : Command k} {r : Registers k} (hr : r j = []) :
      Exec (.repeat j body) r 2 (true, r)
  | repeatNext {j : Fin (k + 1)} {body : Command k} {r middle : Registers k} {b tail t s result}
      (hr : r j = b :: tail) (hb : Exec body (set r j tail) t (true, middle))
      (hrest : Exec (.repeat j body) middle s result) :
      Exec (.repeat j body) r (t + s + 1) result
  | repeatFailure {j : Fin (k + 1)} {body : Command k} {r out : Registers k} {b tail t}
      (hr : r j = b :: tail) (hb : Exec body (set r j tail) t (false, out)) :
      Exec (.repeat j body) r (t + 1) (false, out)

/-- Every counted high-level execution expands into the same number of actual
elementary stack instructions. There is no uninterpreted operation or cost. -/
theorem Exec.compile {k : Nat} {command : Command k} {r : Registers k} {time result}
    (h : Exec command r time result) :
    StackProgram.Exec (compile command) (compile command).start r time result := by
  induction h with
  | stop b r => exact StackProgram.exec_stop k b r
  | push j b r => exact StackProgram.exec_push j b r
  | pop j r => exact StackProgram.exec_pop j r
  | clear j r => exact StackWords.exec_clear j r
  | copy hsd hst hdt hs => exact StackWords.exec_copy _ _ _ hsd hst hdt _ hs
  | length hsd hst hdt hs => exact StackWords.exec_length _ _ _ hsd hst hdt _ hs
  | add hsd hst hdt hs => exact exec_addLength _ _ _ hsd hst hdt _ hs
  | multiply hsd hst hdt hcs hcd hct hfc hft hfd hs hm =>
      exact exec_multiply _ _ _ _ _ hsd hst hdt hcs hcd hct hfc hft hfd _ hs _ hm
  | prependNat hno hns hos hs => exact exec_prependNat _ _ _ hno hns hos _ hs
  | prependLiteral hno hns hos hs => exact exec_prependLiteral _ _ _ hno hns hos _ _ hs
  | seq _ _ ihfirst ihsecond => exact StackProgram.exec_seq _ _ ihfirst ihsecond
  | seqFailure _ ihfirst => exact StackProgram.exec_seq_failure _ _ ihfirst
  | ifTrue _ _ ihtest ihyes => exact exec_select_yes _ _ _ ihtest ihyes
  | ifFalse _ _ ihtest ihno => exact exec_select_no _ _ _ ihtest ihno
  | branchEmpty hr _ ih => exact StackProgram.exec_peekCase_empty _ _ _ _ hr ih
  | branchZero hr _ ih => exact StackProgram.exec_peekCase_zero _ _ _ _ hr ih
  | branchOne hr _ ih => exact StackProgram.exec_peekCase_one _ _ _ _ hr ih
  | repeatDone hr => exact StackProgram.exec_whileCounter_done _ _ _ hr
  | repeatNext hr _ _ ihbody ihrest => exact StackProgram.exec_whileCounter_next _ _ hr ihbody ihrest
  | repeatFailure hr _ ihbody => exact StackProgram.exec_whileCounter_failure _ _ hr ihbody

theorem Exec.machine_run {k : Nat} {command : Command k} {r : Registers k} {time result}
    (h : Exec command r time result) :
    StackMachine.run (machine command) time ⟨(machine command).start, r⟩ = some result :=
  StackProgram.compile_exec (encoding command) h.compile

end Complexity.StackTableauProgram
