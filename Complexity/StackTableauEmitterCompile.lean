module

public import Complexity.StackTableauEmitter
public import Complexity.StackTableauProgram
import Lean.Elab.Tactic.Omega

/-!
A concrete finite-stack compiler for the clause-emitter language. Every numeric
operation expands into stack-cell operations; loop counters are unary stacks.
There is no instruction that evaluates an arbitrary Lean function. Registers
are allocated from a statically bounded suffix. The execution lemmas below
establish costs and effects of the compiler's elementary combinators.
-/

@[expose] public section

namespace Complexity.StackTableauEmitterCompile

open StackTableauEmitter
open StackTableauProgram (Command Exec)
open StackMachine (Registers)

/-- A total address constructor. Compiler allocations stay below `k + 1`, so
its remainder operation does not identify any allocated addresses. -/
def register (k index : Nat) : Fin (k + 1) := ⟨index % (k + 1), Nat.mod_lt _ (by omega)⟩

theorem register_val {k index : Nat} (h : index < k + 1) :
    (register k index).val = index := Nat.mod_eq_of_lt h

theorem register_ne {k a b : Nat} (ha : a < k + 1) (hb : b < k + 1) (hab : a ≠ b) :
    register k a ≠ register k b := by
  intro h
  have heq := congrArg Fin.val h
  simp only [register_val ha, register_val hb] at heq
  exact hab heq

/-- A fixed numeral is compiled into a finite sequence of pushes. -/
def pushTrue {k : Nat} (dst : Fin (k + 1)) : Nat → Command k
  | 0 => .stop true
  | n + 1 => .seq (.push dst true) (pushTrue dst n)

/-- Clear a register and write a fixed unary numeral. -/
def constant {k : Nat} (dst : Fin (k + 1)) (n : Nat) : Command k :=
  .seq (.clear dst) (pushTrue dst n)

/-- Pop one destination cell per counter cell, saturating at the empty word. -/
def subtractCounter {k : Nat} (counter dst : Fin (k + 1)) : Command k :=
  .repeat counter (.pop dst)

/-- Expression scratch-register demand, excluding its destination and the two
shared arithmetic work registers. -/
def numSpace {n : Nat} : NumExpr n → Nat
  | .var _ => 0
  | .const _ => 0
  | .add left right | .mul left right | .sub left right =>
      2 + max (numSpace left) (numSpace right)
  | .pred value => numSpace value

/-- Compile one expression; `dst` is outside the fresh suffix beginning at
`base`. Registers 3 and 4 are reserved scratch and arithmetic counter. -/
def compileNum {k n : Nat} (env : Fin n → Fin (k + 1))
    (dst : Fin (k + 1)) (base : Nat) : NumExpr n → Command k
  | .var index => .copy (env index) dst (register k 3)
  | .const value => constant dst value
  | .add left right =>
      .seq (compileNum env (register k base) (base + 2) left)
        (.seq (compileNum env (register k (base + 1)) (base + 2) right)
          (.seq (.copy (register k base) dst (register k 3))
            (.add (register k (base + 1)) dst (register k 3))))
  | .mul left right =>
      .seq (compileNum env (register k base) (base + 2) left)
        (.seq (compileNum env (register k (base + 1)) (base + 2) right)
          (.multiply (register k base) (register k (base + 1)) dst (register k 4) (register k 3)))
  | .sub left right =>
      .seq (compileNum env (register k base) (base + 2) left)
        (.seq (compileNum env (register k (base + 1)) (base + 2) right)
          (.seq (.copy (register k base) dst (register k 3))
            (.seq (.copy (register k (base + 1)) (register k 4) (register k 3))
              (subtractCounter (register k 4) dst))))
  | .pred value => .seq (compileNum env dst base value) (.pop dst)

/-- Workspace for a literal list; every literal reuses the same expression
workspace after its number has been serialized. -/
def literalSpace {n : Nat} : List (LiteralExpr n) → Nat
  | [] => 1
  | literal :: rest => max (1 + numSpace literal.index) (literalSpace rest)

/-- Emit the tail first, then prepend the head, preserving the source order. -/
def compileLiterals {k n : Nat} (env : Fin n → Fin (k + 1))
    (base : Nat) : List (LiteralExpr n) → Command k
  | [] => .stop true
  | literal :: rest =>
      .seq (compileLiterals env base rest)
        (.seq (compileNum env (register k base) (base + 1) literal.index)
          (.prependLiteral (register k base) (register k 0) (register k 3) literal.positive))

def programSpace {n : Nat} : ClauseProgram n → Nat
  | .clause literals => literalSpace literals
  | .seq first second => max (programSpace first) (programSpace second)
  | .forDown bound body => 2 + max (numSpace bound) (programSpace body)
  | .ifLe left right yes no =>
      2 + max (max (numSpace left) (numSpace right)) (max (programSpace yes) (programSpace no))
  | .ifInput index empty zero one =>
      2 + max (numSpace index) (max (programSpace empty) (max (programSpace zero) (programSpace one)))

/-- Compile clauses by prepending their bytes. Every emitted clause increments
the actual header counter in register 2. -/
def compileBody {k n : Nat} (env : Fin n → Fin (k + 1))
    (base : Nat) (program : ClauseProgram n) : Command k :=
  match program with
  | .clause literals =>
      .seq (compileLiterals env base literals)
        (.seq (constant (register k base) literals.length)
          (.seq (.prependNat (register k base) (register k 0) (register k 3))
            (.push (register k 2) true)))
  | .seq first second => .seq (compileBody env base second) (compileBody env base first)
  | .forDown bound body =>
      .seq (compileNum env (register k base) (base + 2) bound)
        (.seq (constant (register k (base + 1)) 0)
          (.repeat (register k base)
            (.seq (compileBody (Fin.cases (register k (base + 1)) env) (base + 2) body)
              (.push (register k (base + 1)) true))))
  | .ifLe left right yes no =>
      .seq (compileNum env (register k base) (base + 2) left)
        (.seq (compileNum env (register k (base + 1)) (base + 2) right)
          (.seq (subtractCounter (register k (base + 1)) (register k base))
            (.branch (register k base) (compileBody env (base + 2) yes)
              (compileBody env (base + 2) no) (compileBody env (base + 2) no))))
  | .ifInput index empty zero one =>
      .seq (compileNum env (register k base) (base + 2) index)
        (.seq (.copy (register k 1) (register k (base + 1)) (register k 3))
          (.seq (subtractCounter (register k base) (register k (base + 1)))
            (.branch (register k (base + 1)) (compileBody env (base + 2) empty)
              (compileBody env (base + 2) zero) (compileBody env (base + 2) one))))

/-- Closed input-indexed emitters receive input length as their sole numeric
parameter. Register zero starts with the input, as required by StackMachine. -/
def command (program : ClauseProgram 1) : Command (6 + programSpace program) :=
  let k := 6 + programSpace program
  .seq (.copy (register k 0) (register k 1) (register k 3))
    (.seq (.clear (register k 0))
      (.seq (.length (register k 1) (register k 5) (register k 3))
        (.seq (compileBody (fun _ => register k 5) 6 program)
          (.prependNat (register k 2) (register k 0) (register k 3)))))

/-- The resulting machine has a fixed finite number of states and stacks for
each fixed emitter syntax. Its instruction set is entirely elementary. -/
def machine (program : ClauseProgram 1) : StackMachine.Machine :=
  StackTableauProgram.machine (command program)

theorem exec_pushTrue {k : Nat} (dst : Fin (k + 1)) (n : Nat) (r : Registers k) :
    Exec (pushTrue dst n) r (2 * n + 1)
      (true, StackMachine.set r dst (List.replicate n true ++ r dst)) := by
  induction n generalizing r with
  | zero => simpa [pushTrue] using Exec.stop true r
  | succ n ih =>
      have h := Exec.seq (Exec.push dst true r) (ih (StackMachine.set r dst (true :: r dst)))
      simpa [pushTrue, List.replicate_succ', List.append_assoc,
        Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

theorem exec_constant {k : Nat} (dst : Fin (k + 1)) (n : Nat) (r : Registers k) :
    Exec (constant dst n) r ((r dst).length + 2 * n + 3)
      (true, StackMachine.set r dst (List.replicate n true)) := by
  have h := Exec.seq (Exec.clear dst r) (exec_pushTrue dst n (StackMachine.set r dst []))
  have ht : (r dst).length + 2 + (2 * n + 1) = (r dst).length + 2 * n + 3 := by omega
  rw [ht] at h
  simpa [constant] using h

theorem exec_subtractCounter {k : Nat} (counter dst : Fin (k + 1))
    (hcd : counter ≠ dst) (n : Nat) (r : Registers k)
    (hc : r counter = List.replicate n true) :
    Exec (subtractCounter counter dst) r (3 * n + 2)
      (true, StackMachine.set (StackMachine.set r counter []) dst ((r dst).drop n)) := by
  induction n generalizing r with
  | zero =>
      have hr : StackMachine.set (StackMachine.set r counter []) dst (r dst) = r := by
        have hc' : r counter = [] := hc
        rw [← hc', StackWords.set_unchanged, StackWords.set_unchanged]
      simpa [subtractCounter, hr] using Exec.repeatDone hc
  | succ n ih =>
      let popped := StackMachine.set r counter (List.replicate n true)
      let middle := StackMachine.set popped dst ((popped dst).tail)
      have hm : middle counter = List.replicate n true := by
        simp [middle, popped, hcd]
      have hi := ih middle hm
      have hp : Exec (.pop dst) popped 2 (true, middle) := Exec.pop dst popped
      have hout : StackMachine.set (StackMachine.set middle counter []) dst ((middle dst).drop n) =
          StackMachine.set (StackMachine.set r counter []) dst ((r dst).drop (n + 1)) := by
        funext a
        by_cases had : a = dst
        · subst a
          simp [middle, popped, Ne.symm hcd, List.drop_tail]
        · by_cases hac : a = counter
          · subst a; simp [had]
          · simp [StackMachine.set, middle, popped, had, hac]
      have hh := Exec.repeatNext (by simpa [List.replicate_succ] using hc) hp hi
      rw [hout] at hh
      have ht : 2 + (3 * n + 2) + 1 = 3 * (n + 1) + 2 := by omega
      rw [ht] at hh
      exact hh

/-- An expression changes only its destination, shared arithmetic counter,
and its statically allocated suffix. -/
def Frame {k : Nat} (base : Nat) (dst : Fin (k + 1))
    (before after : Registers k) : Prop :=
  ∀ j, j.val < base → j ≠ dst → j ≠ register k 4 → after j = before j

theorem Frame.refl {k : Nat} (base : Nat) (dst : Fin (k + 1)) (r : Registers k) :
    Frame base dst r r := by intro _ _ _ _; rfl

theorem Frame.trans {k base : Nat} {dst : Fin (k + 1)} {r s t : Registers k}
    (hrs : Frame base dst r s) (hst : Frame base dst s t) : Frame base dst r t := by
  intro j hj hd hc
  exact (hst j hj hd hc).trans (hrs j hj hd hc)

theorem Frame.weaken {k base base' : Nat} {dst dst' : Fin (k + 1)}
    {r s : Registers k} (h : Frame base' dst' r s) (hb : base ≤ base')
    (hd : dst' = dst ∨ base ≤ dst'.val) : Frame base dst r s := by
  intro j hj hjd hjc
  apply h j (by omega) _ hjc
  intro heq
  rcases hd with hd | hd
  · exact hjd (heq.trans hd)
  · subst j; omega

theorem Frame.set {k base : Nat} {dst target : Fin (k + 1)} (r : Registers k)
    (value : List Bool) (h : target = dst ∨ target = register k 4 ∨ base ≤ target.val) :
    Frame base dst r (StackMachine.set r target value) := by
  intro j hj hd hc
  apply StackMachine.set_other r _
  intro heq
  subst j
  rcases h with h | h | h
  · exact hd h
  · exact hc h
  · omega

theorem frame_scratch {k base : Nat} {dst : Fin (k + 1)} {r s : Registers k}
    (h : Frame base dst r s) (hb : 5 ≤ base) (hd : 5 ≤ dst.val)
    (hk : 5 ≤ k + 1) : s (register k 3) = r (register k 3) := by
  apply h
  · rw [register_val (by omega)]; omega
  · intro heq
    have hv := congrArg Fin.val heq
    rw [register_val (by omega)] at hv
    omega
  · exact register_ne (by omega) (by omega) (by omega)

end Complexity.StackTableauEmitterCompile
