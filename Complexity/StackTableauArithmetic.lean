module

public import Complexity.StackWords
public import Complexity.SAT
import Lean.Elab.Tactic.Omega

/-!
Finite stack programs for the arithmetic and serialization operations needed by
the tableau generator. Costs count actual pop, push, jump, and halt instructions.
Counters contain unary strings of true bits. No arithmetic operation is treated
as a unit-cost instruction.
-/

@[expose] public section

namespace Complexity.StackTableauArithmetic

open StackMachine (Registers set)
open StackProgram StackWords

abbrev AddLabel := Sum (Fin 4) (Fin 6)

/-- Preserve the source while prepending one true bit per source bit. -/
def addLength {k : Nat} (src dst scratch : Fin (k + 1)) : Program k AddLabel :=
  seq (transfer src scratch) (scatter scratch src dst true true)

def addEncoding : Encoding AddLabel := (Encoding.fin 3).sum (Encoding.fin 5)

theorem exec_addLength {k : Nat} (src dst scratch : Fin (k + 1))
    (hsd : src ≠ dst) (hst : src ≠ scratch) (hdt : dst ≠ scratch)
    (r : Registers k) (hempty : r scratch = []) :
    Exec (addLength src dst scratch) (.inl 0) r (5 * (r src).length + 4)
      (true, set r dst (List.replicate (r src).length true ++ r dst)) := by
  let r₁ := set (set r src []) scratch ((r src).reverse ++ r scratch)
  let r₂ := set (set (set r₁ scratch []) src ((r₁ scratch).reverse ++ r₁ src)) dst
    ((r₁ scratch).reverse.map (mapBit true true) ++ r₁ dst)
  have ht : Exec (transfer src scratch) 0 r (2 * (r src).length + 2) (true, r₁) :=
    exec_transfer src scratch hst r
  have hs : Exec (scatter scratch src dst true true) 0 r₁
      (3 * (r₁ scratch).length + 2) (true, r₂) :=
    exec_scatter scratch src dst (Ne.symm hst) (Ne.symm hdt) hsd true true r₁
  have he := exec_seq (transfer src scratch) (scatter scratch src dst true true) ht hs
  have hout : r₂ = set r dst (List.replicate (r src).length true ++ r dst) := by
    funext a
    by_cases hd : a = dst
    · subst a
      simp [r₂, r₁, Ne.symm hsd, hst, hdt, hempty, map_ones]
    · by_cases hsrc : a = src
      · subst a
        simp [r₂, r₁, hd, hst, hempty]
      · by_cases hsc : a = scratch
        · subst a
          simp [r₂, hd, hsrc, hempty]
        · simp [r₂, r₁, StackMachine.set, hd, hsrc, hsc]
  have htime : 2 * (r src).length + 2 + (3 * (r₁ scratch).length + 2) =
      5 * (r src).length + 4 := by
    simp [r₁, hempty]
    omega
  rw [hout, htime] at he
  exact he

theorem exec_add {k : Nat} (src dst scratch : Fin (k + 1))
    (hsd : src ≠ dst) (hst : src ≠ scratch) (hdt : dst ≠ scratch)
    (r : Registers k) (hempty : r scratch = []) (n m : Nat)
    (hsrc : r src = List.replicate n true) (hdst : r dst = List.replicate m true) :
    Exec (addLength src dst scratch) (.inl 0) r (5 * n + 4)
      (true, set r dst (List.replicate (n + m) true)) := by
  simpa [hsrc, hdst] using
    exec_addLength src dst scratch hsd hst hdt r hempty

abbrev RepeatAddLabel := Sum Bool AddLabel

def repeatAdd {k : Nat} (src dst counter scratch : Fin (k + 1)) :
    Program k RepeatAddLabel := whileCounter counter (addLength src dst scratch)

def repeatAddEncoding : Encoding RepeatAddLabel := Encoding.bool.sum addEncoding

/-- Destructively consume the repetition counter, preserving the multiplicand
and scratch, and add their product to the destination. -/
theorem exec_repeatAdd {k : Nat} (src dst counter scratch : Fin (k + 1))
    (hsd : src ≠ dst) (hst : src ≠ scratch) (hdt : dst ≠ scratch)
    (hcs : counter ≠ src) (hcd : counter ≠ dst) (hct : counter ≠ scratch)
    (m : Nat) (r : Registers k) (hcounter : r counter = List.replicate m true)
    (hempty : r scratch = []) :
    Exec (repeatAdd src dst counter scratch) (.inl false) r
      (m * (5 * (r src).length + 5) + 2)
      (true, set (set r counter []) dst
        (List.replicate (m * (r src).length) true ++ r dst)) := by
  induction m generalizing r with
  | zero =>
      have hout : set (set r counter []) dst (List.replicate (0 * (r src).length) true ++ r dst) = r := by
        have hc : set r counter [] = r := by
          have hz : r counter = [] := by simpa using hcounter
          rw [← hz]
          exact set_unchanged r counter
        simp [hc]
      rw [hout]
      simpa [repeatAdd] using
        exec_whileCounter_done counter (addLength src dst scratch) r (by simpa using hcounter)
  | succ m ih =>
      let r₁ := set r counter (List.replicate m true)
      let r₂ := set r₁ dst (List.replicate (r₁ src).length true ++ r₁ dst)
      have hr₁ : r₁ scratch = [] := by simp [r₁, Ne.symm hct, hempty]
      have hb := exec_addLength src dst scratch hsd hst hdt r₁ hr₁
      have hc₂ : r₂ counter = List.replicate m true := by simp [r₂, r₁, hcd]
      have hs₂ : r₂ scratch = [] := by simp [r₂, r₁, Ne.symm hdt, Ne.symm hct, hempty]
      have hrest := ih r₂ hc₂ hs₂
      have hcons : r counter = true :: List.replicate m true := by
        simpa only [List.replicate_succ] using hcounter
      have he := exec_whileCounter_next counter (addLength src dst scratch) hcons hb hrest
      have hout : set (set r₂ counter []) dst
          (List.replicate (m * (r₂ src).length) true ++ r₂ dst) =
          set (set r counter []) dst
            (List.replicate ((m + 1) * (r src).length) true ++ r dst) := by
        funext a
        by_cases hd : a = dst
        · subst a
          simp [r₂, r₁, hsd, Ne.symm hcs, Ne.symm hcd, Nat.add_mul,
            ← List.append_assoc]
        · by_cases hc : a = counter
          · subst a
            simp [hd]
          · simp [r₂, r₁, StackMachine.set, hd, hc]
      have htime : 5 * (r₁ src).length + 4 + (m * (5 * (r₂ src).length + 5) + 2) + 1 =
          (m + 1) * (5 * (r src).length + 5) + 2 := by
        simp [r₂, r₁, hsd, Ne.symm hcs, Nat.add_mul]
        omega
      rw [hout, htime] at he
      exact he

abbrev MultiplyLabel := Sum Bool (Sum (Sum Bool (Sum (Fin 4) (Fin 6))) RepeatAddLabel)

/-- Copy the multiplier into a loop counter, then perform counted unary adds. -/
def multiply {k : Nat} (src factor dst counter scratch : Fin (k + 1)) :
    Program k MultiplyLabel :=
  seq (clear dst) (seq (copy factor counter scratch) (repeatAdd src dst counter scratch))

def multiplyEncoding : Encoding MultiplyLabel :=
  Encoding.bool.sum (copyMapEncoding.sum repeatAddEncoding)

theorem exec_multiply {k : Nat} (src factor dst counter scratch : Fin (k + 1))
    (hsd : src ≠ dst) (hst : src ≠ scratch) (hdt : dst ≠ scratch)
    (hcs : counter ≠ src) (hcd : counter ≠ dst) (hct : counter ≠ scratch)
    (hfc : factor ≠ counter) (hft : factor ≠ scratch) (hfd : factor ≠ dst)
    (r : Registers k) (hempty : r scratch = []) (m : Nat)
    (hfactor : r factor = List.replicate m true) :
    Exec (multiply src factor dst counter scratch) (.inl false) r
      ((r dst).length + (r counter).length + 5 * m +
        m * (5 * (r src).length + 5) + 10)
      (true, set (set r counter []) dst (List.replicate (m * (r src).length) true)) := by
  let r₀ := set r dst []
  let r₁ := set r₀ counter (r₀ factor)
  have hclear := exec_clear dst r
  have hs₀ : r₀ scratch = [] := by simp [r₀, Ne.symm hdt, hempty]
  have hcopy := exec_copy factor counter scratch hfc hft hct r₀ hs₀
  have hc₁ : r₁ counter = List.replicate m true := by simp [r₁, r₀, hfd, hfactor]
  have hs₁ : r₁ scratch = [] := by simp [r₁, r₀, Ne.symm hct, Ne.symm hdt, hempty]
  have hloop := exec_repeatAdd src dst counter scratch hsd hst hdt hcs hcd hct m r₁ hc₁ hs₁
  have he := exec_seq (clear dst)
    (seq (copy factor counter scratch) (repeatAdd src dst counter scratch)) hclear
    (exec_seq (copy factor counter scratch) (repeatAdd src dst counter scratch) hcopy hloop)
  have hout : set (set r₁ counter []) dst
      (List.replicate (m * (r₁ src).length) true ++ r₁ dst) =
      set (set r counter []) dst (List.replicate (m * (r src).length) true) := by
    funext a
    by_cases hd : a = dst
    · subst a
      simp [r₁, r₀, hsd, Ne.symm hcs, Ne.symm hcd]
    · by_cases hc : a = counter
      · subst a
        simp [hd]
      · simp [r₁, r₀, StackMachine.set, hd, hc]
  have htime : (r dst).length + 2 +
      ((r₀ counter).length + 5 * (r₀ factor).length + 6 +
        (m * (5 * (r₁ src).length + 5) + 2)) =
      (r dst).length + (r counter).length + 5 * m +
        m * (5 * (r src).length + 5) + 10 := by
    simp [r₁, r₀, hcd, hfd, hsd, Ne.symm hcs, hfactor]
    omega
  rw [hout, htime] at he
  exact he

/-- A coarse quadratic bound derived from the counted instruction execution. -/
theorem multiply_cost_le (sourceLength multiplier destinationLength counterLength bound : Nat)
    (hs : sourceLength ≤ bound) (hm : multiplier ≤ bound)
    (hd : destinationLength ≤ bound) (hc : counterLength ≤ bound) :
    destinationLength + counterLength + 5 * multiplier +
      multiplier * (5 * sourceLength + 5) + 10 ≤
      5 * bound * bound + 12 * bound + 10 := by
  have hmul := Nat.mul_le_mul hm (show 5 * sourceLength + 5 ≤ 5 * bound + 5 by omega)
  have heq : bound * (5 * bound + 5) = 5 * bound * bound + 5 * bound := by
    simp [Nat.mul_add, Nat.mul_comm]
  rw [heq] at hmul
  omega

theorem writeNat_eq_replicate (n : Nat) :
    SAT.writeNat n = List.replicate n true ++ [false] := by
  induction n with
  | zero => rfl
  | succ n ih => simp [SAT.writeNat, List.replicate_succ, ih]

abbrev PrependNatLabel := Sum Bool AddLabel

/-- Put a forward unary numeral in front of the current output. -/
def prependNat {k : Nat} (number output scratch : Fin (k + 1)) : Program k PrependNatLabel :=
  seq (push output false) (addLength number output scratch)

def prependNatEncoding : Encoding PrependNatLabel := Encoding.bool.sum addEncoding

theorem exec_prependNat {k : Nat} (number output scratch : Fin (k + 1))
    (hno : number ≠ output) (hns : number ≠ scratch) (hos : output ≠ scratch)
    (r : Registers k) (hempty : r scratch = []) :
    Exec (prependNat number output scratch) (.inl false) r (5 * (r number).length + 6)
      (true, set r output (SAT.writeNat (r number).length ++ r output)) := by
  let r₁ := set r output (false :: r output)
  have hs₁ : r₁ scratch = [] := by simp [r₁, Ne.symm hos, hempty]
  have he := exec_seq (push output false) (addLength number output scratch)
    (exec_push output false r) (exec_addLength number output scratch hno hns hos r₁ hs₁)
  have htime : 2 + (5 * (r₁ number).length + 4) = 5 * (r number).length + 6 := by
    simp [r₁, hno]
    omega
  rw [htime] at he
  simpa [prependNat, r₁, hno, set_overwrite, writeNat_eq_replicate, List.append_assoc] using he

abbrev PrependLiteralLabel := Sum PrependNatLabel Bool

/-- Serialize a literal using its fixed sign and the length of a unary counter. -/
def prependLiteral {k : Nat} (number output scratch : Fin (k + 1)) (sign : Bool) :
    Program k PrependLiteralLabel :=
  seq (prependNat number output scratch) (push output sign)

def prependLiteralEncoding : Encoding PrependLiteralLabel := prependNatEncoding.sum Encoding.bool

theorem exec_prependLiteral {k : Nat} (number output scratch : Fin (k + 1))
    (hno : number ≠ output) (hns : number ≠ scratch) (hos : output ≠ scratch)
    (sign : Bool) (r : Registers k) (hempty : r scratch = []) :
    Exec (prependLiteral number output scratch sign) (.inl (.inl false)) r
      (5 * (r number).length + 8)
      (true, set r output (SAT.encodeLiteral ⟨(r number).length, sign⟩ ++ r output)) := by
  have he := exec_seq (prependNat number output scratch) (push output sign)
    (exec_prependNat number output scratch hno hns hos r hempty)
    (exec_push output sign (set r output (SAT.writeNat (r number).length ++ r output)))
  simpa [prependLiteral, SAT.encodeLiteral, set_overwrite, Nat.add_assoc] using he

end Complexity.StackTableauArithmetic
