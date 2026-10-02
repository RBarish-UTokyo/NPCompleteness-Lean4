module

public import Complexity.StackTableauEmitterCompile
public import Complexity.PolynomialBound
import Lean.Elab.Tactic.Omega

/-!
# A unary clock on Boolean stacks

A ten-register stack program that, on input `x`, leaves the unary numeral
`powerBound (2 * c) k |x|` in register 0 and `x` in register 1, all other registers
being empty. It is written in the command language of `StackTableauProgram`, whose
execution judgment counts every primitive stack instruction.
-/

@[expose] public section

namespace Complexity.NTM

open StackTableauProgram (Command Exec)
open StackMachine (Registers set)

/-- Multiply register 4 by register 2, `i` times (register 5 is the product, 6 the loop
counter and 3 the scratch register). -/
def powLoop : Nat → Command 9
  | 0 => .stop true
  | i + 1 => .seq (.seq (.multiply 4 2 5 6 3) (.copy 5 4 3)) (powLoop i)

/-- A bound on the cost of one multiplication round when all registers involved have
length at most `B`. -/
def iterCost (B : Nat) : Nat := 5 * (B * B) + 20 * B + 20

theorem exec_powLoop (n : Nat) : ∀ (i a : Nat) (r : Registers 9) (B : Nat),
    r 2 = List.replicate (n + 1) true → r 3 = [] → r 4 = List.replicate a true → r 6 = [] →
    (r 5).length ≤ B → a * (n + 1) ^ i + n + 1 ≤ B →
    ∃ time r', time ≤ i * iterCost B + 1 ∧ Exec (powLoop i) r time (true, r') ∧
      r' 4 = List.replicate (a * (n + 1) ^ i) true ∧ (r' 5).length ≤ B ∧
      ∀ j, j ≠ 4 → j ≠ 5 → r' j = r j
  | 0, a, r, B, _, _, h4, _, h5, _ =>
    ⟨1, r, by omega, Exec.stop true r, by simpa using h4, h5, fun _ _ _ => rfl⟩
  | i + 1, a, r, B, h2, h3, h4, h6, h5, hB => by
    have hmul := Exec.multiply (k := 9) (src := 4) (factor := 2) (dst := 5) (counter := 6)
      (scratch := 3) (r := r) (m := n + 1) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) h3 h2
    let r₁ := set (set r 6 []) 5 (List.replicate ((n + 1) * (r 4).length) true)
    have hcopy := Exec.copy (k := 9) (src := 5) (dst := 4) (scratch := 3) (r := r₁)
      (by decide) (by decide) (by decide) (by simp [r₁, h3])
    let r₂ := set r₁ 4 (r₁ 5)
    have hpow : (n + 1) * a * (n + 1) ^ i = a * (n + 1) ^ (i + 1) := by
      simp [Nat.pow_succ, Nat.mul_comm, Nat.mul_assoc]
    have hone : 1 ≤ (n + 1) ^ i := Nat.pos_of_ne_zero (by simp)
    have ha : a ≤ (n + 1) * a * (n + 1) ^ i := by
      have h1 : a ≤ (n + 1) * a := by
        have := Nat.mul_le_mul_right a (show 1 ≤ n + 1 by omega)
        simpa using this
      have h2 := Nat.mul_le_mul h1 hone
      simpa using h2
    have hna : (n + 1) * a ≤ (n + 1) * a * (n + 1) ^ i := by
      simpa using Nat.mul_le_mul (Nat.le_refl ((n + 1) * a)) hone
    have hlen4 : (r 4).length = a := by simp [h4]
    obtain ⟨time, r', ht, he, h4', h5', hframe⟩ := exec_powLoop n i ((n + 1) * a) r₂ B
      (by simp [r₂, r₁, h2]) (by simp [r₂, r₁, h3]) (by simp [r₂, r₁, hlen4])
      (by simp [r₂, r₁]) (by simp [r₂, r₁, hlen4]; omega) (by omega)
    refine ⟨_, r', ?_, Exec.seq (Exec.seq hmul hcopy) he, ?_, h5', ?_⟩
    · have hm : (n + 1) * (5 * (r 4).length + 5) ≤ B * (5 * B + 5) := by
        rw [hlen4]
        exact Nat.mul_le_mul (by omega) (by omega)
      have hBB : B * (5 * B + 5) = 5 * (B * B) + 5 * B := by
        rw [Nat.mul_add, Nat.mul_comm B (5 * B), Nat.mul_assoc]
        omega
      have hc : (r₁ 4).length + 5 * (r₁ 5).length + 6 ≤ 6 * B + 6 := by
        simp [r₁, hlen4]
        omega
      have hi : i * iterCost B + iterCost B = (i + 1) * iterCost B := by
        rw [Nat.add_mul, Nat.one_mul]
      have hic : iterCost B = 5 * (B * B) + 20 * B + 20 := rfl
      simp only [h6, List.length_nil] at hm hc ⊢
      omega
    · rw [h4', hpow]
    · intro j hj4 hj5
      rw [hframe j hj4 hj5]
      by_cases hj6 : j = 6
      · subst j; simp [r₂, r₁, h6]
      · simp [r₂, r₁, StackMachine.set, hj4, hj5, hj6]

/-- The clock program. -/
def clockCommand (c k : Nat) : Command 9 :=
  .seq (.length 0 2 3) (.seq (.push 2 true) (.seq (StackTableauEmitterCompile.pushTrue 4 (2 * c))
    (.seq (powLoop k) (.seq (.copy 0 1 3) (.seq (.copy 4 0 3)
      (.seq (.clear 2) (.seq (.clear 4) (.clear 5))))))))

def clockMachine (c k : Nat) : StackMachine.Machine :=
  StackTableauProgram.machine (clockCommand c k)

/-- The length of the clock. -/
def clockLength (c k n : Nat) : Nat := powerBound (2 * c) k n

def clockBound (c k n : Nat) : Nat := clockLength c k n + n + 1

def clockTime (c k n : Nat) : Nat :=
  k * iterCost (clockBound c k n) + 20 * clockBound c k n + 4 * c + 40

/-- The final registers of the clock. -/
def ClockResult (c k : Nat) (x : List Bool) (R : Registers 9) : Prop :=
  R 0 = List.replicate (clockLength c k x.length) true ∧ R 1 = x ∧
    ∀ j : Fin 10, 2 ≤ j.val → R j = []

theorem exec_clock (c k : Nat) (x : List Bool) :
    ∃ time R, time ≤ clockTime c k x.length ∧
      Exec (clockCommand c k) (fun j => if j = 0 then x else []) time (true, R) ∧
      ClockResult c k x R := by
  let r₀ : Registers 9 := fun j => if j = 0 then x else []
  have hlength := Exec.length (k := 9) (src := 0) (dst := 2) (scratch := 3) (r := r₀)
    (by decide) (by decide) (by decide) (by simp [r₀])
  let r₁ := set r₀ 2 (List.replicate (r₀ 0).length true)
  have hpush := Exec.push (k := 9) 2 true r₁
  let r₂ := set r₁ 2 (true :: r₁ 2)
  have hconst := StackTableauEmitterCompile.exec_pushTrue (k := 9) 4 (2 * c) r₂
  let r₃ := set r₂ 4 (List.replicate (2 * c) true ++ r₂ 4)
  have h0 : r₀ 0 = x := by simp [r₀]
  have hr₃2 : r₃ 2 = List.replicate (x.length + 1) true := by
    simp [r₃, r₂, r₁, h0, List.replicate_succ]
  have hr₃4 : r₃ 4 = List.replicate (2 * c) true := by simp [r₃, r₂, r₁, r₀]
  have hpowEq : 2 * c * (x.length + 1) ^ k = clockLength c k x.length := by
    simp [clockLength, powerBound_eq]
  obtain ⟨tpow, r₄, htpow, hpowExec, h44, h45, hframe⟩ :=
    exec_powLoop x.length k (2 * c) r₃ (clockBound c k x.length) hr₃2
      (by simp [r₃, r₂, r₁, r₀]) hr₃4 (by simp [r₃, r₂, r₁, r₀])
      (by simp [r₃, r₂, r₁, r₀])
      (by rw [hpowEq]; simp [clockBound])
  rw [hpowEq] at h44
  have hr₄ : ∀ j, j ≠ 4 → j ≠ 5 → r₄ j = r₃ j := hframe
  have hcopy1 := Exec.copy (k := 9) (src := 0) (dst := 1) (scratch := 3) (r := r₄)
    (by decide) (by decide) (by decide)
    (by rw [hr₄ 3 (by decide) (by decide)]; simp [r₃, r₂, r₁, r₀])
  let r₅ := set r₄ 1 (r₄ 0)
  have hcopy2 := Exec.copy (k := 9) (src := 4) (dst := 0) (scratch := 3) (r := r₅)
    (by decide) (by decide) (by decide)
    (by simp [r₅]; rw [hr₄ 3 (by decide) (by decide)]; simp [r₃, r₂, r₁, r₀])
  let r₆ := set r₅ 0 (r₅ 4)
  have hclear2 := Exec.clear (k := 9) 2 r₆
  let r₇ := set r₆ 2 []
  have hclear4 := Exec.clear (k := 9) 4 r₇
  let r₈ := set r₇ 4 []
  have hclear5 := Exec.clear (k := 9) 5 r₈
  let r₉ := set r₈ 5 []
  have hall := Exec.seq hlength (Exec.seq hpush (Exec.seq hconst (Exec.seq hpowExec
    (Exec.seq hcopy1 (Exec.seq hcopy2 (Exec.seq hclear2 (Exec.seq hclear4 hclear5)))))))
  have hr₄0 : r₄ 0 = x := by rw [hr₄ 0 (by decide) (by decide)]; simp [r₃, r₂, r₁, r₀]
  have hr₄1 : r₄ 1 = [] := by
    rw [hr₄ 1 (by decide) (by decide)]; simp [r₃, r₂, r₁, r₀]
  have hr₄2 : r₄ 2 = List.replicate (x.length + 1) true := by
    rw [hr₄ 2 (by decide) (by decide)]; exact hr₃2
  refine ⟨_, r₉, ?_, hall, ?_, ?_, ?_⟩
  · have hL : clockBound c k x.length = clockLength c k x.length + x.length + 1 := rfl
    have e1 : (r₀ 2).length = 0 := by simp [r₀]
    have e2 : (r₀ 0).length = x.length := by simp [h0]
    have e3 : (r₄ 1).length = 0 := by simp [hr₄1]
    have e4 : (r₄ 0).length = x.length := by simp [hr₄0]
    have e5 : (r₅ 0).length = x.length := by simp [r₅, hr₄0]
    have e6 : (r₅ 4).length = clockLength c k x.length := by simp [r₅, h44]
    have e7 : (r₆ 2).length = x.length + 1 := by simp [r₆, r₅, hr₄2]
    have e8 : (r₇ 4).length = clockLength c k x.length := by simp [r₇, r₆, r₅, h44]
    have e9 : (r₈ 5).length = (r₄ 5).length := by simp [r₈, r₇, r₆, r₅]
    rw [e1, e2, e3, e4, e5, e6, e7, e8, e9]
    unfold clockTime
    omega
  · simp [r₉, r₈, r₇, r₆, r₅, h44]
  · simp [r₉, r₈, r₇, r₆, r₅, hr₄0]
  · intro j hj
    by_cases h2 : j = 2
    · subst j; simp [r₉, r₈, r₇]
    by_cases h4 : j = 4
    · subst j; simp [r₉, r₈]
    by_cases h5 : j = 5
    · subst j; simp [r₉]
    have hj0 : j ≠ 0 := fun h => by subst h; simp at hj
    have hj1 : j ≠ 1 := fun h => by subst h; simp at hj
    simp only [r₉, r₈, r₇, r₆, r₅, StackMachine.set, h2, h4, h5, hj0, hj1, ite_false]
    rw [hr₄ j h4 h5]
    simp [r₃, r₂, r₁, r₀, StackMachine.set, h2, h4, hj0]

theorem clock_runs (c k : Nat) (x : List Bool) :
    ∃ time, ∃ R : Registers 9, time ≤ clockTime c k x.length ∧
      StackMachine.runInput (clockMachine c k) time x = some (true, R) ∧
      ClockResult c k x R := by
  obtain ⟨time, R, ht, he, hR⟩ := exec_clock c k x
  exact ⟨time, R, ht, he.machine_run, hR⟩

theorem polynomialBound_clockLength (c k : Nat) : PolynomialBound (clockLength c k) :=
  PolynomialBound.power (2 * c) k

theorem polynomialBound_clockBound (c k : Nat) : PolynomialBound (clockBound c k) :=
  ((polynomialBound_clockLength c k).add PolynomialBound.identity).add
    (PolynomialBound.constant 1)

theorem polynomialBound_clockTime (c k : Nat) : PolynomialBound (clockTime c k) := by
  have hB := polynomialBound_clockBound c k
  have hiter : PolynomialBound (fun n => iterCost (clockBound c k n)) :=
    ((((PolynomialBound.constant 5).mul (hB.mul hB)).add
      ((PolynomialBound.constant 20).mul hB)).add (PolynomialBound.constant 20))
  exact ((((PolynomialBound.constant k).mul hiter).add
    ((PolynomialBound.constant 20).mul hB)).add (PolynomialBound.constant (4 * c))).add
      (PolynomialBound.constant 40)

end Complexity.NTM
