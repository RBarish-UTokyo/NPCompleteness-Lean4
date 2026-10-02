module

public import Complexity.Binary.Basic
public import Complexity.Binary.StackTools
import Lean.Elab.Tactic.Omega

/-!
# Unary to binary conversion on stacks

`incProg D C` increments the binary numeral in register `D` (least significant digit on
top), using `C` as a unary carry counter. A counted loop of increments converts a unary
counter into binary: `whileCounter V (incProg D C)` turns `V = 1^v` and `D = []` into
`D = binOf v`, in `O(v^2)` instructions.
-/

@[expose] public section

namespace Complexity.Binary

open Complexity.StackMachine (Registers set branch)
open Complexity.StackProgram Complexity.StackWords

/-- Increment the binary numeral of `D`, least significant digit on top. Leading ones are
counted in `C`, then the first zero (or the empty end) becomes a one, then the counted ones
come back as zeros. -/
def incProg {k : Nat} (D C : Fin (k + 1)) : Program k (Fin 6) where
  start := 0
  code := fun q =>
    if q = 0 then .pop D 1 1 2
    else if q = 1 then .push D true 3
    else if q = 2 then .push C true 0
    else if q = 3 then .pop C 4 5 5
    else if q = 4 then .halt true
    else .push D false 3

def incEncoding : Encoding (Fin 6) := Encoding.fin 5

theorem exec_inc_drain {k : Nat} (D C : Fin (k + 1)) (hDC : D ≠ C) (j : Nat) (r : Registers k)
    (hC : r C = List.replicate j true) :
    Exec (incProg D C) 3 r (2 * j + 2)
      (true, set (set r C []) D (List.replicate j false ++ r D)) := by
  induction j generalizing r with
  | zero =>
    have hset : set r C [] = r := by
      have hz : r C = [] := by simpa using hC
      rw [← hz, set_unchanged]
    simp only [List.replicate_zero, List.nil_append, Nat.mul_zero, Nat.zero_add, hset, set_unchanged]
    apply Exec.next (q' := 4) (r' := r)
    · simp [StackProgram.step, incProg, hC, branch, hset]
    · exact .halt (by simp [StackProgram.step, incProg])
  | succ j ih =>
    let r₁ := set r C (List.replicate j true)
    let r₂ := set r₁ D (false :: r₁ D)
    have h₁ : StackProgram.step (incProg D C) 3 r = .inr (5, r₁) := by
      simp [StackProgram.step, incProg, hC, branch, List.replicate_succ, r₁]
    have h₂ : StackProgram.step (incProg D C) 5 r₁ = .inr (3, r₂) := by
      simp [StackProgram.step, incProg, r₂]
    have hC₂ : r₂ C = List.replicate j true := by simp [r₂, r₁, Ne.symm hDC]
    have hh := Exec.next h₁ (Exec.next h₂ (ih r₂ hC₂))
    have hout : set (set r₂ C []) D (List.replicate j false ++ r₂ D) =
        set (set r C []) D (List.replicate (j + 1) false ++ r D) := by
      funext a
      by_cases hd : a = D
      · subst a
        simp [r₂, r₁, hDC, List.replicate_succ']
      · by_cases hc : a = C
        · subst a; simp [hd]
        · simp [r₂, r₁, StackMachine.set, hd, hc]
    rw [hout] at hh
    have hcost : 2 * j + 2 + 1 + 1 = 2 * (j + 1) + 2 := by omega
    rw [hcost] at hh
    exact hh

theorem exec_inc_carry {k : Nat} (D C : Fin (k + 1)) (hDC : D ≠ C) (n m : Nat)
    (tail : List Bool) (ht : tail.head? ≠ some true) (r : Registers k)
    (hD : r D = List.replicate n true ++ tail) (hC : r C = List.replicate m true) :
    Exec (incProg D C) 0 r (4 * n + 2 * m + 4)
      (true, set (set r C []) D (List.replicate (n + m) false ++ true :: tail.tail)) := by
  induction n generalizing r m with
  | zero =>
    let r₁ := set r D tail.tail
    let r₂ := set r₁ D (true :: tail.tail)
    have h₁ : StackProgram.step (incProg D C) 0 r = .inr (1, r₁) := by
      cases tail with
      | nil => simp [StackProgram.step, incProg, hD, branch, r₁]
      | cons b rest =>
        cases b with
        | false => simp [StackProgram.step, incProg, hD, branch, r₁]
        | true => simp at ht
    have h₂ : StackProgram.step (incProg D C) 1 r₁ = .inr (3, r₂) := by
      simp [StackProgram.step, incProg, r₂, r₁]
    have hC₂ : r₂ C = List.replicate m true := by simp [r₂, r₁, Ne.symm hDC, hC]
    have hh := Exec.next h₁ (Exec.next h₂ (exec_inc_drain D C hDC m r₂ hC₂))
    have hout : set (set r₂ C []) D (List.replicate m false ++ r₂ D) =
        set (set r C []) D (List.replicate (0 + m) false ++ true :: tail.tail) := by
      funext a
      by_cases hd : a = D
      · subst a; simp [r₂]
      · by_cases hc : a = C
        · subst a; simp [hd]
        · simp [r₂, r₁, StackMachine.set, hd, hc]
    rw [hout] at hh
    have hcost : 2 * m + 2 + 1 + 1 = 4 * 0 + 2 * m + 4 := by omega
    rw [hcost] at hh
    exact hh
  | succ n ih =>
    let r₁ := set r D (List.replicate n true ++ tail)
    let r₂ := set r₁ C (true :: r₁ C)
    have h₁ : StackProgram.step (incProg D C) 0 r = .inr (2, r₁) := by
      simp [StackProgram.step, incProg, hD, branch, List.replicate_succ, r₁]
    have h₂ : StackProgram.step (incProg D C) 2 r₁ = .inr (0, r₂) := by
      simp [StackProgram.step, incProg, r₂]
    have hD₂ : r₂ D = List.replicate n true ++ tail := by simp [r₂, r₁, hDC]
    have hC₂ : r₂ C = List.replicate (m + 1) true := by
      simp [r₂, r₁, Ne.symm hDC, hC, List.replicate_succ]
    have hh := Exec.next h₁ (Exec.next h₂ (ih (m + 1) r₂ hD₂ hC₂))
    have hout : set (set r₂ C []) D (List.replicate (n + (m + 1)) false ++ true :: tail.tail) =
        set (set r C []) D (List.replicate (n + 1 + m) false ++ true :: tail.tail) := by
      funext a
      by_cases hd : a = D
      · subst a; simp [Nat.add_comm, Nat.add_left_comm]
      · by_cases hc : a = C
        · subst a; simp [hd]
        · simp [r₂, r₁, StackMachine.set, hd, hc]
    rw [hout] at hh
    have hcost : 4 * n + 2 * (m + 1) + 4 + 1 + 1 = 4 * (n + 1) + 2 * m + 4 := by omega
    rw [hcost] at hh
    exact hh

theorem split_leading_ones (bs : List Bool) :
    ∃ n tail, bs = List.replicate n true ++ tail ∧ tail.head? ≠ some true := by
  induction bs with
  | nil => exact ⟨0, [], rfl, by simp⟩
  | cons b bs ih =>
    cases b with
    | false => exact ⟨0, false :: bs, rfl, by simp⟩
    | true =>
      obtain ⟨n, tail, h, ht⟩ := ih
      exact ⟨n + 1, tail, by simp [h, List.replicate_succ], ht⟩

theorem inc_split (n : Nat) (tail : List Bool) (ht : tail.head? ≠ some true) :
    inc (List.replicate n true ++ tail) = List.replicate n false ++ true :: tail.tail := by
  cases tail with
  | nil => simpa using inc_replicate_nil n
  | cons b rest =>
    cases b with
    | false => simpa using inc_replicate_false n rest
    | true => simp at ht

/-- One increment, with a carry register that starts and ends empty. -/
theorem exec_inc {k : Nat} (D C : Fin (k + 1)) (hDC : D ≠ C) (r : Registers k)
    (hC : r C = []) :
    ∃ t, t ≤ 4 * (r D).length + 4 ∧
      Exec (incProg D C) (incProg D C).start r t (true, set r D (inc (r D))) := by
  obtain ⟨n, tail, hD, ht⟩ := split_leading_ones (r D)
  have hh := exec_inc_carry D C hDC n 0 tail ht r hD (by simpa using hC)
  have hset : set r C [] = r := by rw [← hC, set_unchanged]
  rw [hset] at hh
  refine ⟨4 * n + 2 * 0 + 4, ?_, ?_⟩
  · rw [hD]; simp; omega
  · rw [hD, inc_split n tail ht]
    change Exec (incProg D C) 0 r _ _
    simpa using hh

/-- `n` further increments. -/
def incN : Nat → List Bool → List Bool
  | 0, bs => bs
  | n + 1, bs => incN n (inc bs)

theorem incN_binOf (n m : Nat) : incN n (binOf m) = binOf (n + m) := by
  induction n generalizing m with
  | zero => simp [incN]
  | succ n ih =>
    simp only [incN]
    have : inc (binOf m) = binOf (m + 1) := rfl
    rw [this, ih]
    congr 1
    omega

theorem incN_nil (n : Nat) : incN n [] = binOf n := by
  simpa only [binOf, Nat.add_zero] using incN_binOf n 0

theorem length_incN_le (n : Nat) (bs : List Bool) : (incN n bs).length ≤ bs.length + n := by
  induction n generalizing bs with
  | zero => simp [incN]
  | succ n ih =>
    simp only [incN]
    have h₁ := ih (inc bs)
    have h₂ := length_inc_le bs
    omega

/-- Counted increments: consume a unary counter, adding its value to a binary numeral. -/
def toBinaryProg {k : Nat} (V D C : Fin (k + 1)) := whileCounter V (incProg D C)

def toBinaryEncoding : Encoding (Sum Bool (Fin 6)) := Encoding.bool.sum incEncoding

theorem exec_toBinary {k : Nat} (V D C : Fin (k + 1)) (hVD : V ≠ D) (hVC : V ≠ C)
    (hDC : D ≠ C) (bound v : Nat) (r : Registers k) (hV : r V = List.replicate v true)
    (hC : r C = []) (hb : (r D).length + v ≤ bound) :
    ∃ t, t ≤ v * (4 * bound + 5) + 2 ∧
      Exec (toBinaryProg V D C) (.inl false) r t (true, set (set r V []) D (incN v (r D))) := by
  induction v generalizing r with
  | zero =>
    refine ⟨2, by simp, ?_⟩
    have hset : set r V [] = r := by
      have hz : r V = [] := by simpa using hV
      rw [← hz, set_unchanged]
    simpa [toBinaryProg, incN, hset] using
      exec_whileCounter_done V (incProg D C) r (by simpa using hV)
  | succ v ih =>
    let r₁ := set r V (List.replicate v true)
    have hC₁ : r₁ C = [] := by simp [r₁, Ne.symm hVC, hC]
    obtain ⟨t, ht, he⟩ := exec_inc D C hDC r₁ hC₁
    let r₂ := set r₁ D (inc (r₁ D))
    have hD₁ : r₁ D = r D := by simp [r₁, Ne.symm hVD]
    have hV₂ : r₂ V = List.replicate v true := by simp [r₂, r₁, hVD]
    have hC₂ : r₂ C = [] := by simp [r₂, Ne.symm hDC, hC₁]
    have hb₂ : (r₂ D).length + v ≤ bound := by
      simp only [r₂, StackMachine.set_same, hD₁]
      have := length_inc_le (r D)
      omega
    obtain ⟨s, hs, he'⟩ := ih r₂ hV₂ hC₂ hb₂
    have hh := exec_whileCounter_next V (incProg D C)
      (by simpa [List.replicate_succ] using hV) he he'
    have hout : set (set r₂ V []) D (incN v (r₂ D)) =
        set (set r V []) D (incN (v + 1) (r D)) := by
      funext a
      by_cases hd : a = D
      · subst a; simp [r₂, hD₁, incN]
      · by_cases hv : a = V
        · subst a; simp [hd]
        · simp [r₂, r₁, StackMachine.set, hd, hv]
    rw [hout] at hh
    refine ⟨t + s + 1, ?_, hh⟩
    have hD : (r D).length ≤ bound := by omega
    rw [hD₁] at ht
    rw [Nat.succ_mul]
    omega

/-- Conversion of a unary counter into a fresh binary numeral. -/
theorem exec_toBinary_nil {k : Nat} (V D C : Fin (k + 1)) (hVD : V ≠ D) (hVC : V ≠ C)
    (hDC : D ≠ C) (v : Nat) (r : Registers k) (hV : r V = List.replicate v true)
    (hC : r C = []) (hD : r D = []) :
    ∃ t, t ≤ v * (4 * v + 5) + 2 ∧
      Exec (toBinaryProg V D C) (.inl false) r t (true, set (set r V []) D (binOf v)) := by
  obtain ⟨t, ht, he⟩ := exec_toBinary V D C hVD hVC hDC v v r hV hC (by simp [hD])
  rw [hD, incN_nil] at he
  exact ⟨t, ht, he⟩

end Complexity.Binary
