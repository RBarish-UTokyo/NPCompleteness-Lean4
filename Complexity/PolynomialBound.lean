module

public import Complexity.Clock
import Lean.Elab.Tactic.Omega

/-!
Elementary closure laws for numerical polynomial upper bounds. These do not
assert that an arbitrary bounded function is polynomial-time computable.
-/

@[expose] public section

namespace Complexity

def PolynomialBound (f : Nat → Nat) : Prop :=
  ∃ c k, ∀ n, f n ≤ powerBound c k n

namespace PolynomialBound

theorem constant (c : Nat) : PolynomialBound (fun _ => c) :=
  ⟨c, 0, by intro n; simp [powerBound]⟩

theorem identity : PolynomialBound (fun n => n) :=
  ⟨1, 1, by intro n; simp [powerBound]⟩

theorem weaken {f g : Nat → Nat} (h : PolynomialBound g) (hle : ∀ n, f n ≤ g n) :
    PolynomialBound f := by
  obtain ⟨c, k, h⟩ := h
  exact ⟨c, k, fun n => Nat.le_trans (hle n) (h n)⟩

theorem add {f g : Nat → Nat} (hf : PolynomialBound f) (hg : PolynomialBound g) :
    PolynomialBound (fun n => f n + g n) := by
  obtain ⟨c, k, hf⟩ := hf
  obtain ⟨d, l, hg⟩ := hg
  refine ⟨c + d, k + l, ?_⟩
  intro n
  have hk : (n + 1) ^ k ≤ (n + 1) ^ (k + l) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have hl : (n + 1) ^ l ≤ (n + 1) ^ (k + l) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have hc := Nat.le_trans (hf n) (Nat.mul_le_mul_left c hk)
  have hd := Nat.le_trans (hg n) (Nat.mul_le_mul_left d hl)
  simpa only [powerBound, Nat.add_mul] using Nat.add_le_add hc hd

theorem mul {f g : Nat → Nat} (hf : PolynomialBound f) (hg : PolynomialBound g) :
    PolynomialBound (fun n => f n * g n) := by
  obtain ⟨c, k, hf⟩ := hf
  obtain ⟨d, l, hg⟩ := hg
  refine ⟨c * d, k + l, ?_⟩
  intro n
  have h := Nat.mul_le_mul (hf n) (hg n)
  simpa [powerBound, Nat.pow_add, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using h

theorem pow {f : Nat → Nat} (hf : PolynomialBound f) (k : Nat) :
    PolynomialBound (fun n => f n ^ k) := by
  induction k with
  | zero => simpa using constant 1
  | succ k ih => simpa only [Nat.pow_succ] using ih.mul hf

theorem power (c k : Nat) : PolynomialBound (powerBound c k) :=
  ⟨c, k, fun _ => Nat.le_refl _⟩

theorem comp {f g : Nat → Nat} (hf : PolynomialBound f) (hg : PolynomialBound g) :
    PolynomialBound (fun n => f (g n)) := by
  obtain ⟨c, k, hf⟩ := hf
  have h := (constant c).mul ((hg.add (constant 1)).pow k)
  exact h.weaken (fun n => hf (g n))

end PolynomialBound

end Complexity
