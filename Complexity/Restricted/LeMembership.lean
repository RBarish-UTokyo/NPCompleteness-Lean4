module

public import Complexity.Restricted.LeScan
public import Complexity.Restricted.CheckedVerifier

/-!
# (≤1,≤2)-SAT is in NP

`leCheck` extracts the literal occurrences of the input formula, checking that every clause
has two or three literals (`pass1`), and then checks the occurrence bounds (`pass2`). With the
3-SAT verifier this gives an NP verifier for (≤1,≤2)-SAT.
-/

@[expose] public section

namespace Complexity.Restricted

open StackTableauProgram (Command Exec)
open StackMachine (Registers set)
open Complexity.SAT

def pass2 : Command 23 := .seq (.push rG2 true) (.repeat rG2 outerBody)

def leCheck : Command 23 := .seq pass1 pass2

def leModel (x : Word) : Bool :=
  match pass1Model x with
  | none => false
  | some lits => outerModel lits

theorem leCheck_writes : ∀ j : Fin 24, j.val < 7 → writes leCheck j = false := by decide

theorem leCheck_spec (r : Regs) (hr : HighEmpty r) :
    ∃ t r', Exec leCheck r t (leModel (r rIn), r') ∧ t ≤ 160 * ((r rIn).length + 1) ^ 3 := by
  obtain ⟨t1, r₁, e1, ht1, h1⟩ := pass1_spec r hr
  have hcube : 1 ≤ ((r rIn).length + 1) ^ 3 := Nat.pow_pos (by omega)
  cases hp : pass1Model (r rIn) with
  | none =>
    rw [hp] at e1
    refine ⟨t1, r₁, ?_, by omega⟩
    have : leModel (r rIn) = false := by simp [leModel, hp]
    rw [this]
    exact Exec.seqFailure e1
  | some lits =>
    rw [hp] at e1
    obtain ⟨hL, ⟨hA, hG, hS, hT1, _⟩, hlen⟩ := h1 lits hp
    have fr1 : ∀ j : Fin 24, j ∉ [rW, rL, rA, rG, rR, rT1, rKC] → 7 ≤ j.val → r₁ j = [] := by
      intro j hj h7
      rw [exec_frame' e1 j (pass1_writes j hj)]
      exact hr j h7
    let r₂ := set r₁ rG2 [true]
    have e2 : Exec (.push rG2 true) r₁ 2 (true, r₂) := by
      have := Exec.push (k := 23) rG2 true r₁
      rwa [fr1 rG2 (by decide) (by decide)] at this
    obtain ⟨t3, r₃, e3, ht3⟩ := outerLoop_spec (r rIn).length lits r₂
      (by simp +decide [r₂, hL]) (by simp +decide [r₂]; exact hlen) (by simp [r₂])
      ⟨by simp +decide [r₂, hA],
        ⟨by simp +decide [r₂, fr1 rB (by decide) (by decide)],
          by simp +decide [r₂, hT1],
          by simp +decide [r₂, fr1 rT2 (by decide) (by decide)],
          by simp +decide [r₂, hS], by simp +decide [r₂, hG]⟩,
        by simp +decide [r₂, fr1 rF (by decide) (by decide)],
        by simp +decide [r₂, fr1 rL2 (by decide) (by decide)],
        by simp +decide [r₂, fr1 rG3 (by decide) (by decide)]⟩
    refine ⟨t1 + (2 + t3), r₃, ?_, ?_⟩
    · have : leModel (r rIn) = outerModel lits := by simp [leModel, hp]
      rw [this]
      exact Exec.seq e1 (Exec.seq e2 e3)
    · have hl2 := writeValues_length_le_two lits
      rw [← hL] at hl2
      have hm := Nat.mul_le_mul_right (80 * ((r rIn).length + 1) ^ 2)
        (show lits.length ≤ (r rIn).length + 1 by omega)
      have hc : ∀ q : Nat, q * (80 * q ^ 2) = 80 * q ^ 3 := by
        intro q
        rw [Nat.mul_left_comm, Nat.pow_succ q 2, Nat.mul_comm q]
      have := hc ((r rIn).length + 1)
      omega

/-! ### Semantics -/

theorem lit_beq (l : Literal) (a : Nat) (s : Bool) :
    (l == ⟨a, s⟩) = decide (s = l.positive ∧ a = l.var) := by
  rcases l with ⟨v, p⟩
  by_cases h1 : v = a <;> by_cases h2 : p = s
  · subst h1; subst h2; simp
  · have : (⟨v, p⟩ : Literal) ≠ ⟨a, s⟩ := by intro e; cases e; exact h2 rfl
    simp [this, Ne.symm h2]
  · have : (⟨v, p⟩ : Literal) ≠ ⟨a, s⟩ := by intro e; cases e; exact h1 rfl
    simp [this, Ne.symm h1]
  · have : (⟨v, p⟩ : Literal) ≠ ⟨a, s⟩ := by intro e; cases e; exact h1 rfl
    simp [this, Ne.symm h1]

theorem scanModel_true (a : Nat) : ∀ (ls : List Literal) (flag : Bool),
    scanModel true a flag ls = decide (ls.count ⟨a, true⟩ = 0)
  | [], _ => by simp [scanModel]
  | l :: ls, flag => by
    rw [scanModel, List.count_cons, lit_beq]
    by_cases h : true = l.positive ∧ a = l.var
    · rw [matchModel, ite_eq_left h]
      simp [h]
    · rw [matchModel, ite_eq_right h]
      simp only [h, decide_false, Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
      exact scanModel_true a ls flag

theorem scanModel_false (a : Nat) : ∀ (ls : List Literal) (flag : Bool),
    scanModel false a flag ls = decide (ls.count ⟨a, false⟩ + (if flag then 1 else 0) ≤ 1)
  | [], flag => by cases flag <;> simp [scanModel]
  | l :: ls, flag => by
    rw [scanModel, List.count_cons, lit_beq]
    by_cases h : false = l.positive ∧ a = l.var
    · rw [matchModel, ite_eq_left h]
      cases flag
      · simp only [Bool.false_eq_true, ↓reduceIte]
        rw [scanModel_false a ls true]
        simp [h]
      · simp [h]
    · rw [matchModel, ite_eq_right h]
      simp only [h, decide_false, Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
      exact scanModel_false a ls flag

/-- The occurrence cap of a literal: one if positive, two if negative. -/
def cap (l : Literal) : Nat := if l.positive then 1 else 2

theorem scanModel_self (l : Literal) (ls : List Literal) :
    scanModel l.positive l.var false ls = decide (ls.count l + 1 ≤ cap l) := by
  rcases l with ⟨v, p⟩
  cases p
  · rw [scanModel_false]
    simp only [cap, Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
    apply decide_eq_decide.mpr
    omega
  · rw [scanModel_true]
    simp only [cap, ↓reduceIte]
    apply decide_eq_decide.mpr
    omega

theorem outerModel_iff : ∀ lits : List Literal,
    outerModel lits = true ↔ ∀ x : Literal, lits.count x ≤ cap x
  | [] => by simp [outerModel]
  | l :: ls => by
    simp only [outerModel, Bool.and_eq_true, scanModel_self, decide_eq_true_eq, outerModel_iff ls]
    constructor
    · rintro ⟨h1, h2⟩ x
      rw [List.count_cons]
      by_cases hx : l = x
      · subst hx; simp; omega
      · have : (l == x) = false := by simp [hx]
        rw [this]
        simpa using h2 x
    · intro h
      refine ⟨?_, ?_⟩
      · have := h l
        rw [List.count_cons] at this
        simpa using this
      · intro x
        have := h x
        rw [List.count_cons] at this
        omega

theorem leModel_encode (f : CNF) : leModel (encode f) = true ↔ IsLeOneLeTwoCNF f := by
  unfold leModel
  rw [pass1Model_encode]
  by_cases hf : ∀ c ∈ f, c.length = 2 ∨ c.length = 3
  · rw [ite_eq_left hf]
    dsimp only
    rw [outerModel_iff]
    constructor
    · intro h
      refine ⟨fun c hc => by rcases hf c hc with h' | h' <;> omega, fun v => ?_⟩
      rw [filter_pos_count, filter_neg_count]
      have h1 := h ⟨v, true⟩
      have h2 := h ⟨v, false⟩
      simp only [List.count_reverse, cap] at h1 h2
      exact ⟨by simpa using h1, by simpa using h2⟩
    · rintro ⟨_, h⟩ x
      rcases x with ⟨v, p⟩
      have hv := h v
      rw [filter_pos_count, filter_neg_count] at hv
      rw [List.count_reverse]
      cases p
      · simpa [cap] using hv.2
      · simpa [cap] using hv.1
  · rw [ite_eq_right hf]
    simp only [Bool.false_eq_true, false_iff]
    intro h
    apply hf
    intro c hc
    have := h.1 c hc
    omega

/-! ### NP membership -/

theorem leCheck_checkSpec : CheckSpec leCheck leModel 160 where
  writes_low := leCheck_writes
  runs := leCheck_spec

theorem leOneLeTwoSAT_inNP : InNP SAT.LeOneLeTwoSAT := by
  apply inNP_of_check leCheck_checkSpec
  · rintro x hm ⟨f, rfl, _, hs⟩
    exact ⟨f, rfl, (leModel_encode f).mp hm, hs⟩
  · rintro x ⟨f, rfl, hle, hs⟩
    exact ⟨(leModel_encode f).mpr hle, f, rfl, fun c hc => (hle.1 c hc).2, hs⟩

end Complexity.Restricted
