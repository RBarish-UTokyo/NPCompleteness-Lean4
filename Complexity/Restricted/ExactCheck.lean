module

public import Complexity.Restricted.Commands
public import Complexity.SATVariants
import Lean.Elab.Tactic.Omega

/-!
# A stack program checking the exactly-3 shape of an encoded formula

`exactCheck` works on 24 registers. It reads the input word from register `0` (by one
copy) and writes only registers `7, …, 23`. On the code `encode f` of a formula it decides
whether every clause of `f` has exactly three literals on distinct variables; on every word
it halts within a quadratic number of instructions.
-/

@[expose] public section

namespace Complexity.Restricted

open StackTableauProgram (Command Exec)
open StackMachine (Registers set)
open Complexity.SAT

abbrev Regs := Registers 23

abbrev rIn : Fin 24 := 0
abbrev rW : Fin 24 := 7
abbrev rKC : Fin 24 := 8
abbrev rA : Fin 24 := 9
abbrev rB : Fin 24 := 10
abbrev rC : Fin 24 := 11
abbrev rT1 : Fin 24 := 12
abbrev rT2 : Fin 24 := 13
abbrev rS : Fin 24 := 14
abbrev rG : Fin 24 := 15

/-! ### Reading a literal -/

/-- Pop a literal code `s 1^v 0` from `w` and push `v` ones onto `x`. -/
def readLit (w x : Fin 24) : Command 23 :=
  .branch w (.stop false) (.seq (.pop w) (readUnaryC w x rG)) (.seq (.pop w) (readUnaryC w x rG))

def litModel : Word → Word → Bool × Word × Word
  | [], d => (false, [], d)
  | _ :: rest, d => unaryModel rest d

theorem litModel_encodeLiteral (l : Literal) (rest d : Word) :
    litModel (encodeLiteral l ++ rest) d = (true, rest, List.replicate l.var true ++ d) := by
  simp [encodeLiteral, litModel, unaryModel_writeNat]

theorem litModel_src_le (w d : Word) : (litModel w d).2.1.length ≤ w.length := by
  cases w with
  | nil => simp [litModel]
  | cons b rest =>
    have := unaryModel_src_le rest d
    simp only [litModel, List.length_cons]
    omega

theorem litModel_dst_le (w d : Word) : (litModel w d).2.2.length ≤ w.length + d.length := by
  cases w with
  | nil => simp [litModel]
  | cons b rest =>
    have := unaryModel_length rest d
    simp only [litModel, List.length_cons]
    omega

theorem readLit_spec (w x : Fin 24) (hwx : w ≠ x) (hwg : w ≠ rG) (hxg : x ≠ rG) (r : Regs)
    (hg : r rG = []) :
    ∃ t r', Exec (readLit w x) r t ((litModel (r w) (r x)).1, r') ∧ t ≤ 8 * (r w).length + 12 ∧
      r' w = (litModel (r w) (r x)).2.1 ∧ r' x = (litModel (r w) (r x)).2.2 ∧ r' rG = [] ∧
      ∀ j, j ≠ w → j ≠ x → j ≠ rG → r' j = r j := by
  cases hw : r w with
  | nil =>
    refine ⟨2, r, Exec.branchEmpty hw (Exec.stop _ _), by simp, by simp [litModel, hw],
      by simp [litModel], hg, fun _ _ _ _ => rfl⟩
  | cons b rest =>
    let r₁ := set r w rest
    have hp : Exec (.pop w) r 2 (true, r₁) := by
      have := Exec.pop (k := 23) w r; rwa [hw] at this
    obtain ⟨t, r', he, ht, h1, h2, h3, h4⟩ := readUnaryC_spec w x rG hwx hwg hxg r₁
      (by simp [r₁, StackMachine.set_other _ (Ne.symm hwg), hg])
    have e1 : r₁ w = rest := by simp [r₁]
    have e2 : r₁ x = r x := by simp [r₁, StackMachine.set_other _ (Ne.symm hwx)]
    rw [e1, e2] at he h1 h2
    rw [e1] at ht
    have hseq := Exec.seq hp he
    refine ⟨2 + t + 1, r', ?_, ?_, by simpa [litModel] using h1, by simpa [litModel] using h2, h3, ?_⟩
    · cases b
      · exact Exec.branchZero hw hseq
      · exact Exec.branchOne hw hseq
    · simp only [List.length_cons]; omega
    · intro j hj1 hj2 hj3
      rw [h4 j hj1 hj2 hj3]
      simp [r₁, StackMachine.set_other _ hj1]

/-! ### Distinctness tests -/

def neqC (x y : Fin 24) : Command 23 := .ifThenElse (eqU x y rT1 rT2 rS) (.stop false) (.stop true)

theorem neqC_spec (x y : Fin 24) (hxt₁ : x ≠ rT1) (hxt₂ : x ≠ rT2) (hxs : x ≠ rS)
    (hyt₁ : y ≠ rT1) (hyt₂ : y ≠ rT2) (hys : y ≠ rS) (r : Regs) (h₁ : r rT1 = [])
    (h₂ : r rT2 = []) (hs : r rS = []) :
    ∃ t, Exec (neqC x y) r t (!decide ((r x).length = (r y).length), r) ∧
      t ≤ 10 * ((r x).length + (r y).length) + 31 := by
  obtain ⟨t, r', he, ht, hr⟩ := eqU_spec x y rT1 rT2 rS hxt₁ hxt₂ hxs hyt₁ hyt₂ hys
    (by decide) (by decide) (by decide) r h₁ h₂ hs
  rw [hr] at he
  by_cases heq : (r x).length = (r y).length
  · rw [show decide ((r x).length = (r y).length) = true by simp [heq]] at he
    exact ⟨t + 1, by simpa [neqC, heq] using Exec.ifTrue he (Exec.stop false r), by omega⟩
  · rw [show decide ((r x).length = (r y).length) = false by simp [heq]] at he
    exact ⟨t + 1, by simpa [neqC, heq] using Exec.ifFalse he (Exec.stop true r), by omega⟩

/-! ### One clause -/

def readThree : Command 23 :=
  .seq (header3 rW) (.seq (readLit rW rA) (.seq (readLit rW rB) (readLit rW rC)))

def testThree : Command 23 :=
  .seq (neqC rA rB) (.seq (neqC rA rC) (.seq (neqC rB rC)
    (.seq (.clear rA) (.seq (.clear rB) (.clear rC)))))

def exactClause : Command 23 := .seq readThree testThree

/-- The three variables read from a clause code, as unary numerals, and the rest. -/
def readThreeModel (w : Word) : Option (Word × Word × Word × Word) :=
  match header3Model w with
  | none => none
  | some w1 =>
    match litModel w1 [] with
    | (false, _, _) => none
    | (true, w2, a) =>
      match litModel w2 [] with
      | (false, _, _) => none
      | (true, w3, b) =>
        match litModel w3 [] with
        | (false, _, _) => none
        | (true, w4, c) => some (w4, a, b, c)

def distinctThree (a b c : Word) : Bool :=
  !decide (a.length = b.length) && !decide (a.length = c.length) && !decide (b.length = c.length)

def exactClauseModel (w : Word) : Option Word :=
  match readThreeModel w with
  | none => none
  | some (w4, a, b, c) => if distinctThree a b c then some w4 else none

/-- The work registers are empty. -/
def Clean (r : Regs) : Prop :=
  r rA = [] ∧ r rB = [] ∧ r rC = [] ∧ r rT1 = [] ∧ r rT2 = [] ∧ r rS = [] ∧ r rG = []

theorem readThree_spec (r : Regs) (hc : Clean r) :
    ∃ t r', Exec readThree r t ((readThreeModel (r rW)).isSome, r') ∧
      t ≤ 30 * (r rW).length + 50 ∧
      (∀ w4 a b c, readThreeModel (r rW) = some (w4, a, b, c) →
        r' rW = w4 ∧ r' rA = a ∧ r' rB = b ∧ r' rC = c ∧ r' rT1 = [] ∧ r' rT2 = [] ∧
          r' rS = [] ∧ r' rG = [] ∧ w4.length ≤ (r rW).length ∧ a.length ≤ (r rW).length ∧
          b.length ≤ (r rW).length ∧ c.length ≤ (r rW).length) := by
  obtain ⟨hA, hB, hC, hT1, hT2, hS, hG⟩ := hc
  obtain ⟨t0, r0, e0, ht0, hw0, fr0⟩ := header3_spec rW r
  cases hm : header3Model (r rW) with
  | none =>
    rw [hm] at e0
    refine ⟨t0, r0, ?_, by omega, ?_⟩
    · simpa [readThree, readThreeModel, hm] using Exec.seqFailure (second := (Command.seq (readLit rW rA)
        (Command.seq (readLit rW rB) (readLit rW rC)))) e0
    · intro w4 a b c h; simp [readThreeModel, hm] at h
  | some w1 =>
    rw [hm] at e0
    have hw1 : r0 rW = w1 := hw0 w1 hm
    have hlen1 : w1.length + 4 = (r rW).length := by
      revert hm
      generalize r rW = w
      intro hm
      match w, hm with
      | true :: true :: true :: false :: rest, hm => simp [header3Model] at hm; subst hm; simp
    have g0 : r0 rG = [] := by rw [fr0 rG (by decide)]; exact hG
    obtain ⟨t1, r1, e1, ht1, hw1', hx1, hg1, fr1⟩ := readLit_spec rW rA (by decide) (by decide)
      (by decide) r0 g0
    have a0 : r0 rA = [] := by rw [fr0 rA (by decide)]; exact hA
    rw [hw1, a0] at e1 hw1' hx1
    rw [hw1] at ht1
    cases hl1 : litModel w1 [] with
    | mk b1 rest1 =>
      obtain ⟨w2, a⟩ := rest1
      rw [hl1] at e1 hw1' hx1
      cases b1 with
      | false =>
        refine ⟨t0 + t1, r1, ?_, by omega, ?_⟩
        · have := Exec.seq e0 (Exec.seqFailure (second := (Command.seq (readLit rW rB)
            (readLit rW rC))) e1)
          simpa [readThree, readThreeModel, hm, hl1] using this
        · intro w4 a b c h; simp [readThreeModel, hm, hl1] at h
      | true =>
        have hla := litModel_dst_le w1 []
        have hlw := litModel_src_le w1 []
        rw [hl1] at hla hlw
        simp only [List.length_nil, Nat.add_zero] at hla hlw
        obtain ⟨t2, r2, e2, ht2, hw2', hx2, hg2, fr2⟩ := readLit_spec rW rB (by decide) (by decide)
          (by decide) r1 hg1
        have b1' : r1 rB = [] := by
          rw [fr1 rB (by decide) (by decide) (by decide), fr0 rB (by decide)]; exact hB
        simp only at hw1' hx1
        rw [hw1', b1'] at e2 hw2' hx2
        rw [hw1'] at ht2
        cases hl2 : litModel w2 [] with
        | mk b2 rest2 =>
          obtain ⟨w3, bb⟩ := rest2
          rw [hl2] at e2 hw2' hx2
          cases b2 with
          | false =>
            refine ⟨t0 + (t1 + t2), r2, ?_, by omega, ?_⟩
            · have := Exec.seq e0 (Exec.seq e1 (Exec.seqFailure (second := readLit rW rC) e2))
              simpa [readThree, readThreeModel, hm, hl1, hl2] using this
            · intro w4 a b c h; simp [readThreeModel, hm, hl1, hl2] at h
          | true =>
            have hlb := litModel_dst_le w2 []
            have hlw2 := litModel_src_le w2 []
            rw [hl2] at hlb hlw2
            simp only [List.length_nil, Nat.add_zero] at hlb hlw2
            obtain ⟨t3, r3, e3, ht3, hw3', hx3, hg3, fr3⟩ := readLit_spec rW rC (by decide)
              (by decide) (by decide) r2 hg2
            have c2 : r2 rC = [] := by
              rw [fr2 rC (by decide) (by decide) (by decide),
                fr1 rC (by decide) (by decide) (by decide), fr0 rC (by decide)]; exact hC
            simp only at hw2' hx2
            rw [hw2', c2] at e3 hw3' hx3
            rw [hw2'] at ht3
            cases hl3 : litModel w3 [] with
            | mk b3 rest3 =>
              obtain ⟨w4, cc⟩ := rest3
              rw [hl3] at e3 hw3' hx3
              have hlc := litModel_dst_le w3 []
              have hlw3 := litModel_src_le w3 []
              rw [hl3] at hlc hlw3
              simp only [List.length_nil, Nat.add_zero] at hlc hlw3
              refine ⟨t0 + (t1 + (t2 + t3)), r3, ?_, by omega, ?_⟩
              · have := Exec.seq e0 (Exec.seq e1 (Exec.seq e2 e3))
                cases b3 <;> simpa [readThree, readThreeModel, hm, hl1, hl2, hl3] using this
              · intro w4' a' b' c' h
                cases b3 with
                | false => simp [readThreeModel, hm, hl1, hl2, hl3] at h
                | true =>
                  simp [readThreeModel, hm, hl1, hl2, hl3] at h
                  obtain ⟨rfl, rfl, rfl, rfl⟩ := h
                  simp only at hw3' hx3
                  have fA : r3 rA = a := by
                    rw [fr3 rA (by decide) (by decide) (by decide),
                      fr2 rA (by decide) (by decide) (by decide)]; exact hx1
                  have fB : r3 rB = bb := by
                    rw [fr3 rB (by decide) (by decide) (by decide)]; exact hx2
                  have frT : ∀ j : Fin 24, j ≠ rW → j ≠ rA → j ≠ rB → j ≠ rC → j ≠ rG →
                      r3 j = r j := by
                    intro j h1 h2 h3 h4 h5
                    rw [fr3 j h1 h4 h5, fr2 j h1 h3 h5, fr1 j h1 h2 h5, fr0 j h1]
                  refine ⟨hw3', fA, fB, hx3, ?_, ?_, ?_, hg3, by omega, by omega, by omega,
                    by omega⟩
                  · rw [frT rT1 (by decide) (by decide) (by decide) (by decide) (by decide)]
                    exact hT1
                  · rw [frT rT2 (by decide) (by decide) (by decide) (by decide) (by decide)]
                    exact hT2
                  · rw [frT rS (by decide) (by decide) (by decide) (by decide) (by decide)]
                    exact hS

theorem testThree_spec (r : Regs) (hT1 : r rT1 = []) (hT2 : r rT2 = []) (hS : r rS = []) :
    ∃ t r', Exec testThree r t (distinctThree (r rA) (r rB) (r rC), r') ∧
      t ≤ 25 * ((r rA).length + (r rB).length + (r rC).length) + 110 ∧
      (distinctThree (r rA) (r rB) (r rC) = true →
        r' rA = [] ∧ r' rB = [] ∧ r' rC = [] ∧ ∀ j, j ≠ rA → j ≠ rB → j ≠ rC → r' j = r j) := by
  obtain ⟨t1, e1, ht1⟩ := neqC_spec rA rB (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) r hT1 hT2 hS
  obtain ⟨t2, e2, ht2⟩ := neqC_spec rA rC (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) r hT1 hT2 hS
  obtain ⟨t3, e3, ht3⟩ := neqC_spec rB rC (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) r hT1 hT2 hS
  by_cases hab : (r rA).length = (r rB).length
  · rw [show (!decide ((r rA).length = (r rB).length)) = false by simp [hab]] at e1
    refine ⟨t1, r, ?_, by omega, ?_⟩
    · simpa [testThree, distinctThree, hab] using Exec.seqFailure (second := (Command.seq (neqC rA rC)
        (Command.seq (neqC rB rC) (Command.seq (.clear rA) (Command.seq (.clear rB) (.clear rC))))))
        e1
    · intro h; simp [distinctThree, hab] at h
  · rw [show (!decide ((r rA).length = (r rB).length)) = true by simp [hab]] at e1
    by_cases hac : (r rA).length = (r rC).length
    · rw [show (!decide ((r rA).length = (r rC).length)) = false by simp [hac]] at e2
      refine ⟨t1 + t2, r, ?_, by omega, ?_⟩
      · simpa [testThree, distinctThree, hab, hac] using Exec.seq e1 (Exec.seqFailure (second :=
          (Command.seq (neqC rB rC) (Command.seq (.clear rA) (Command.seq (.clear rB)
            (.clear rC))))) e2)
      · intro h; simp [distinctThree, hac] at h
    · rw [show (!decide ((r rA).length = (r rC).length)) = true by simp [hac]] at e2
      by_cases hbc : (r rB).length = (r rC).length
      · rw [show (!decide ((r rB).length = (r rC).length)) = false by simp [hbc]] at e3
        refine ⟨t1 + (t2 + t3), r, ?_, by omega, ?_⟩
        · simpa [testThree, distinctThree, hab, hac, hbc] using Exec.seq e1 (Exec.seq e2 (Exec.seqFailure
            (second := (Command.seq (.clear rA) (Command.seq (.clear rB) (.clear rC)))) e3))
        · intro h; simp [distinctThree, hbc] at h
      · rw [show (!decide ((r rB).length = (r rC).length)) = true by simp [hbc]] at e3
        let rA' := set r rA []
        let rB' := set rA' rB []
        let rC' := set rB' rC []
        have ec : Exec (Command.seq (.clear rA) (Command.seq (.clear rB) (.clear rC))) r
            ((r rA).length + 2 + ((rA' rB).length + 2 + ((rB' rC).length + 2))) (true, rC') :=
          Exec.seq (Exec.clear rA r) (Exec.seq (Exec.clear rB rA') (Exec.clear rC rB'))
        have l1 : (rA' rB).length = (r rB).length := by
          simp [rA', StackMachine.set_other _ (show rB ≠ rA by decide)]
        have l2 : (rB' rC).length = (r rC).length := by
          simp [rB', rA', StackMachine.set_other _ (show rC ≠ rB by decide),
            StackMachine.set_other _ (show rC ≠ rA by decide)]
        refine ⟨t1 + (t2 + (t3 + ((r rA).length + 2 + ((rA' rB).length + 2 +
          ((rB' rC).length + 2))))), rC', ?_, by omega, ?_⟩
        · simpa [testThree, distinctThree, hab, hac, hbc] using Exec.seq e1 (Exec.seq e2 (Exec.seq e3 ec))
        · intro _
          refine ⟨by simp [rC', rB', rA', StackMachine.set_other _ (show rA ≠ rC by decide),
              StackMachine.set_other _ (show rA ≠ rB by decide)],
            by simp [rC', rB', StackMachine.set_other _ (show rB ≠ rC by decide)],
            by simp [rC'], ?_⟩
          intro j h1 h2 h3
          simp [rC', rB', rA', StackMachine.set_other _ h1, StackMachine.set_other _ h2,
            StackMachine.set_other _ h3]

theorem exactClause_spec (r : Regs) (hc : Clean r) :
    ∃ t r', Exec exactClause r t ((exactClauseModel (r rW)).isSome, r') ∧
      t ≤ 120 * (r rW).length + 200 ∧
      (∀ w', exactClauseModel (r rW) = some w' →
        r' rW = w' ∧ Clean r' ∧ w'.length ≤ (r rW).length) := by
  obtain ⟨t1, r1, e1, ht1, h1⟩ := readThree_spec r hc
  cases hm : readThreeModel (r rW) with
  | none =>
    rw [hm] at e1
    refine ⟨t1, r1, ?_, by omega, ?_⟩
    · simpa [exactClause, exactClauseModel, hm] using Exec.seqFailure (second := testThree) e1
    · intro w' h; simp [exactClauseModel, hm] at h
  | some val =>
    obtain ⟨w4, a, b, c⟩ := val
    rw [hm] at e1
    obtain ⟨hw4, hA, hB, hC, hT1, hT2, hS, hG, hl4, hla, hlb, hlc⟩ := h1 w4 a b c hm
    obtain ⟨t2, r2, e2, ht2, h2⟩ := testThree_spec r1 hT1 hT2 hS
    rw [hA, hB, hC] at e2 ht2 h2
    refine ⟨t1 + t2, r2, ?_, by omega, ?_⟩
    · have := Exec.seq e1 e2
      cases hd : distinctThree a b c <;> simpa [exactClause, exactClauseModel, hm, hd] using this
    · intro w' h
      cases hd : distinctThree a b c with
      | false => simp [exactClauseModel, hm, hd] at h
      | true =>
        simp [exactClauseModel, hm, hd] at h
        subst h
        obtain ⟨gA, gB, gC, gfr⟩ := h2 hd
        refine ⟨by rw [gfr rW (by decide) (by decide) (by decide)]; exact hw4,
          ⟨gA, gB, gC, ?_, ?_, ?_, ?_⟩, hl4⟩
        · rw [gfr rT1 (by decide) (by decide) (by decide)]; exact hT1
        · rw [gfr rT2 (by decide) (by decide) (by decide)]; exact hT2
        · rw [gfr rS (by decide) (by decide) (by decide)]; exact hS
        · rw [gfr rG (by decide) (by decide) (by decide)]; exact hG

/-! ### All clauses -/

def exactLoopModel : Nat → Word → Option Word
  | 0, w => some w
  | m + 1, w =>
    match exactClauseModel w with
    | none => none
    | some w' => exactLoopModel m w'

theorem exactLoop_spec : ∀ (m : Nat) (r : Regs), (r rKC).length = m → Clean r →
    ∃ t r', Exec (.repeat rKC exactClause) r t ((exactLoopModel m (r rW)).isSome, r') ∧
      t ≤ m * (120 * (r rW).length + 201) + 2 := by
  intro m
  induction m with
  | zero =>
    intro r hm _
    exact ⟨2, r, Exec.repeatDone (List.eq_nil_of_length_eq_zero hm), by omega⟩
  | succ m ih =>
    intro r hm hc
    obtain ⟨b, tail, hkc⟩ : ∃ b tail, r rKC = b :: tail := by
      cases h : r rKC with
      | nil => rw [h] at hm; simp at hm
      | cons b tail => exact ⟨b, tail, rfl⟩
    let r₀ := set r rKC tail
    have hc₀ : Clean r₀ := by
      obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hc
      exact ⟨by simp +decide [r₀, h1], by simp +decide [r₀, h2], by simp +decide [r₀, h3], by simp +decide [r₀, h4],
        by simp +decide [r₀, h5], by simp +decide [r₀, h6], by simp +decide [r₀, h7]⟩
    have hw₀ : r₀ rW = r rW := by simp +decide [r₀]
    obtain ⟨t1, r1, e1, ht1, h1⟩ := exactClause_spec r₀ hc₀
    rw [hw₀] at e1 ht1 h1
    cases hmod : exactClauseModel (r rW) with
    | none =>
      rw [hmod] at e1
      refine ⟨t1 + 1, r1, ?_, ?_⟩
      · simpa [exactLoopModel, hmod] using Exec.repeatFailure hkc e1
      · have : 0 ≤ m * (120 * (r rW).length + 201) := Nat.zero_le _
        rw [Nat.succ_mul]; omega
    | some w' =>
      rw [hmod] at e1
      obtain ⟨hw1, hc1, hl1⟩ := h1 w' hmod
      have hkc1 : (r1 rKC).length = m := by
        have := exec_frame e1 rKC (by decide)
        simp only at this
        rw [this]
        simp [r₀]
        rw [hkc] at hm
        simpa using hm
      obtain ⟨t2, r2, e2, ht2⟩ := ih r1 hkc1 hc1
      rw [hw1] at e2 ht2
      refine ⟨t1 + t2 + 1, r2, ?_, ?_⟩
      · simpa [exactLoopModel, hmod] using Exec.repeatNext hkc e1 e2
      · have := Nat.mul_le_mul_left m (show 120 * w'.length + 201 ≤ 120 * (r rW).length + 201 by
          omega)
        rw [Nat.succ_mul]; omega

/-! ### The whole check -/

def exactCheck : Command 23 :=
  .seq (.copy rIn rW rS) (.seq (readUnaryC rW rKC rG) (.repeat rKC exactClause))

/-- The decision of `exactCheck` on an input word. -/
def exactModel (x : Word) : Bool :=
  match unaryModel x [] with
  | (false, _, _) => false
  | (true, rest, kc) => (exactLoopModel kc.length rest).isSome

/-- Registers `7, …, 23` are empty. -/
def HighEmpty (r : Regs) : Prop := ∀ j : Fin 24, 7 ≤ j.val → r j = []

theorem exactCheck_writes : ∀ j : Fin 24, j.val < 7 → writes exactCheck j = false := by
  decide

theorem exactCheck_spec (r : Regs) (hr : HighEmpty r) :
    ∃ t r', Exec exactCheck r t (exactModel (r rIn), r') ∧
      t ≤ 250 * ((r rIn).length + 1) ^ 2 ∧ ∀ j : Fin 24, j.val < 7 → r' j = r j := by
  let r₁ := set r rW (r rIn)
  have ec : Exec (.copy rIn rW rS) r ((r rW).length + 5 * (r rIn).length + 6) (true, r₁) :=
    Exec.copy (by decide) (by decide) (by decide) (hr rS (by decide))
  have hW0 : (r rW).length = 0 := by simp [hr rW (by decide)]
  obtain ⟨t2, r₂, e2, ht2, hw2, hk2, hg2, fr2⟩ := readUnaryC_spec rW rKC rG (by decide)
    (by decide) (by decide) r₁ (by simp +decide [r₁, hr rG (by decide)])
  have e1w : r₁ rW = r rIn := by simp [r₁]
  have e1k : r₁ rKC = [] := by simp +decide [r₁, hr rKC (by decide)]
  rw [e1w, e1k] at e2 hw2 hk2
  rw [e1w] at ht2
  have hframe : ∀ (res : Bool × Regs) (t : Nat), Exec exactCheck r t res →
      ∀ j : Fin 24, j.val < 7 → res.2 j = r j := by
    intro res t h j hj
    exact exec_frame h j (exactCheck_writes j hj)
  cases hu : unaryModel (r rIn) [] with
  | mk b rest =>
    obtain ⟨rest, kc⟩ := rest
    rw [hu] at e2 hw2 hk2
    dsimp only at hw2 hk2
    cases b with
    | false =>
      have he : Exec exactCheck r _ (false, r₂) :=
        Exec.seq ec (Exec.seqFailure (second := .repeat rKC exactClause) e2)
      refine ⟨_, r₂, by simpa [exactModel, hu] using he, ?_, hframe _ _ he⟩
      have : (r rIn).length + 1 ≤ ((r rIn).length + 1) ^ 2 := Nat.le_self_pow (by decide) _
      omega
    | true =>
      have hlen := unaryModel_length (r rIn) []
      rw [hu] at hlen
      simp only [List.length_nil, Nat.add_zero] at hlen
      have hc₂ : Clean r₂ := by
        have z : ∀ j : Fin 24, j ≠ rW → j ≠ rKC → j ≠ rG → 7 ≤ j.val → r₂ j = [] := by
          intro j h1 h2 h3 h4
          rw [fr2 j h1 h2 h3]
          simp [r₁, StackMachine.set_other _ h1, hr j h4]
        exact ⟨z rA (by decide) (by decide) (by decide) (by decide),
          z rB (by decide) (by decide) (by decide) (by decide),
          z rC (by decide) (by decide) (by decide) (by decide),
          z rT1 (by decide) (by decide) (by decide) (by decide),
          z rT2 (by decide) (by decide) (by decide) (by decide),
          z rS (by decide) (by decide) (by decide) (by decide), hg2⟩
      obtain ⟨t3, r₃, e3, ht3⟩ := exactLoop_spec kc.length r₂ (by rw [hk2]) hc₂
      rw [hw2] at e3 ht3
      have he : Exec exactCheck r _ ((exactLoopModel kc.length rest).isSome, r₃) :=
        Exec.seq ec (Exec.seq e2 e3)
      refine ⟨_, r₃, by simpa [exactModel, hu] using he, ?_, hframe _ _ he⟩
      have hk : kc.length ≤ (r rIn).length := by omega
      have hrest : rest.length ≤ (r rIn).length := by omega
      have h1 := Nat.mul_le_mul hk
        (show 120 * rest.length + 201 ≤ 120 * (r rIn).length + 201 by omega)
      generalize (r rIn).length = n at *
      have h2 : (n + 1) ^ 2 = n * n + 2 * n + 1 := by
        rw [Nat.pow_two]; simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one, Nat.one_mul]; omega
      rw [h2]
      have h3 : n * (120 * n + 201) = 120 * (n * n) + 201 * n := by
        simp only [Nat.mul_add, Nat.mul_left_comm n 120 n, Nat.mul_comm n 201]
      omega

/-! ### Semantics on encoded formulas -/

theorem header3Model_writeNat (n : Nat) (rest : Word) :
    header3Model (writeNat n ++ rest) = if n = 3 then some rest else none := by
  match n with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | 3 => rfl
  | n + 4 => simp [writeNat, header3Model]

abbrev exactOK (c : Clause) : Prop := c.length = 3 ∧ (c.map Literal.var).Nodup

theorem exactClauseModel_encode (c : Clause) (rest : Word) :
    exactClauseModel (encodeClause c ++ rest) = if exactOK c then some rest else none := by
  unfold encodeClause writeList
  rw [List.append_assoc, exactClauseModel, readThreeModel, header3Model_writeNat]
  by_cases h3 : c.length = 3
  · match c, h3 with
    | [l1, l2, l3], _ =>
      simp only [List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, ↓reduceIte,
        writeValues, List.append_assoc, List.append_nil]
      rw [litModel_encodeLiteral]; dsimp only; rw [litModel_encodeLiteral]; dsimp only
      rw [litModel_encodeLiteral]; dsimp only
      simp only [distinctThree, List.length_replicate, List.append_nil]
      by_cases e12 : l1.var = l2.var <;> by_cases e13 : l1.var = l3.var <;>
        by_cases e23 : l2.var = l3.var <;> simp [exactOK, e12, e13, e23]
  · simp [h3, exactOK]

theorem exactLoopModel_encode (f : CNF) (rest : Word) :
    exactLoopModel f.length (writeValues encodeClause f ++ rest) =
      if ∀ c ∈ f, exactOK c then some rest else none := by
  induction f with
  | nil => simp [exactLoopModel, writeValues]
  | cons c f ih =>
    simp only [List.length_cons, exactLoopModel, writeValues, List.append_assoc,
      exactClauseModel_encode, List.forall_mem_cons]
    by_cases hc : exactOK c
    · rw [ite_eq_left hc]
      dsimp only
      rw [ih]
      by_cases hf : ∀ a ∈ f, exactOK a
      · rw [ite_eq_left hf, ite_eq_left ⟨hc, hf⟩]
      · rw [ite_eq_right hf, ite_eq_right (fun h => hf h.2)]
    · rw [ite_eq_right hc]
      dsimp only
      rw [ite_eq_right (fun h => hc h.1)]

theorem exactModel_encode (f : CNF) : exactModel (encode f) = true ↔ IsExactThreeCNF f := by
  have h := unaryModel_writeNat f.length (writeValues encodeClause f) []
  simp only [List.append_nil] at h
  unfold encode writeList
  rw [exactModel, h]
  simp only [List.length_replicate]
  have := exactLoopModel_encode f []
  simp only [List.append_nil] at this
  rw [this]
  by_cases hf : ∀ c ∈ f, exactOK c
  · rw [ite_eq_left hf]
    simp only [Option.isSome_some, true_iff]
    exact hf
  · rw [ite_eq_right hf]
    simp only [Option.isSome_none, Bool.false_eq_true, false_iff]
    exact hf

end Complexity.Restricted
