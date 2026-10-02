module

public import Complexity.StackTableauProgram
public import Complexity.SAT
import Lean.Elab.Tactic.Omega

/-!
# Reusable commands for syntactic checks

Small programs in the structured stack language `StackTableauProgram.Command`, with their
exact behavior and instruction counts:

* `Exec.frame`: a command leaves every register it does not write unchanged;
* `readUnaryC src dst g`: pop a unary numeral `1…10` from `src`, pushing its ones onto `dst`;
* `eqU x y t₁ t₂ s`: compare the lengths of `x` and `y`, using the empty temporaries `t₁`, `t₂`
  and scratch `s`, and restore the temporaries;
* `header3 w`: pop the unary numeral `3` from `w`, failing on any other header.
-/

@[expose] public section

namespace Complexity.Restricted

open StackTableauProgram (Command Exec)
open StackMachine (Registers set)

variable {k : Nat}

/-! ### Frame -/

/-- The registers a command may write. -/
def writes : Command k → Fin (k + 1) → Bool
  | .stop _, _ => false
  | .push j _, i => decide (i = j)
  | .pop j, i => decide (i = j)
  | .clear j, i => decide (i = j)
  | .copy _ dst _, i => decide (i = dst)
  | .length _ dst _, i => decide (i = dst)
  | .add _ dst _, i => decide (i = dst)
  | .multiply _ _ dst counter _, i => decide (i = dst) || decide (i = counter)
  | .prependNat _ out _, i => decide (i = out)
  | .prependLiteral _ out _ _, i => decide (i = out)
  | .seq a b, i => writes a i || writes b i
  | .ifThenElse t y n, i => writes t i || writes y i || writes n i
  | .branch _ e z o, i => writes e i || writes z i || writes o i
  | .repeat j body, i => decide (i = j) || writes body i

theorem exec_frame {c : Command k} {r : Registers k} {t : Nat} {res : Bool × Registers k}
    (h : Exec c r t res) : ∀ i, writes c i = false → res.2 i = r i := by
  induction h with
  | stop b r => intro i _; rfl
  | push j b r =>
    intro i hi
    simp only [writes, decide_eq_false_iff_not] at hi
    exact StackMachine.set_other _ hi _
  | pop j r =>
    intro i hi
    simp only [writes, decide_eq_false_iff_not] at hi
    exact StackMachine.set_other _ hi _
  | clear j r =>
    intro i hi
    simp only [writes, decide_eq_false_iff_not] at hi
    exact StackMachine.set_other _ hi _
  | copy =>
    intro i hi
    simp only [writes, decide_eq_false_iff_not] at hi
    exact StackMachine.set_other _ hi _
  | length =>
    intro i hi
    simp only [writes, decide_eq_false_iff_not] at hi
    exact StackMachine.set_other _ hi _
  | add =>
    intro i hi
    simp only [writes, decide_eq_false_iff_not] at hi
    exact StackMachine.set_other _ hi _
  | multiply =>
    intro i hi
    simp only [writes, Bool.or_eq_false_iff, decide_eq_false_iff_not] at hi
    simp only [StackMachine.set_other _ hi.1, StackMachine.set_other _ hi.2]
  | prependNat =>
    intro i hi
    simp only [writes, decide_eq_false_iff_not] at hi
    exact StackMachine.set_other _ hi _
  | prependLiteral =>
    intro i hi
    simp only [writes, decide_eq_false_iff_not] at hi
    exact StackMachine.set_other _ hi _
  | seq _ _ ih1 ih2 =>
    intro i hi
    simp only [writes, Bool.or_eq_false_iff] at hi
    exact (ih2 i hi.2).trans (ih1 i hi.1)
  | seqFailure _ ih =>
    intro i hi
    simp only [writes, Bool.or_eq_false_iff] at hi
    exact ih i hi.1
  | ifTrue _ _ ih1 ih2 =>
    intro i hi
    simp only [writes, Bool.or_eq_false_iff] at hi
    exact (ih2 i hi.1.2).trans (ih1 i hi.1.1)
  | ifFalse _ _ ih1 ih2 =>
    intro i hi
    simp only [writes, Bool.or_eq_false_iff] at hi
    exact (ih2 i hi.2).trans (ih1 i hi.1.1)
  | branchEmpty _ _ ih =>
    intro i hi
    simp only [writes, Bool.or_eq_false_iff] at hi
    exact ih i hi.1.1
  | branchZero _ _ ih =>
    intro i hi
    simp only [writes, Bool.or_eq_false_iff] at hi
    exact ih i hi.1.2
  | branchOne _ _ ih =>
    intro i hi
    simp only [writes, Bool.or_eq_false_iff] at hi
    exact ih i hi.2
  | repeatDone _ => intro i _; rfl
  | repeatNext _ _ _ ih1 ih2 =>
    intro i hi
    have hi' := hi
    simp only [writes, Bool.or_eq_false_iff, decide_eq_false_iff_not] at hi'
    have h1 := ih1 i hi'.2
    simp only at h1
    rw [ih2 i hi, h1, StackMachine.set_other _ hi'.1]
  | repeatFailure _ _ ih =>
    intro i hi
    simp only [writes, Bool.or_eq_false_iff, decide_eq_false_iff_not] at hi
    rw [ih i hi.2, StackMachine.set_other _ hi.1]

/-! ### Reading a unary numeral -/

def readUnaryBody (src dst g : Fin (k + 1)) : Command k :=
  .branch src (.stop false) (.pop src) (.seq (.pop src) (.seq (.push dst true) (.push g true)))

/-- Pop `1^v 0` from `src` and push `v` ones onto `dst`; `g` is an empty loop register. -/
def readUnaryC (src dst g : Fin (k + 1)) : Command k :=
  .seq (.push g true) (.repeat g (readUnaryBody src dst g))

/-- The decision, the rest of `src` and the new `dst` of `readUnaryC`. -/
def unaryModel : SAT.Word → SAT.Word → Bool × SAT.Word × SAT.Word
  | [], d => (false, [], d)
  | false :: rest, d => (true, rest, d)
  | true :: rest, d => unaryModel rest (true :: d)

theorem replicate_append_cons {α : Type} (a : α) (l : List α) :
    ∀ n, List.replicate n a ++ a :: l = a :: (List.replicate n a ++ l)
  | 0 => rfl
  | n + 1 => by simp [List.replicate_succ, replicate_append_cons a l n]

theorem unaryModel_writeNat (n : Nat) (rest d : SAT.Word) :
    unaryModel (SAT.writeNat n ++ rest) d = (true, rest, List.replicate n true ++ d) := by
  induction n generalizing d with
  | zero => rfl
  | succ n ih =>
    simp only [SAT.writeNat, List.cons_append, unaryModel, ih, replicate_append_cons,
      List.replicate_succ, List.cons_append]

theorem unaryModel_length (w d : SAT.Word) :
    (unaryModel w d).2.1.length + (unaryModel w d).2.2.length ≤ w.length + d.length := by
  induction w generalizing d with
  | nil => simp [unaryModel]
  | cons b rest ih =>
    cases b with
    | false => simp [unaryModel]
    | true =>
      have := ih (true :: d)
      simp only [unaryModel, List.length_cons] at this ⊢
      omega

theorem unaryModel_src_le (w d : SAT.Word) : (unaryModel w d).2.1.length ≤ w.length := by
  induction w generalizing d with
  | nil => simp [unaryModel]
  | cons b rest ih =>
    cases b with
    | false => simp [unaryModel]
    | true =>
      have := ih (true :: d)
      simp only [unaryModel, List.length_cons] at this ⊢
      omega

theorem readUnaryLoop_spec (src dst g : Fin (k + 1)) (hsd : src ≠ dst) (hsg : src ≠ g)
    (hdg : dst ≠ g) :
    ∀ (w d : SAT.Word) (r : Registers k), r g = [true] → r src = w → r dst = d →
      ∃ t r', Exec (.repeat g (readUnaryBody src dst g)) r t ((unaryModel w d).1, r') ∧
        t ≤ 8 * w.length + 6 ∧ r' src = (unaryModel w d).2.1 ∧
        r' dst = (unaryModel w d).2.2 ∧ r' g = [] ∧
        ∀ j, j ≠ src → j ≠ dst → j ≠ g → r' j = r j := by
  intro w
  induction w with
  | nil =>
    intro d r hg hs hd
    refine ⟨3, set r g [], ?_, by simp, ?_, ?_, ?_, ?_⟩
    · have hb : Exec (readUnaryBody src dst g) (set r g []) 2 (false, set r g []) :=
        Exec.branchEmpty (by simp [StackMachine.set_other _ hsg, hs]) (Exec.stop _ _)
      exact Exec.repeatFailure hg hb
    · simp [StackMachine.set_other _ hsg, hs, unaryModel]
    · simp [StackMachine.set_other _ hdg, hd, unaryModel]
    · simp
    · intro j _ _ hj
      exact StackMachine.set_other _ hj _
  | cons b rest ih =>
    intro d r hg hs hd
    cases b with
    | false =>
      let r₁ := set (set r g []) src rest
      refine ⟨6, r₁, ?_, by simp, ?_, ?_, ?_, ?_⟩
      · have hb : Exec (readUnaryBody src dst g) (set r g []) 3 (true, r₁) := by
          have := Exec.pop (k := k) src (set r g [])
          have hsrc : (set r g []) src = false :: rest := by
            simp [StackMachine.set_other _ hsg, hs]
          rw [hsrc] at this
          exact Exec.branchZero hsrc this
        have hdone : Exec (.repeat g (readUnaryBody src dst g)) r₁ 2 (true, r₁) :=
          Exec.repeatDone (by simp [r₁, StackMachine.set_other _ (Ne.symm hsg)])
        exact Exec.repeatNext hg hb hdone
      · simp [r₁, unaryModel]
      · simp [r₁, StackMachine.set_other _ hsd.symm, StackMachine.set_other _ hdg, hd, unaryModel]
      · simp [r₁, StackMachine.set_other _ (Ne.symm hsg)]
      · intro j hj1 _ hj3
        simp [r₁, StackMachine.set_other _ hj1, StackMachine.set_other _ hj3]
    | true =>
      let r₁ := set (set (set (set r g []) src rest) dst (true :: d)) g [true]
      have hsrc : (set r g []) src = true :: rest := by
        simp [StackMachine.set_other _ hsg, hs]
      have hb : Exec (readUnaryBody src dst g) (set r g []) 7 (true, r₁) := by
        have h1 := Exec.pop (k := k) src (set r g [])
        rw [hsrc] at h1
        have h2 := Exec.push (k := k) dst true (set (set r g []) src rest)
        have hd' : (set (set r g []) src rest) dst = d := by
          simp [StackMachine.set_other _ hsd.symm, StackMachine.set_other _ hdg, hd]
        rw [hd'] at h2
        have h3 := Exec.push (k := k) g true (set (set (set r g []) src rest) dst (true :: d))
        have hg' : (set (set (set r g []) src rest) dst (true :: d)) g = [] := by
          simp [StackMachine.set_other _ (Ne.symm hdg), StackMachine.set_other _ (Ne.symm hsg)]
        rw [hg'] at h3
        exact Exec.branchOne hsrc (Exec.seq h1 (Exec.seq h2 h3))
      obtain ⟨t, r', he, ht, h1, h2, h3, h4⟩ := ih (true :: d) r₁ (by simp [r₁])
        (by simp [r₁, StackMachine.set_other _ hsg, StackMachine.set_other _ hsd])
        (by simp [r₁, StackMachine.set_other _ hdg])
      refine ⟨7 + t + 1, r', Exec.repeatNext hg hb he, ?_, ?_, ?_, h3, ?_⟩
      · simp only [List.length_cons]; omega
      · simpa [unaryModel] using h1
      · simpa [unaryModel] using h2
      · intro j hj1 hj2 hj3
        rw [h4 j hj1 hj2 hj3]
        simp [r₁, StackMachine.set_other _ hj1, StackMachine.set_other _ hj2,
          StackMachine.set_other _ hj3]

theorem readUnaryC_spec (src dst g : Fin (k + 1)) (hsd : src ≠ dst) (hsg : src ≠ g)
    (hdg : dst ≠ g) (r : Registers k) (hg : r g = []) :
    ∃ t r', Exec (readUnaryC src dst g) r t ((unaryModel (r src) (r dst)).1, r') ∧
      t ≤ 8 * (r src).length + 8 ∧ r' src = (unaryModel (r src) (r dst)).2.1 ∧
      r' dst = (unaryModel (r src) (r dst)).2.2 ∧ r' g = [] ∧
      ∀ j, j ≠ src → j ≠ dst → j ≠ g → r' j = r j := by
  have hp := Exec.push (k := k) g true r
  rw [hg] at hp
  obtain ⟨t, r', he, ht, h1, h2, h3, h4⟩ := readUnaryLoop_spec src dst g hsd hsg hdg (r src)
    (r dst) (set r g [true]) (by simp) (by simp [StackMachine.set_other _ hsg])
    (by simp [StackMachine.set_other _ hdg])
  refine ⟨2 + t, r', Exec.seq hp he, by omega, h1, h2, h3, ?_⟩
  intro j hj1 hj2 hj3
  rw [h4 j hj1 hj2 hj3, StackMachine.set_other _ hj3]

/-! ### Comparing lengths -/

def drainBody (y : Fin (k + 1)) : Command k := .branch y (.stop false) (.pop y) (.pop y)

theorem drain_spec (x y : Fin (k + 1)) (hxy : x ≠ y) :
    ∀ (a b : SAT.Word) (r : Registers k), r x = a → r y = b →
      ∃ t r', Exec (.repeat x (drainBody y)) r t (decide (a.length ≤ b.length), r') ∧
        t ≤ 4 * a.length + 3 ∧
        (a.length ≤ b.length → r' x = [] ∧ (r' y).length = b.length - a.length) ∧
        (¬ a.length ≤ b.length → r' y = [] ∧ (r' x).length ≤ a.length) ∧
        ∀ j, j ≠ x → j ≠ y → r' j = r j := by
  intro a
  induction a with
  | nil =>
    intro b r hx hy
    refine ⟨2, r, Exec.repeatDone hx, by simp, ?_, ?_, ?_⟩
    · intro _; exact ⟨hx, by simp [hy]⟩
    · intro h; simp at h
    · intro j _ _; rfl
  | cons c a ih =>
    intro b r hx hy
    cases b with
    | nil =>
      have hy' : (set r x a) y = [] := by simp [StackMachine.set_other _ (Ne.symm hxy), hy]
      refine ⟨3, set r x a, ?_, by simp, ?_, ?_, ?_⟩
      · exact Exec.repeatFailure hx (Exec.branchEmpty hy' (Exec.stop _ _))
      · intro h; simp at h
      · intro _; exact ⟨hy', by simp⟩
      · intro j hj _; exact StackMachine.set_other _ hj _
    | cons e b =>
      have hy' : (set r x a) y = e :: b := by simp [StackMachine.set_other _ (Ne.symm hxy), hy]
      have hb : Exec (drainBody y) (set r x a) 3 (true, set (set r x a) y b) := by
        have h1 := Exec.pop (k := k) y (set r x a)
        rw [hy'] at h1
        cases e
        · exact Exec.branchZero hy' h1
        · exact Exec.branchOne hy' h1
      obtain ⟨t, r', he, ht, h1, h2, h3⟩ := ih b (set (set r x a) y b)
        (by simp [StackMachine.set_other _ hxy]) (by simp)
      refine ⟨3 + t + 1, r', ?_, ?_, ?_, ?_, ?_⟩
      · have := Exec.repeatNext hx hb he
        simpa using this
      · simp only [List.length_cons]; omega
      · intro h
        simp only [List.length_cons] at h ⊢
        obtain ⟨h1a, h1b⟩ := h1 (by omega)
        exact ⟨h1a, by omega⟩
      · intro h
        simp only [List.length_cons] at h ⊢
        obtain ⟨h2a, h2b⟩ := h2 (by omega)
        exact ⟨h2a, by omega⟩
      · intro j hj1 hj2
        rw [h3 j hj1 hj2]
        simp [StackMachine.set_other _ hj1, StackMachine.set_other _ hj2]

/-- Decide whether `x` and `y` have equal lengths; the temporaries end empty. -/
def eqU (x y t₁ t₂ s : Fin (k + 1)) : Command k :=
  .seq (.copy x t₁ s) (.seq (.copy y t₂ s)
    (.ifThenElse (.repeat t₁ (drainBody t₂))
      (.branch t₂ (.stop true) (.seq (.clear t₂) (.stop false)) (.seq (.clear t₂) (.stop false)))
      (.seq (.clear t₁) (.stop false))))

theorem eqU_spec (x y t₁ t₂ s : Fin (k + 1)) (hxt₁ : x ≠ t₁) (hxt₂ : x ≠ t₂) (hxs : x ≠ s)
    (hyt₁ : y ≠ t₁) (hyt₂ : y ≠ t₂) (hys : y ≠ s) (ht₁₂ : t₁ ≠ t₂) (ht₁s : t₁ ≠ s)
    (ht₂s : t₂ ≠ s) (r : Registers k) (h₁ : r t₁ = []) (h₂ : r t₂ = []) (hs : r s = []) :
    ∃ t r', Exec (eqU x y t₁ t₂ s) r t (decide ((r x).length = (r y).length), r') ∧
      t ≤ 10 * ((r x).length + (r y).length) + 30 ∧ r' = r := by
  let r₁ := set r t₁ (r x)
  have hc1 : Exec (.copy x t₁ s) r (0 + 5 * (r x).length + 6) (true, r₁) := by
    have := Exec.copy (k := k) (r := r) hxt₁ hxs ht₁s hs
    rwa [h₁] at this
  let r₂ := set r₁ t₂ (r y)
  have hc2 : Exec (.copy y t₂ s) r₁ (0 + 5 * (r y).length + 6) (true, r₂) := by
    have := Exec.copy (k := k) (r := r₁) hyt₂ hys ht₂s
      (by simp [r₁, StackMachine.set_other _ (Ne.symm ht₁s), hs])
    have e1 : r₁ t₂ = [] := by simp [r₁, StackMachine.set_other _ (Ne.symm ht₁₂), h₂]
    have e2 : r₁ y = r y := by simp [r₁, StackMachine.set_other _ hyt₁]
    rwa [e1, e2] at this
  obtain ⟨td, r₃, hd, htd, hle, hgt, hfr⟩ := drain_spec t₁ t₂ ht₁₂ (r x) (r y) r₂
    (by simp [r₂, r₁, StackMachine.set_other _ ht₁₂]) (by simp [r₂])
  have hback : ∀ (r' : Registers k), r' t₁ = [] → r' t₂ = [] →
      (∀ j, j ≠ t₁ → j ≠ t₂ → r' j = r₂ j) → r' = r := by
    intro r' e1 e2 e3
    funext j
    by_cases j1 : j = t₁
    · subst j1; rw [e1, h₁]
    · by_cases j2 : j = t₂
      · subst j2; rw [e2, h₂]
      · rw [e3 j j1 j2]
        simp [r₂, r₁, StackMachine.set_other _ j1, StackMachine.set_other _ j2]
  by_cases hab : (r x).length ≤ (r y).length
  · obtain ⟨hx3, hy3⟩ := hle hab
    have hdec : decide ((r x).length ≤ (r y).length) = true := by simp [hab]
    rw [hdec] at hd
    by_cases heq : (r x).length = (r y).length
    · have hy0 : r₃ t₂ = [] := List.eq_nil_of_length_eq_zero (by omega)
      have hbr : Exec (.branch t₂ (.stop true) (.seq (.clear t₂) (.stop false))
          (.seq (.clear t₂) (.stop false))) r₃ 2 (true, r₃) :=
        Exec.branchEmpty hy0 (Exec.stop _ _)
      rw [show decide ((r x).length = (r y).length) = true by simp [heq]]
      refine ⟨_, r₃, Exec.seq hc1 (Exec.seq hc2 (Exec.ifTrue hd hbr)), ?_,
        hback r₃ hx3 hy0 hfr⟩
      · simp [heq] at htd ⊢; omega
    · obtain ⟨c, tail, hct⟩ : ∃ c tail, r₃ t₂ = c :: tail := by
        cases h : r₃ t₂ with
        | nil => rw [h] at hy3; simp at hy3; omega
        | cons c tail => exact ⟨c, tail, rfl⟩
      let r₄ := set r₃ t₂ []
      have hcl : Exec (.seq (.clear t₂) (.stop false)) r₃ ((r₃ t₂).length + 2 + 1) (false, r₄) :=
        Exec.seq (Exec.clear t₂ r₃) (Exec.stop _ _)
      have hbr : Exec (.branch t₂ (.stop true) (.seq (.clear t₂) (.stop false))
          (.seq (.clear t₂) (.stop false))) r₃ ((r₃ t₂).length + 2 + 1 + 1) (false, r₄) := by
        cases c
        · exact Exec.branchZero hct hcl
        · exact Exec.branchOne hct hcl
      refine ⟨(0 + 5 * (r x).length + 6) + ((0 + 5 * (r y).length + 6) +
        (td + ((r₃ t₂).length + 2 + 1 + 1))), r₄, ?_, ?_, ?_⟩
      · have : Exec (eqU x y t₁ t₂ s) r _ (false, r₄) := Exec.seq hc1 (Exec.seq hc2 (Exec.ifTrue hd hbr))
        simpa [heq] using this
      · rw [hy3]; omega
      · apply hback r₄ (by simp [r₄, StackMachine.set_other _ ht₁₂, hx3]) (by simp [r₄])
        intro j hj1 hj2
        simp [r₄, StackMachine.set_other _ hj2, hfr j hj1 hj2]
  · obtain ⟨hy3, hx3⟩ := hgt hab
    have hdec : decide ((r x).length ≤ (r y).length) = false := by simp [hab]
    rw [hdec] at hd
    let r₄ := set r₃ t₁ []
    have hcl : Exec (.seq (.clear t₁) (.stop false)) r₃ ((r₃ t₁).length + 2 + 1) (false, r₄) :=
      Exec.seq (Exec.clear t₁ r₃) (Exec.stop _ _)
    refine ⟨(0 + 5 * (r x).length + 6) + ((0 + 5 * (r y).length + 6) +
      (td + ((r₃ t₁).length + 2 + 1))), r₄, ?_, ?_, ?_⟩
    · have : Exec (eqU x y t₁ t₂ s) r _ (false, r₄) := Exec.seq hc1 (Exec.seq hc2 (Exec.ifFalse hd hcl))
      have hne : ¬ (r x).length = (r y).length := by omega
      simpa [hne] using this
    · omega
    · apply hback r₄ (by simp [r₄]) (by simp [r₄, StackMachine.set_other _ (Ne.symm ht₁₂), hy3])
      intro j hj1 hj2
      simp [r₄, StackMachine.set_other _ hj1, hfr j hj1 hj2]

/-! ### Popping a fixed header -/

def popOne (w : Fin (k + 1)) (next : Command k) : Command k :=
  .branch w (.stop false) (.stop false) (.seq (.pop w) next)

/-- Pop the unary numeral `3` (the bits `1110`). -/
def header3 (w : Fin (k + 1)) : Command k :=
  popOne w (popOne w (popOne w (.branch w (.stop false) (.pop w) (.stop false))))

def header3Model : SAT.Word → Option SAT.Word
  | true :: true :: true :: false :: rest => some rest
  | _ => none

theorem header3_spec (w : Fin (k + 1)) (r : Registers k) :
    ∃ t r', Exec (header3 w) r t ((header3Model (r w)).isSome, r') ∧ t ≤ 12 ∧
      (∀ rest, header3Model (r w) = some rest → r' w = rest) ∧
      ∀ j, j ≠ w → r' j = r j := by
  match hw : r w with
  | [] =>
    refine ⟨2, r, Exec.branchEmpty hw (Exec.stop _ _), by simp, ?_, ?_⟩
    · intro rest h; simp [header3Model] at h
    · intro j _; rfl
  | false :: tail =>
    refine ⟨2, r, Exec.branchZero hw (Exec.stop _ _), by simp, ?_, ?_⟩
    · intro rest h; simp [header3Model] at h
    · intro j _; rfl
  | true :: tail =>
    let r₁ := set r w tail
    have hp1 : Exec (.pop w) r 2 (true, r₁) := by
      have := Exec.pop (k := k) w r; rwa [hw] at this
    have fr1 : ∀ j, j ≠ w → r₁ j = r j := fun j hj => StackMachine.set_other _ hj _
    match ht : tail with
    | [] =>
      have hr1 : r₁ w = [] := by simp [r₁, ht]
      refine ⟨2 + 2 + 1, r₁, Exec.branchOne hw (Exec.seq hp1 (Exec.branchEmpty hr1 (Exec.stop _ _))),
        by simp, ?_, fr1⟩
      intro rest h; simp [header3Model] at h
    | false :: tail2 =>
      have hr1 : r₁ w = false :: tail2 := by simp [r₁, ht]
      refine ⟨2 + 2 + 1, r₁, Exec.branchOne hw (Exec.seq hp1 (Exec.branchZero hr1 (Exec.stop _ _))),
        by simp, ?_, fr1⟩
      intro rest h; simp [header3Model] at h
    | true :: tail2 =>
      have hr1 : r₁ w = true :: tail2 := by simp [r₁, ht]
      let r₂ := set r₁ w tail2
      have hp2 : Exec (.pop w) r₁ 2 (true, r₂) := by
        have := Exec.pop (k := k) w r₁; rwa [hr1] at this
      have fr2 : ∀ j, j ≠ w → r₂ j = r j := fun j hj => (StackMachine.set_other _ hj _).trans (fr1 j hj)
      match ht2 : tail2 with
      | [] =>
        have hr2 : r₂ w = [] := by simp [r₂, ht2]
        refine ⟨_, r₂, Exec.branchOne hw (Exec.seq hp1 (Exec.branchOne hr1 (Exec.seq hp2
          (Exec.branchEmpty hr2 (Exec.stop _ _))))), by simp, ?_, fr2⟩
        intro rest h; simp [header3Model] at h
      | false :: tail3 =>
        have hr2 : r₂ w = false :: tail3 := by simp [r₂, ht2]
        refine ⟨_, r₂, Exec.branchOne hw (Exec.seq hp1 (Exec.branchOne hr1 (Exec.seq hp2
          (Exec.branchZero hr2 (Exec.stop _ _))))), by simp, ?_, fr2⟩
        intro rest h; simp [header3Model] at h
      | true :: tail3 =>
        have hr2 : r₂ w = true :: tail3 := by simp [r₂, ht2]
        let r₃ := set r₂ w tail3
        have hp3 : Exec (.pop w) r₂ 2 (true, r₃) := by
          have := Exec.pop (k := k) w r₂; rwa [hr2] at this
        have fr3 : ∀ j, j ≠ w → r₃ j = r j :=
          fun j hj => (StackMachine.set_other _ hj _).trans (fr2 j hj)
        have hr3 : r₃ w = tail3 := by simp [r₃]
        match ht3 : tail3 with
        | [] =>
          refine ⟨_, r₃, Exec.branchOne hw (Exec.seq hp1 (Exec.branchOne hr1 (Exec.seq hp2
            (Exec.branchOne hr2 (Exec.seq hp3 (Exec.branchEmpty hr3 (Exec.stop _ _))))))),
            by simp, ?_, fr3⟩
          intro rest h; simp [header3Model] at h
        | true :: tail4 =>
          refine ⟨_, r₃, Exec.branchOne hw (Exec.seq hp1 (Exec.branchOne hr1 (Exec.seq hp2
            (Exec.branchOne hr2 (Exec.seq hp3 (Exec.branchOne hr3 (Exec.stop _ _))))))),
            by simp, ?_, fr3⟩
          intro rest h; simp [header3Model] at h
        | false :: tail4 =>
          have hp4 : Exec (.pop w) r₃ 2 (true, set r₃ w tail4) := by
            have := Exec.pop (k := k) w r₃; rwa [hr3] at this
          refine ⟨_, set r₃ w tail4, Exec.branchOne hw (Exec.seq hp1 (Exec.branchOne hr1
            (Exec.seq hp2 (Exec.branchOne hr2 (Exec.seq hp3 (Exec.branchZero hr3 hp4)))))),
            by simp, ?_, ?_⟩
          · intro rest h
            simp [header3Model] at h
            simp [h]
          · intro j hj
            exact (StackMachine.set_other _ hj _).trans (fr3 j hj)

end Complexity.Restricted
