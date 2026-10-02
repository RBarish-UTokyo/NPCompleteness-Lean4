module

public import Complexity.Restricted.LeExtract
public import Complexity.Restricted.Counting
import Lean.Elab.Tactic.Omega

/-!
# Counting repeated literals on a stack

`pass2` reads the literal codes on register `rL` one at a time; for each literal it scans the
remaining codes and fails if the same literal occurs again (for a positive literal) or occurs
twice more (for a negative literal). It accepts exactly when every positive literal occurs at
most once and every negative literal at most twice in the list, within a cubic number of
instructions.
-/

@[expose] public section

namespace Complexity.Restricted

open StackTableauProgram (Command Exec)
open StackMachine (Registers set)
open Complexity.SAT

/-! ### Comparing one literal -/

def onMatch : Bool → Command 23
  | true => .stop false
  | false => .branch rF (.push rF true) (.stop false) (.stop false)

def matchStep (s s' : Bool) : Command 23 :=
  if s = s' then .ifThenElse (eqU rA rB rT1 rT2 rS) (onMatch s) (.stop true) else .stop true

def flagReg (flag : Bool) : Word := if flag then [true] else []

/-- `none`: the scan fails; `some flag'`: the scan continues with the flag `flag'`. -/
def matchModel (s s' : Bool) (a b : Nat) (flag : Bool) : Option Bool :=
  if s = s' ∧ a = b then (if s then none else if flag then none else some true) else some flag

theorem matchStep_spec (s s' : Bool) (a b : Nat) (flag : Bool) (r : Regs)
    (hA : r rA = List.replicate a true) (hB : r rB = List.replicate b true)
    (hT1 : r rT1 = []) (hT2 : r rT2 = []) (hS : r rS = []) (hF : r rF = flagReg flag) :
    ∃ t r', Exec (matchStep s s') r t ((matchModel s s' a b flag).isSome, r') ∧
      t ≤ 10 * (a + b) + 34 ∧
      ∀ flag', matchModel s s' a b flag = some flag' →
        r' rF = flagReg flag' ∧ ∀ j, j ≠ rF → r' j = r j := by
  by_cases hs : s = s'
  · subst hs
    have hm : matchStep s s = .ifThenElse (eqU rA rB rT1 rT2 rS) (onMatch s) (.stop true) := by
      simp [matchStep]
    rw [hm]
    obtain ⟨t0, r0, e0, ht0, hr0⟩ := eqU_spec rA rB rT1 rT2 rS (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) r
      hT1 hT2 hS
    rw [hr0, hA, hB] at e0
    simp only [List.length_replicate] at e0 ht0
    rw [hA, hB] at ht0
    simp only [List.length_replicate] at ht0
    by_cases hab : a = b
    · rw [show decide (a = b) = true by simp [hab]] at e0
      cases s with
      | true =>
        refine ⟨t0 + 1, r, ?_, by omega, ?_⟩
        · have : matchModel true true a b flag = none := by simp [matchModel, hab]
          rw [this]
          exact Exec.ifTrue e0 (Exec.stop false r)
        · intro flag' h; simp [matchModel, hab] at h
      | false =>
        cases flag with
        | false =>
          have hF' : r rF = [] := by simpa [flagReg] using hF
          refine ⟨t0 + (2 + 1), set r rF [true], ?_, by omega, ?_⟩
          · have : matchModel false false a b false = some true := by simp [matchModel, hab]
            rw [this]
            have hp := Exec.push (k := 23) rF true r
            rw [hF'] at hp
            exact Exec.ifTrue e0 (Exec.branchEmpty hF' hp)
          · intro flag' h
            simp [matchModel, hab] at h
            subst h
            refine ⟨by simp [flagReg], fun j hj => StackMachine.set_other _ hj _⟩
        | true =>
          have hF' : r rF = true :: [] := by simpa [flagReg] using hF
          refine ⟨t0 + (1 + 1), r, ?_, by omega, ?_⟩
          · have : matchModel false false a b true = none := by simp [matchModel, hab]
            rw [this]
            exact Exec.ifTrue e0 (Exec.branchOne hF' (Exec.stop false r))
          · intro flag' h; simp [matchModel, hab] at h
    · rw [show decide (a = b) = false by simp [hab]] at e0
      refine ⟨t0 + 1, r, ?_, by omega, ?_⟩
      · have : matchModel s s a b flag = some flag := by simp [matchModel, hab]
        rw [this]
        exact Exec.ifFalse e0 (Exec.stop true r)
      · intro flag' h
        simp [matchModel, hab] at h
        subst h
        exact ⟨hF, fun _ _ => rfl⟩
  · have hm : matchStep s s' = .stop true := by simp [matchStep, hs]
    rw [hm]
    refine ⟨1, r, ?_, by omega, ?_⟩
    · have : matchModel s s' a b flag = some flag := by simp [matchModel, hs]
      rw [this]
      exact Exec.stop true r
    · intro flag' h
      simp [matchModel, hs] at h
      subst h
      exact ⟨hF, fun _ _ => rfl⟩

/-! ### Scanning the remaining literals -/

def litStep (s s' : Bool) : Command 23 :=
  .seq (.pop rL2) (.seq (readUnaryC rL2 rB rG) (.seq (matchStep s s')
    (.seq (.clear rB) (.push rG3 true))))

def scanBody (s : Bool) : Command 23 :=
  .branch rL2 (.stop true) (litStep s false) (litStep s true)

def scan (s : Bool) : Command 23 := .seq (.push rG3 true) (.repeat rG3 (scanBody s))

def scanModel (s : Bool) (a : Nat) : Bool → List Literal → Bool
  | _, [] => true
  | flag, l :: ls =>
    match matchModel s l.positive a l.var flag with
    | none => false
    | some flag' => scanModel s a flag' ls

theorem scanBody_writes (s : Bool) : ∀ j : Fin 24, j ∉ [rL2, rB, rG, rG3, rF, rT1, rT2] →
    writes (scanBody s) j = false := by
  cases s <;> decide

/-- The registers of the scan loop, apart from the literal codes, the variable and the flag. -/
structure ScanRegs (r : Regs) : Prop where
  b : r rB = []
  t1 : r rT1 = []
  t2 : r rT2 = []
  s : r rS = []
  g : r rG = []

theorem litStep_spec (s s' : Bool) (a v n : Nat) (flag : Bool) (b : Bool) (rest : Word)
    (r : Regs) (hL2 : r rL2 = b :: (writeNat v ++ rest)) (hG3 : r rG3 = [])
    (hA : r rA = List.replicate a true) (ha : a ≤ n) (hlen : v + 1 + rest.length ≤ n)
    (hr : ScanRegs r) (hF : r rF = flagReg flag) :
    ∃ t r', Exec (litStep s s') r t ((matchModel s s' a v flag).isSome, r') ∧
      t ≤ 40 * n + 58 ∧
      ∀ flag', matchModel s s' a v flag = some flag' →
        r' rL2 = rest ∧ r' rG3 = [true] ∧ r' rA = List.replicate a true ∧ ScanRegs r' ∧
          r' rF = flagReg flag' := by
  let r₁ := set r rL2 (writeNat v ++ rest)
  have e1 : Exec (.pop rL2) r 2 (true, r₁) := by
    have := Exec.pop (k := 23) rL2 r; rwa [hL2] at this
  obtain ⟨t2, r₂, e2, ht2, h2l, h2b, h2g, fr2⟩ := readUnaryC_spec rL2 rB rG (by decide)
    (by decide) (by decide) r₁ (by simp +decide [r₁, hr.g])
  have e1l : r₁ rL2 = writeNat v ++ rest := by simp [r₁]
  have e1b : r₁ rB = [] := by simp +decide [r₁, hr.b]
  rw [e1l, e1b, unaryModel_writeNat] at e2 h2l h2b
  rw [e1l] at ht2
  simp only [List.append_nil] at h2l h2b
  have f2 : ∀ j : Fin 24, j ≠ rL2 → j ≠ rB → j ≠ rG → r₂ j = r j := by
    intro j h1 h2 h3
    rw [fr2 j h1 h2 h3]
    simp [r₁, StackMachine.set_other _ h1]
  obtain ⟨t3, r₃, e3, ht3, h3⟩ := matchStep_spec s s' a v flag r₂
    (by rw [f2 rA (by decide) (by decide) (by decide)]; exact hA) h2b
    (by rw [f2 rT1 (by decide) (by decide) (by decide)]; exact hr.t1)
    (by rw [f2 rT2 (by decide) (by decide) (by decide)]; exact hr.t2)
    (by rw [f2 rS (by decide) (by decide) (by decide)]; exact hr.s)
    (by rw [f2 rF (by decide) (by decide) (by decide)]; exact hF)
  simp only [List.length_append, SATBounds.writeNat_length] at ht2
  cases hm : matchModel s s' a v flag with
  | none =>
    rw [hm] at e3
    refine ⟨2 + (t2 + t3), r₃, ?_, by omega, ?_⟩
    · exact Exec.seq e1 (Exec.seq e2 (Exec.seqFailure (second :=
        Command.seq (.clear rB) (.push rG3 true)) e3))
    · intro flag' h; simp at h
  | some flag' =>
    rw [hm] at e3
    obtain ⟨h3f, f3⟩ := h3 flag' hm
    let r₄ := set r₃ rB []
    have e4 : Exec (.clear rB) r₃ (v + 2) (true, r₄) := by
      have := Exec.clear (k := 23) rB r₃
      rwa [f3 rB (by decide), h2b, List.length_replicate] at this
    have g3 : r₄ rG3 = [] := by
      simp only [r₄]
      rw [StackMachine.set_other _ (by decide), f3 rG3 (by decide),
        f2 rG3 (by decide) (by decide) (by decide), hG3]
    let r₅ := set r₄ rG3 [true]
    have e5 : Exec (.push rG3 true) r₄ 2 (true, r₅) := by
      have := Exec.push (k := 23) rG3 true r₄; rwa [g3] at this
    have f5 : ∀ j : Fin 24, j ≠ rL2 → j ≠ rB → j ≠ rG → j ≠ rG3 → j ≠ rF → r₅ j = r j := by
      intro j h1 h2 h3 h4 h5
      simp only [r₅, r₄]
      rw [StackMachine.set_other _ h4, StackMachine.set_other _ h2, f3 j h5, f2 j h1 h2 h3]
    refine ⟨2 + (t2 + (t3 + (v + 2 + 2))), r₅, ?_, by omega, ?_⟩
    · exact Exec.seq e1 (Exec.seq e2 (Exec.seq e3 (Exec.seq e4 e5)))
    · intro flag'' h
      simp only [Option.some.injEq] at h
      subst h
      refine ⟨?_, by simp [r₅], ?_, ⟨by simp +decide [r₅, r₄], ?_, ?_, ?_, ?_⟩, ?_⟩
      · simp only [r₅, r₄]
        rw [StackMachine.set_other _ (by decide), StackMachine.set_other _ (by decide),
          f3 rL2 (by decide), h2l]
      · rw [f5 rA (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hA
      · rw [f5 rT1 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hr.t1
      · rw [f5 rT2 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hr.t2
      · rw [f5 rS (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hr.s
      · simp only [r₅, r₄]
        rw [StackMachine.set_other _ (by decide), StackMachine.set_other _ (by decide),
          f3 rG (by decide), h2g]
      · simp only [r₅, r₄]
        rw [StackMachine.set_other _ (by decide), StackMachine.set_other _ (by decide), h3f]

theorem scanLoop_spec (s : Bool) (a n : Nat) : ∀ (ls : List Literal) (flag : Bool) (r : Regs),
    r rL2 = writeValues encodeLiteral ls → r rG3 = [true] → r rA = List.replicate a true →
    a ≤ n → (r rL2).length ≤ n → ScanRegs r → r rF = flagReg flag →
    ∃ t r', Exec (.repeat rG3 (scanBody s)) r t (scanModel s a flag ls, r') ∧
      t ≤ ls.length * (40 * n + 60) + 5 ∧
      (scanModel s a flag ls = true →
        (r' rF).length ≤ 1 ∧ r' rL2 = [] ∧ r' rG3 = [] ∧ ScanRegs r' ∧
          r' rA = List.replicate a true) := by
  intro ls
  induction ls with
  | nil =>
    intro flag r hL2 hG3 hA _ _ hr hF
    let r₀ := set r rG3 []
    have hb : Exec (scanBody s) r₀ 2 (true, r₀) :=
      Exec.branchEmpty (by simp +decide [r₀, hL2, writeValues]) (Exec.stop _ _)
    have hd : Exec (.repeat rG3 (scanBody s)) r₀ 2 (true, r₀) :=
      Exec.repeatDone (by simp [r₀])
    refine ⟨2 + 2 + 1, r₀, Exec.repeatNext hG3 hb hd, by simp, ?_⟩
    intro _
    refine ⟨?_, by simp +decide [r₀, hL2, writeValues], by simp [r₀],
      ⟨by simp +decide [r₀, hr.b], by simp +decide [r₀, hr.t1], by simp +decide [r₀, hr.t2],
        by simp +decide [r₀, hr.s], by simp +decide [r₀, hr.g]⟩, by simp +decide [r₀, hA]⟩
    simp +decide [r₀, hF, flagReg]
    cases flag <;> simp
  | cons l ls ih =>
    intro flag r hL2 hG3 hA ha hn hr hF
    let r₀ := set r rG3 []
    have hL2' : r₀ rL2 = l.positive :: (writeNat l.var ++ writeValues encodeLiteral ls) := by
      simp +decide [r₀, hL2, writeValues, encodeLiteral]
    have hlen : l.var + 1 + (writeValues encodeLiteral ls).length ≤ n := by
      rw [hL2] at hn
      simp only [writeValues, List.length_append, SATBounds.encodeLiteral_length] at hn
      omega
    obtain ⟨t1, r₁, e1, ht1, h1⟩ := litStep_spec s l.positive a l.var n flag l.positive
      (writeValues encodeLiteral ls) r₀ hL2' (by simp [r₀]) (by simp +decide [r₀, hA]) ha hlen
      ⟨by simp +decide [r₀, hr.b], by simp +decide [r₀, hr.t1], by simp +decide [r₀, hr.t2],
        by simp +decide [r₀, hr.s], by simp +decide [r₀, hr.g]⟩ (by simp +decide [r₀, hF])
    have hbody : ∀ {res : Bool × Regs} {t : Nat}, Exec (litStep s l.positive) r₀ t res →
        Exec (scanBody s) r₀ (t + 1) res := by
      intro res t h
      cases hp : l.positive
      · rw [hp] at hL2' h
        exact Exec.branchZero hL2' h
      · rw [hp] at hL2' h
        exact Exec.branchOne hL2' h
    have hls : ls.length * 2 ≤ n := by
      have := writeValues_length_le_two ls
      omega
    cases hm : matchModel s l.positive a l.var flag with
    | none =>
      rw [hm] at e1
      refine ⟨t1 + 1 + 1, r₁, ?_, ?_, ?_⟩
      · have : scanModel s a flag (l :: ls) = false := by simp [scanModel, hm]
        rw [this]
        exact Exec.repeatFailure hG3 (hbody e1)
      · simp only [List.length_cons, Nat.add_mul, Nat.one_mul]; omega
      · intro h; simp [scanModel, hm] at h
    | some flag' =>
      rw [hm] at e1
      obtain ⟨g1, g2, g3, g4, g5⟩ := h1 flag' hm
      obtain ⟨t2, r₂, e2, ht2, h2⟩ := ih flag' r₁ g1 g2 g3 ha
        (by rw [g1]; omega) g4 g5
      have hsm : scanModel s a flag (l :: ls) = scanModel s a flag' ls := by
        simp [scanModel, hm]
      refine ⟨t1 + 1 + t2 + 1, r₂, ?_, ?_, ?_⟩
      · rw [hsm]
        exact Exec.repeatNext hG3 (hbody e1) e2
      · simp only [List.length_cons, Nat.add_mul, Nat.one_mul]; omega
      · rw [hsm]; exact h2



/-! ### The outer loop -/

def outerStep (s : Bool) : Command 23 :=
  .seq (.pop rL) (.seq (readUnaryC rL rA rG) (.seq (.copy rL rL2 rS) (.seq (scan s)
    (.seq (.clear rF) (.seq (.clear rA) (.push rG2 true))))))

def outerBody : Command 23 := .branch rL (.stop true) (outerStep false) (outerStep true)

def outerModel : List Literal → Bool
  | [] => true
  | l :: ls => scanModel l.positive l.var false ls && outerModel ls

theorem scan_writes (s : Bool) : ∀ j : Fin 24, j ∉ [rL2, rB, rG, rG3, rF, rT1, rT2] →
    writes (scan s) j = false := by
  cases s <;> decide

/-- The work registers of the outer loop are empty. -/
structure PRegs (r : Regs) : Prop where
  a : r rA = []
  sr : ScanRegs r
  f : r rF = []
  l2 : r rL2 = []
  g3 : r rG3 = []

theorem outerStep_spec (n : Nat) (l : Literal) (ls : List Literal) (r : Regs)
    (hL : r rL = l.positive :: (writeNat l.var ++ writeValues encodeLiteral ls))
    (hn : (r rL).length ≤ n) (hG2 : r rG2 = []) (hp : PRegs r) :
    ∃ t r', Exec (outerStep l.positive) r t (scanModel l.positive l.var false ls, r') ∧
      t ≤ 80 * (n + 1) ^ 2 - 2 ∧
      (scanModel l.positive l.var false ls = true →
        r' rL = writeValues encodeLiteral ls ∧ r' rG2 = [true] ∧ PRegs r') := by
  have hlen : l.var + 1 + (writeValues encodeLiteral ls).length + 1 ≤ n := by
    rw [hL] at hn
    simp only [List.length_cons, List.length_append, SATBounds.writeNat_length] at hn
    omega
  have hls : ls.length * 2 ≤ n := by
    have := writeValues_length_le_two ls
    omega
  let r₁ := set r rL (writeNat l.var ++ (writeValues encodeLiteral ls))
  have e1 : Exec (.pop rL) r 2 (true, r₁) := by
    have := Exec.pop (k := 23) rL r; rwa [hL] at this
  obtain ⟨t2, r₂, e2, ht2, h2l, h2a, h2g, fr2⟩ := readUnaryC_spec rL rA rG (by decide)
    (by decide) (by decide) r₁ (by simp +decide [r₁, hp.sr.g])
  have e1l : r₁ rL = writeNat l.var ++ (writeValues encodeLiteral ls) := by simp [r₁]
  have e1a : r₁ rA = [] := by simp +decide [r₁, hp.a]
  rw [e1l, e1a, unaryModel_writeNat] at e2 h2l h2a
  rw [e1l] at ht2
  simp only [List.append_nil] at h2l h2a
  simp only [List.length_append, SATBounds.writeNat_length] at ht2
  have f2 : ∀ j : Fin 24, j ≠ rL → j ≠ rA → j ≠ rG → r₂ j = r j := by
    intro j h1 h2 h3
    rw [fr2 j h1 h2 h3]
    simp [r₁, StackMachine.set_other _ h1]
  let r₃ := set r₂ rL2 (writeValues encodeLiteral ls)
  have e3 : Exec (.copy rL rL2 rS) r₂ (0 + 5 * (writeValues encodeLiteral ls).length + 6) (true, r₃) := by
    have := Exec.copy (k := 23) (r := r₂) (src := rL) (dst := rL2) (scratch := rS)
      (by decide) (by decide) (by decide)
      (by rw [f2 rS (by decide) (by decide) (by decide)]; exact hp.sr.s)
    rwa [f2 rL2 (by decide) (by decide) (by decide), hp.l2, h2l] at this
  have f3 : ∀ j : Fin 24, j ≠ rL → j ≠ rA → j ≠ rG → j ≠ rL2 → r₃ j = r j := by
    intro j h1 h2 h3 h4
    simp only [r₃]
    rw [StackMachine.set_other _ h4, f2 j h1 h2 h3]
  let r₄ := set r₃ rG3 [true]
  have e4 : Exec (.push rG3 true) r₃ 2 (true, r₄) := by
    have := Exec.push (k := 23) rG3 true r₃
    rwa [f3 rG3 (by decide) (by decide) (by decide) (by decide), hp.g3] at this
  have f4 : ∀ j : Fin 24, j ≠ rL → j ≠ rA → j ≠ rG → j ≠ rL2 → j ≠ rG3 → r₄ j = r j := by
    intro j h1 h2 h3 h4 h5
    simp only [r₄]
    rw [StackMachine.set_other _ h5, f3 j h1 h2 h3 h4]
  obtain ⟨t5, r₅, e5, ht5, h5⟩ := scanLoop_spec l.positive l.var n ls false r₄
    (by simp +decide [r₄, r₃]) (by simp [r₄])
    (by simp only [r₄, r₃]; rw [StackMachine.set_other _ (by decide),
      StackMachine.set_other _ (by decide), h2a])
    (by omega) (by simp +decide [r₄, r₃]; omega)
    ⟨by rw [f4 rB (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hp.sr.b,
      by rw [f4 rT1 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hp.sr.t1,
      by rw [f4 rT2 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hp.sr.t2,
      by rw [f4 rS (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hp.sr.s,
      by simp only [r₄, r₃]; rw [StackMachine.set_other _ (by decide),
        StackMachine.set_other _ (by decide), h2g]⟩
    (by rw [f4 rF (by decide) (by decide) (by decide) (by decide) (by decide), hp.f]; rfl)
  have escan : Exec (scan l.positive) r₃ (2 + t5) (scanModel l.positive l.var false ls, r₅) :=
    Exec.seq e4 e5
  have hmul := Nat.mul_le_mul_right (40 * n + 60) (show ls.length ≤ n by omega)
  have hsq : (n + 1) ^ 2 = n * n + 2 * n + 1 := by
    rw [Nat.pow_two]; simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one, Nat.one_mul]; omega
  have hmul' : n * (40 * n + 60) = 40 * (n * n) + 60 * n := by
    simp only [Nat.mul_add, Nat.mul_left_comm n 40 n, Nat.mul_comm n 60]
  cases hs : scanModel l.positive l.var false ls with
  | false =>
    rw [hs] at escan
    refine ⟨2 + (t2 + ((0 + 5 * (writeValues encodeLiteral ls).length + 6) + (2 + t5))), r₅, ?_, ?_, ?_⟩
    · exact Exec.seq e1 (Exec.seq e2 (Exec.seq e3 (Exec.seqFailure (second :=
        Command.seq (.clear rF) (.seq (.clear rA) (.push rG2 true))) escan)))
    · rw [hsq]; omega
    · intro h; cases h
  | true =>
    rw [hs] at escan
    obtain ⟨g1, g2, g3, g4, g5⟩ := h5 hs
    have fr5 : ∀ j : Fin 24, j ∉ [rL2, rB, rG, rG3, rF, rT1, rT2] → r₅ j = r₃ j :=
      fun j hj => exec_frame' escan j (scan_writes l.positive j hj)
    let r₆ := set r₅ rF []
    have e6 : Exec (.clear rF) r₅ ((r₅ rF).length + 2) (true, r₆) := Exec.clear rF r₅
    let r₇ := set r₆ rA []
    have e7 : Exec (.clear rA) r₆ (l.var + 2) (true, r₇) := by
      have := Exec.clear (k := 23) rA r₆
      rwa [show r₆ rA = List.replicate l.var true by simp +decide [r₆, g5],
        List.length_replicate] at this
    have g7 : r₇ rG2 = [] := by
      simp only [r₇, r₆]
      rw [StackMachine.set_other _ (by decide), StackMachine.set_other _ (by decide),
        fr5 rG2 (by decide), f3 rG2 (by decide) (by decide) (by decide) (by decide), hG2]
    let r₈ := set r₇ rG2 [true]
    have e8 : Exec (.push rG2 true) r₇ 2 (true, r₈) := by
      have := Exec.push (k := 23) rG2 true r₇; rwa [g7] at this
    refine ⟨2 + (t2 + ((0 + 5 * (writeValues encodeLiteral ls).length + 6) + ((2 + t5) +
      ((r₅ rF).length + 2 + (l.var + 2 + 2))))), r₈, ?_, ?_, ?_⟩
    · exact Exec.seq e1 (Exec.seq e2 (Exec.seq e3 (Exec.seq escan (Exec.seq e6
        (Exec.seq e7 e8)))))
    · rw [hsq]; omega
    · intro _
      refine ⟨?_, by simp [r₈], ⟨by simp +decide [r₈, r₇], ⟨?_, ?_, ?_, ?_, ?_⟩,
        by simp +decide [r₈, r₇, r₆], ?_, ?_⟩⟩
      · simp only [r₈, r₇, r₆]
        rw [StackMachine.set_other _ (by decide), StackMachine.set_other _ (by decide),
          StackMachine.set_other _ (by decide), fr5 rL (by decide)]
        simp only [r₃]
        rw [StackMachine.set_other _ (by decide), h2l]
      all_goals simp only [r₈, r₇, r₆]
      all_goals rw [StackMachine.set_other _ (by decide), StackMachine.set_other _ (by decide),
          StackMachine.set_other _ (by decide)]
      · exact g4.b
      · exact g4.t1
      · exact g4.t2
      · exact g4.s
      · exact g4.g
      · exact g2
      · exact g3

theorem outerLoop_spec (n : Nat) : ∀ (lits : List Literal) (r : Regs),
    r rL = writeValues encodeLiteral lits → (r rL).length ≤ n → r rG2 = [true] → PRegs r →
    ∃ t r', Exec (.repeat rG2 outerBody) r t (outerModel lits, r') ∧
      t ≤ lits.length * (80 * (n + 1) ^ 2) + 5 := by
  intro lits
  induction lits with
  | nil =>
    intro r hL _ hG2 _
    let r₀ := set r rG2 []
    have hb : Exec outerBody r₀ 2 (true, r₀) :=
      Exec.branchEmpty (by simp +decide [r₀, hL, writeValues]) (Exec.stop _ _)
    exact ⟨2 + 2 + 1, r₀, Exec.repeatNext hG2 hb (Exec.repeatDone (by simp [r₀])), by simp⟩
  | cons l ls ih =>
    intro r hL hn hG2 hp
    let r₀ := set r rG2 []
    have hL0 : r₀ rL = l.positive :: (writeNat l.var ++ writeValues encodeLiteral ls) := by
      simp +decide [r₀, hL, writeValues, encodeLiteral]
    have hn0 : (r₀ rL).length ≤ n := by simp +decide [r₀]; exact hn
    obtain ⟨t1, r₁, e1, ht1, h1⟩ := outerStep_spec n l ls r₀ hL0 hn0 (by simp [r₀])
      ⟨by simp +decide [r₀, hp.a], ⟨by simp +decide [r₀, hp.sr.b], by simp +decide [r₀, hp.sr.t1],
        by simp +decide [r₀, hp.sr.t2], by simp +decide [r₀, hp.sr.s],
        by simp +decide [r₀, hp.sr.g]⟩, by simp +decide [r₀, hp.f],
        by simp +decide [r₀, hp.l2], by simp +decide [r₀, hp.g3]⟩
    have hbody : ∀ {res : Bool × Regs} {t : Nat}, Exec (outerStep l.positive) r₀ t res →
        Exec outerBody r₀ (t + 1) res := by
      intro res t h
      cases hpos : l.positive
      · rw [hpos] at hL0 h
        exact Exec.branchZero hL0 h
      · rw [hpos] at hL0 h
        exact Exec.branchOne hL0 h
    have hpos2 : 2 ≤ 80 * (n + 1) ^ 2 := by
      have : 1 ≤ (n + 1) ^ 2 := Nat.pow_pos (by omega)
      omega
    cases hs : scanModel l.positive l.var false ls with
    | false =>
      rw [hs] at e1
      refine ⟨t1 + 1 + 1, r₁, ?_, ?_⟩
      · have : outerModel (l :: ls) = false := by simp [outerModel, hs]
        rw [this]
        exact Exec.repeatFailure hG2 (hbody e1)
      · simp only [List.length_cons, Nat.add_mul, Nat.one_mul]; omega
    | true =>
      rw [hs] at e1
      obtain ⟨g1, g2, g3⟩ := h1 hs
      have hls : (r₁ rL).length ≤ n := by
        rw [g1]
        rw [hL] at hn
        simp only [writeValues, List.length_append] at hn
        omega
      obtain ⟨t2, r₂, e2, ht2⟩ := ih r₁ g1 hls g2 g3
      refine ⟨t1 + 1 + t2 + 1, r₂, ?_, ?_⟩
      · have : outerModel (l :: ls) = outerModel ls := by simp [outerModel, hs]
        rw [this]
        exact Exec.repeatNext hG2 (hbody e1) e2
      · simp only [List.length_cons, Nat.add_mul, Nat.one_mul]; omega

end Complexity.Restricted
