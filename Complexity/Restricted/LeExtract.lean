module

public import Complexity.Restricted.ExactCheck
public import Complexity.StackParse
public import Complexity.SATBounds
import Lean.Elab.Tactic.Omega

/-!
# Extracting the literals of an encoded formula

`pass1` copies the input word into a work register and parses it as a formula whose clauses
have two or three literals, moving the code of every literal onto register `rL` (in reverse
order). On every word it halts within a cubic number of instructions; on success `rL`
contains the codes of a list of literals, which for `encode f` is the reversed list of all
literal occurrences of `f`.
-/

@[expose] public section

namespace Complexity.Restricted

open StackTableauProgram (Command Exec)
open StackMachine (Registers set)
open Complexity.SAT

abbrev rL : Fin 24 := 16
abbrev rL2 : Fin 24 := 17
abbrev rR : Fin 24 := 18
abbrev rF : Fin 24 := 19
abbrev rG2 : Fin 24 := 20
abbrev rG3 : Fin 24 := 21

/-! ### Unary numerals and `readNat` -/

theorem unaryModel_of_readNat {w rest d : Word} {v : Nat} (h : readNat w = some (v, rest)) :
    unaryModel w d = (true, rest, List.replicate v true ++ d) := by
  rw [readNat_eq_some h, unaryModel_writeNat]

theorem unaryModel_of_readNat_none : ∀ {w : Word} (d : Word), readNat w = none →
    (unaryModel w d).1 = false
  | [], _, _ => rfl
  | false :: _, _, h => by simp [readNat] at h
  | true :: rest, d, h => by
    have : readNat rest = none := by
      cases hr : readNat rest with
      | none => rfl
      | some p => obtain ⟨n, t⟩ := p; simp [readNat, hr] at h
    simp only [unaryModel]
    exact unaryModel_of_readNat_none (true :: d) this

theorem writeValues_length_le_two (ls : List Literal) :
    2 * ls.length ≤ (writeValues encodeLiteral ls).length := by
  induction ls with
  | nil => simp [writeValues]
  | cons l ls ih =>
    simp only [writeValues, List.length_append, SATBounds.encodeLiteral_length, List.length_cons]
    omega

/-! ### Moving one literal -/

def moveLit : Command 23 :=
  .branch rW (.stop false)
    (.seq (.pop rW) (.seq (readUnaryC rW rA rG) (.seq (.push rL false)
      (.seq (.add rA rL rS) (.seq (.push rL false) (.clear rA))))))
    (.seq (.pop rW) (.seq (readUnaryC rW rA rG) (.seq (.push rL false)
      (.seq (.add rA rL rS) (.seq (.push rL true) (.clear rA))))))

theorem exec_frame' {c : Command 23} {r : Regs} {t : Nat} {b : Bool} {r' : Regs}
    (h : Exec c r t (b, r')) : ∀ i, writes c i = false → r' i = r i :=
  exec_frame h

theorem moveLit_writes : ∀ j : Fin 24, j ∉ [rW, rL, rA, rG] →
    writes moveLit j = false := by decide

theorem moveLit_spec (r : Regs) (hA : r rA = []) (hG : r rG = []) (hS : r rS = []) :
    ∃ t r', Exec moveLit r t ((readLiteral (r rW)).isSome, r') ∧ t ≤ 15 * (r rW).length + 30 ∧
      ∀ l rest, readLiteral (r rW) = some (l, rest) →
        r' rW = rest ∧ r' rL = encodeLiteral l ++ r rL ∧ r' rA = [] ∧ r' rG = [] := by
  cases hw : r rW with
  | nil =>
    refine ⟨2, r, Exec.branchEmpty hw (Exec.stop _ _), by omega, ?_⟩
    intro l rest h; simp [readLiteral] at h
  | cons s rest =>
    let r₁ := set r rW rest
    have hp : Exec (.pop rW) r 2 (true, r₁) := by
      have := Exec.pop (k := 23) rW r; rwa [hw] at this
    obtain ⟨t2, r₂, e2, ht2, h2w, h2a, h2g, fr2⟩ := readUnaryC_spec rW rA rG (by decide)
      (by decide) (by decide) r₁ (by simp +decide [r₁, hG])
    have e1w : r₁ rW = rest := by simp [r₁]
    have e1a : r₁ rA = [] := by simp +decide [r₁, hA]
    rw [e1w, e1a] at e2 h2w h2a
    rw [e1w] at ht2
    cases hn : readNat rest with
    | none =>
      have hf := unaryModel_of_readNat_none [] hn
      rw [hf] at e2
      have hlit : readLiteral (s :: rest) = none := by simp [readLiteral, hn]
      refine ⟨2 + t2 + 1, r₂, ?_, by simp; omega, ?_⟩
      · rw [hlit]
        cases s
        · exact Exec.branchZero hw (Exec.seq hp (Exec.seqFailure e2))
        · exact Exec.branchOne hw (Exec.seq hp (Exec.seqFailure e2))
      · intro l rest' h; rw [hlit] at h; simp at h
    | some p =>
      obtain ⟨v, tail⟩ := p
      have hu := unaryModel_of_readNat (d := []) hn
      rw [hu] at e2 h2w h2a
      simp only [List.append_nil] at h2w h2a
      have hlit : readLiteral (s :: rest) = some (⟨v, s⟩, tail) := by simp [readLiteral, hn]
      have hv : v ≤ rest.length := by
        have := congrArg List.length (readNat_eq_some hn)
        simp only [List.length_append, SATBounds.writeNat_length] at this
        omega
      have hS2 : r₂ rS = [] := by
        rw [fr2 rS (by decide) (by decide) (by decide)]; simp +decide [r₁, hS]
      have hL2 : r₂ rL = r rL := by
        rw [fr2 rL (by decide) (by decide) (by decide)]; simp +decide [r₁]
      let r₃ := set r₂ rL (false :: r rL)
      have e3 : Exec (.push rL false) r₂ 2 (true, r₃) := by
        have := Exec.push (k := 23) rL false r₂; rwa [hL2] at this
      let r₄ := set r₃ rL (List.replicate v true ++ false :: r rL)
      have e4 : Exec (.add rA rL rS) r₃ (5 * v + 4) (true, r₄) := by
        have := Exec.add (k := 23) (r := r₃) (src := rA) (dst := rL) (scratch := rS)
          (by decide) (by decide) (by decide) (by simp +decide [r₃, hS2])
        have ea : r₃ rA = List.replicate v true := by simp +decide [r₃, h2a]
        have el : r₃ rL = false :: r rL := by simp [r₃]
        rw [ea, el, List.length_replicate] at this
        simpa [r₄, r₃] using this
      let r₅ := set r₄ rL (s :: List.replicate v true ++ false :: r rL)
      have e5 : Exec (.push rL s) r₄ 2 (true, r₅) := by
        have := Exec.push (k := 23) rL s r₄
        simpa [r₄, r₅] using this
      let r₆ := set r₅ rA []
      have e6 : Exec (.clear rA) r₅ (v + 2) (true, r₆) := by
        have := Exec.clear (k := 23) rA r₅
        have ea : r₅ rA = List.replicate v true := by simp +decide [r₅, r₄, r₃, h2a]
        rw [ea, List.length_replicate] at this
        exact this
      have hrest : Exec (.seq (.push rL false) (.seq (.add rA rL rS) (.seq (.push rL s)
          (.clear rA)))) r₂ (2 + (5 * v + 4 + (2 + (v + 2)))) (true, r₆) :=
        Exec.seq e3 (Exec.seq e4 (Exec.seq e5 e6))
      refine ⟨2 + (t2 + (2 + (5 * v + 4 + (2 + (v + 2))))) + 1, r₆, ?_, by simp; omega, ?_⟩
      · rw [hlit]
        cases s
        · exact Exec.branchZero hw (Exec.seq hp (Exec.seq e2 hrest))
        · exact Exec.branchOne hw (Exec.seq hp (Exec.seq e2 hrest))
      · intro l rest' h
        rw [hlit] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨?_, ?_, by simp [r₆], ?_⟩
        · simp +decide [r₆, r₅, r₄, r₃, h2w]
        · simp +decide [r₆, r₅, encodeLiteral, StackParse.writeNat_eq]
        · simp +decide [r₆, r₅, r₄, r₃, h2g]



/-! ### Moving the literals of a clause -/

def moveModel : Nat → Word → List Literal → Option (Word × List Literal)
  | 0, w, acc => some (w, acc)
  | n + 1, w, acc =>
    match readLiteral w with
    | none => none
    | some (l, w') => moveModel n w' (l :: acc)

/-- The temporaries of `moveLit` are empty. -/
def MClean (r : Regs) : Prop := r rA = [] ∧ r rG = [] ∧ r rS = []

theorem moveLoop_writes : ∀ j : Fin 24, j ∉ [rW, rL, rA, rG, rR] →
    writes (.repeat rR moveLit) j = false := by decide

theorem moveLoop_spec : ∀ (n : Nat) (acc : List Literal) (r : Regs), (r rR).length = n →
    r rL = writeValues encodeLiteral acc → MClean r →
    ∃ t r', Exec (.repeat rR moveLit) r t ((moveModel n (r rW) acc).isSome, r') ∧
      t ≤ n * (15 * (r rW).length + 31) + 2 ∧
      ∀ w' acc', moveModel n (r rW) acc = some (w', acc') →
        r' rW = w' ∧ r' rL = writeValues encodeLiteral acc' ∧ MClean r' ∧ r' rR = [] ∧
        w'.length + (writeValues encodeLiteral acc').length =
          (r rW).length + (writeValues encodeLiteral acc).length := by
  intro n
  induction n with
  | zero =>
    intro acc r hn hL hc
    refine ⟨2, r, Exec.repeatDone (List.eq_nil_of_length_eq_zero hn), by omega, ?_⟩
    intro w' acc' h
    simp only [moveModel, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, hL, hc, List.eq_nil_of_length_eq_zero hn, rfl⟩
  | succ n ih =>
    intro acc r hn hL hc
    obtain ⟨hA, hG, hS⟩ := hc
    obtain ⟨b, tail, hR⟩ : ∃ b tail, r rR = b :: tail := by
      cases h : r rR with
      | nil => rw [h] at hn; simp at hn
      | cons b tail => exact ⟨b, tail, rfl⟩
    let r₀ := set r rR tail
    obtain ⟨t1, r₁, e1, ht1, h1⟩ := moveLit_spec r₀ (by simp +decide [r₀, hA])
      (by simp +decide [r₀, hG]) (by simp +decide [r₀, hS])
    have e0w : r₀ rW = r rW := by simp +decide [r₀]
    rw [e0w] at e1 ht1 h1
    cases hl : readLiteral (r rW) with
    | none =>
      rw [hl] at e1
      refine ⟨t1 + 1, r₁, ?_, ?_, ?_⟩
      · simpa [moveModel, hl] using Exec.repeatFailure hR e1
      · have h2 : 15 * (r rW).length + 31 ≤ (n + 1) * (15 * (r rW).length + 31) :=
          Nat.le_mul_of_pos_left _ (by omega)
        omega
      · intro w' acc' h
        simp [moveModel, hl] at h
    | some p =>
      obtain ⟨l, w'⟩ := p
      rw [hl] at e1
      obtain ⟨h1w, h1L, h1A, h1G⟩ := h1 l w' hl
      have fr := fun j hj => exec_frame' e1 j (moveLit_writes j hj)
      have h1R : (r₁ rR).length = n := by
        rw [fr rR (by decide)]
        simp [r₀]
        rw [hR] at hn; simpa using hn
      have h1S : r₁ rS = [] := by
        rw [fr rS (by decide)]
        simp +decide [r₀, hS]
      have h1L' : r₁ rL = writeValues encodeLiteral (l :: acc) := by
        rw [h1L, show r₀ rL = r rL by simp +decide [r₀], hL]
        rfl
      have hlen := congrArg List.length (readLiteral_eq_some hl)
      simp only [List.length_append, SATBounds.encodeLiteral_length] at hlen
      obtain ⟨t2, r₂, e2, ht2, h2⟩ := ih (l :: acc) r₁ h1R h1L' ⟨h1A, h1G, h1S⟩
      rw [h1w] at e2 ht2 h2
      refine ⟨t1 + t2 + 1, r₂, ?_, ?_, ?_⟩
      · simpa [moveModel, hl] using Exec.repeatNext hR e1 e2
      · have := Nat.mul_le_mul_left n (show 15 * w'.length + 31 ≤ 15 * (r rW).length + 31 by
          omega)
        rw [Nat.succ_mul]; omega
      · intro w'' acc'' h
        simp only [moveModel, hl] at h
        obtain ⟨g1, g2, g3, g5, g4⟩ := h2 w'' acc'' h
        refine ⟨g1, g2, g3, g5, ?_⟩
        rw [g4]
        simp only [writeValues, List.length_append, SATBounds.encodeLiteral_length]
        omega

/-! ### Clause lengths two or three -/

def len23 (x : Fin 24) : Command 23 :=
  .branch x (.stop false) (.stop false) (.seq (.pop x)
    (.branch x (.stop false) (.stop false) (.seq (.pop x)
      (.branch x (.stop true) (.stop false) (.seq (.pop x)
        (.branch x (.stop true) (.stop false) (.stop false)))))))

theorem len23_spec (x : Fin 24) (r : Regs) (n : Nat) (hx : r x = List.replicate n true) :
    ∃ t r', Exec (len23 x) r t (decide (n = 2 ∨ n = 3), r') ∧ t ≤ 12 ∧
      (n = 2 ∨ n = 3 → r' x = []) := by
  match n, hx with
  | 0, hx =>
    exact ⟨2, r, Exec.branchEmpty hx (Exec.stop _ _), by omega, by simp⟩
  | 1, hx =>
    have h1 : (set r x []) x = [] := by simp
    have p1 : Exec (.pop x) r 2 (true, set r x []) := by
      have := Exec.pop (k := 23) x r; rw [hx] at this; exact this
    exact ⟨_, _, Exec.branchOne hx (Exec.seq p1 (Exec.branchEmpty h1 (Exec.stop _ _))),
      by omega, by simp⟩
  | 2, hx =>
    have p1 : Exec (.pop x) r 2 (true, set r x [true]) := by
      have := Exec.pop (k := 23) x r; rw [hx] at this; exact this
    have h1 : (set r x [true]) x = true :: [] := by simp
    have p2 : Exec (.pop x) (set r x [true]) 2 (true, set (set r x [true]) x []) := by
      have := Exec.pop (k := 23) x (set r x [true]); rw [h1] at this; exact this
    have h2 : (set (set r x [true]) x []) x = [] := by simp
    exact ⟨_, _, Exec.branchOne hx (Exec.seq p1 (Exec.branchOne h1 (Exec.seq p2
      (Exec.branchEmpty h2 (Exec.stop _ _))))), by omega, by simp⟩
  | 3, hx =>
    have p1 : Exec (.pop x) r 2 (true, set r x [true, true]) := by
      have := Exec.pop (k := 23) x r; rw [hx] at this; exact this
    have h1 : (set r x [true, true]) x = true :: [true] := by simp
    have p2 : Exec (.pop x) (set r x [true, true]) 2
        (true, set (set r x [true, true]) x [true]) := by
      have := Exec.pop (k := 23) x (set r x [true, true]); rw [h1] at this; exact this
    have h2 : (set (set r x [true, true]) x [true]) x = true :: [] := by simp
    have p3 : Exec (.pop x) (set (set r x [true, true]) x [true]) 2
        (true, set (set (set r x [true, true]) x [true]) x []) := by
      have := Exec.pop (k := 23) x (set (set r x [true, true]) x [true])
      rw [h2] at this; exact this
    have h3 : (set (set (set r x [true, true]) x [true]) x []) x = [] := by simp
    exact ⟨_, _, Exec.branchOne hx (Exec.seq p1 (Exec.branchOne h1 (Exec.seq p2
      (Exec.branchOne h2 (Exec.seq p3 (Exec.branchEmpty h3 (Exec.stop _ _))))))),
      by omega, by simp⟩
  | n + 4, hx =>
    have hx' : r x = true :: true :: true :: true :: List.replicate n true := by
      rw [hx]; simp [List.replicate_succ]
    have p1 : Exec (.pop x) r 2 (true, set r x (true :: true :: true :: List.replicate n true)) := by
      have := Exec.pop (k := 23) x r; rw [hx'] at this; exact this
    let r₁ := set r x (true :: true :: true :: List.replicate n true)
    have h1 : r₁ x = true :: (true :: true :: List.replicate n true) := by simp [r₁]
    have p2 : Exec (.pop x) r₁ 2 (true, set r₁ x (true :: true :: List.replicate n true)) := by
      have := Exec.pop (k := 23) x r₁; rw [h1] at this; exact this
    let r₂ := set r₁ x (true :: true :: List.replicate n true)
    have h2 : r₂ x = true :: (true :: List.replicate n true) := by simp [r₂]
    have p3 : Exec (.pop x) r₂ 2 (true, set r₂ x (true :: List.replicate n true)) := by
      have := Exec.pop (k := 23) x r₂; rw [h2] at this; exact this
    let r₃ := set r₂ x (true :: List.replicate n true)
    have h3 : r₃ x = true :: List.replicate n true := by simp [r₃]
    have hd : decide (n + 4 = 2 ∨ n + 4 = 3) = false := by simp
    rw [hd]
    exact ⟨_, _, Exec.branchOne hx' (Exec.seq p1 (Exec.branchOne h1 (Exec.seq p2
      (Exec.branchOne h2 (Exec.seq p3 (Exec.branchOne h3 (Exec.stop false r₃))))))), by omega,
      fun h => absurd h (by omega)⟩

/-! ### One clause -/

def clauseLe : Command 23 :=
  .seq (readUnaryC rW rR rG) (.seq (.copy rR rT1 rS) (.seq (len23 rT1) (.repeat rR moveLit)))

def clauseLeModel (w : Word) (acc : List Literal) : Option (Word × List Literal) :=
  match readNat w with
  | none => none
  | some (n, rest) => if n = 2 ∨ n = 3 then moveModel n rest acc else none

/-- The temporaries of `clauseLe` are empty. -/
def CClean (r : Regs) : Prop := r rA = [] ∧ r rG = [] ∧ r rS = [] ∧ r rT1 = [] ∧ r rR = []

theorem clauseLe_writes : ∀ j : Fin 24, j ∉ [rW, rL, rA, rG, rR, rT1] →
    writes clauseLe j = false := by decide

theorem clauseLe_spec (acc : List Literal) (r : Regs) (hL : r rL = writeValues encodeLiteral acc)
    (hc : CClean r) :
    ∃ t r', Exec clauseLe r t ((clauseLeModel (r rW) acc).isSome, r') ∧
      t ≤ 50 * ((r rW).length + 1) ^ 2 ∧
      ∀ w' acc', clauseLeModel (r rW) acc = some (w', acc') →
        r' rW = w' ∧ r' rL = writeValues encodeLiteral acc' ∧ CClean r' ∧
        w'.length + (writeValues encodeLiteral acc').length ≤
          (r rW).length + (writeValues encodeLiteral acc).length := by
  obtain ⟨hA, hG, hS, hT1, hR⟩ := hc
  obtain ⟨t1, r₁, e1, ht1, h1w, h1r, h1g, fr1⟩ := readUnaryC_spec rW rR rG (by decide)
    (by decide) (by decide) r hG
  rw [hR] at e1 h1w h1r
  have hsq : (r rW).length + 1 ≤ ((r rW).length + 1) ^ 2 := Nat.le_self_pow (by decide) _
  cases hn : readNat (r rW) with
  | none =>
    have hf := unaryModel_of_readNat_none [] hn
    rw [hf] at e1
    refine ⟨t1, r₁, ?_, by omega, ?_⟩
    · simpa [clauseLe, clauseLeModel, hn] using Exec.seqFailure (second :=
        Command.seq (.copy rR rT1 rS) (.seq (len23 rT1) (.repeat rR moveLit))) e1
    · intro w' acc' h; simp [clauseLeModel, hn] at h
  | some p =>
    obtain ⟨n, rest⟩ := p
    have hu := unaryModel_of_readNat (d := []) hn
    rw [hu] at e1 h1w h1r
    simp only [List.append_nil] at h1w h1r
    have hlen := congrArg List.length (readNat_eq_some hn)
    simp only [List.length_append, SATBounds.writeNat_length] at hlen
    let r₂ := set r₁ rT1 (List.replicate n true)
    have e2 : Exec (.copy rR rT1 rS) r₁ (0 + 5 * n + 6) (true, r₂) := by
      have := Exec.copy (k := 23) (r := r₁) (src := rR) (dst := rT1) (scratch := rS)
        (by decide) (by decide) (by decide)
        (by rw [fr1 rS (by decide) (by decide) (by decide)]; exact hS)
      rwa [fr1 rT1 (by decide) (by decide) (by decide), hT1, h1r, List.length_replicate] at this
    obtain ⟨t3, r₃, e3, ht3, h3⟩ := len23_spec rT1 r₂ n (by simp [r₂])
    have fr3 : ∀ j : Fin 24, j ≠ rT1 → r₃ j = r₁ j := by
      intro j hj
      rw [exec_frame' e3 j (by revert hj; revert j; decide)]
      simp [r₂, StackMachine.set_other _ hj]
    have hw2 : (r rW).length + 1 ≤ ((r rW).length + 1) ^ 2 := hsq
    by_cases h23 : n = 2 ∨ n = 3
    · rw [show decide (n = 2 ∨ n = 3) = true by simp [h23]] at e3
      have h3t : r₃ rT1 = [] := h3 h23
      have g : ∀ j : Fin 24, j ≠ rT1 → j ≠ rW → j ≠ rR → j ≠ rG → r₃ j = r j := by
        intro j hj1 hj2 hj3 hj4
        rw [fr3 j hj1, fr1 j hj2 hj3 hj4]
      have g3w : r₃ rW = rest := by rw [fr3 rW (by decide), h1w]
      have g3r : r₃ rR = List.replicate n true := by rw [fr3 rR (by decide), h1r]
      have g3g : r₃ rG = [] := by rw [fr3 rG (by decide), h1g]
      obtain ⟨t4, r₄, e4, ht4, h4⟩ := moveLoop_spec n acc r₃ (by rw [g3r]; simp)
        (by rw [g rL (by decide) (by decide) (by decide) (by decide), hL])
        ⟨by rw [g rA (by decide) (by decide) (by decide) (by decide)]; exact hA, g3g,
          by rw [g rS (by decide) (by decide) (by decide) (by decide)]; exact hS⟩
      rw [g3w] at e4 ht4 h4
      have hmodel : clauseLeModel (r rW) acc = moveModel n rest acc := by
        simp [clauseLeModel, hn, h23]
      refine ⟨t1 + ((0 + 5 * n + 6) + (t3 + t4)), r₄, ?_, ?_, ?_⟩
      · rw [hmodel]
        exact Exec.seq e1 (Exec.seq e2 (Exec.seq e3 e4))
      · have h5 := Nat.mul_le_mul (show n ≤ (r rW).length by omega)
          (show 15 * rest.length + 31 ≤ 15 * (r rW).length + 31 by omega)
        generalize (r rW).length = w at *
        have h6 : (w + 1) ^ 2 = w * w + 2 * w + 1 := by
          rw [Nat.pow_two]; simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one, Nat.one_mul]; omega
        have h7 : w * (15 * w + 31) = 15 * (w * w) + 31 * w := by
          simp only [Nat.mul_add, Nat.mul_left_comm w 15 w, Nat.mul_comm w 31]
        rw [h6]
        omega
      · intro w' acc' h
        rw [hmodel] at h
        obtain ⟨k1, k2, ⟨k3, k4, k5⟩, k6, k7⟩ := h4 w' acc' h
        have k8 : r₄ rT1 = [] := by
          rw [exec_frame' e4 rT1 (by decide), h3t]
        refine ⟨k1, k2, ⟨k3, k4, k5, k8, k6⟩, ?_⟩
        omega
    · rw [show decide (n = 2 ∨ n = 3) = false by simp [h23]] at e3
      refine ⟨t1 + ((0 + 5 * n + 6) + t3), r₃, ?_, by omega, ?_⟩
      · have : clauseLeModel (r rW) acc = none := by simp [clauseLeModel, hn, h23]
        rw [this]
        exact Exec.seq e1 (Exec.seq e2 (Exec.seqFailure (second := .repeat rR moveLit) e3))
      · intro w' acc' h
        simp [clauseLeModel, hn, h23] at h



theorem writeValues_append (a b : List Literal) :
    writeValues encodeLiteral (a ++ b) = writeValues encodeLiteral a ++ writeValues encodeLiteral b := by
  induction a with
  | nil => rfl
  | cons l a ih => simp [writeValues, ih, List.append_assoc]

theorem moveModel_acc : ∀ (n : Nat) (w : Word) (acc : List Literal) (w' : Word)
    (acc' : List Literal), moveModel n w acc = some (w', acc') → ∃ ls, acc' = ls ++ acc
  | 0, w, acc, w', acc', h => by
    simp only [moveModel, Option.some.injEq, Prod.mk.injEq] at h
    exact ⟨[], by simp [h.2]⟩
  | n + 1, w, acc, w', acc', h => by
    simp only [moveModel] at h
    cases hl : readLiteral w with
    | none => rw [hl] at h; simp at h
    | some p =>
      obtain ⟨l, w''⟩ := p
      rw [hl] at h
      obtain ⟨ls, hls⟩ := moveModel_acc n w'' (l :: acc) w' acc' h
      exact ⟨ls ++ [l], by simp [hls]⟩

theorem clauseLeModel_acc {w : Word} {acc : List Literal} {w' : Word} {acc' : List Literal}
    (h : clauseLeModel w acc = some (w', acc')) : ∃ ls, acc' = ls ++ acc := by
  unfold clauseLeModel at h
  cases hn : readNat w with
  | none => rw [hn] at h; simp at h
  | some p =>
    obtain ⟨n, rest⟩ := p
    rw [hn] at h
    dsimp only at h
    split at h
    · exact moveModel_acc n rest acc w' acc' h
    · simp at h

/-! ### All clauses -/

def leLoopModel : Nat → Word → List Literal → Option (Word × List Literal)
  | 0, w, acc => some (w, acc)
  | m + 1, w, acc =>
    match clauseLeModel w acc with
    | none => none
    | some (w', acc') => leLoopModel m w' acc'

theorem leLoop_spec (N : Nat) : ∀ (m : Nat) (acc : List Literal) (r : Regs),
    (r rKC).length = m → r rL = writeValues encodeLiteral acc → CClean r → (r rW).length ≤ N →
    ∃ t r', Exec (.repeat rKC clauseLe) r t ((leLoopModel m (r rW) acc).isSome, r') ∧
      t ≤ m * (50 * (N + 1) ^ 2 + 1) + 2 ∧
      ∀ w' acc', leLoopModel m (r rW) acc = some (w', acc') →
        r' rL = writeValues encodeLiteral acc' ∧ CClean r' ∧
        w'.length + (writeValues encodeLiteral acc').length ≤
          (r rW).length + (writeValues encodeLiteral acc).length := by
  intro m
  induction m with
  | zero =>
    intro acc r hm hL hc _
    refine ⟨2, r, Exec.repeatDone (List.eq_nil_of_length_eq_zero hm), by omega, ?_⟩
    intro w' acc' h
    simp only [leLoopModel, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨hL, hc, Nat.le_refl _⟩
  | succ m ih =>
    intro acc r hm hL hc hN
    obtain ⟨hA, hG, hS, hT1, hR⟩ := hc
    obtain ⟨b, tail, hK⟩ : ∃ b tail, r rKC = b :: tail := by
      cases h : r rKC with
      | nil => rw [h] at hm; simp at hm
      | cons b tail => exact ⟨b, tail, rfl⟩
    let r₀ := set r rKC tail
    obtain ⟨t1, r₁, e1, ht1, h1⟩ := clauseLe_spec acc r₀ (by simp +decide [r₀, hL])
      ⟨by simp +decide [r₀, hA], by simp +decide [r₀, hG], by simp +decide [r₀, hS],
        by simp +decide [r₀, hT1], by simp +decide [r₀, hR]⟩
    have e0w : r₀ rW = r rW := by simp +decide [r₀]
    have e0l : r₀ rL = r rL := by simp +decide [r₀]
    rw [e0w] at e1 ht1 h1
    have hsq : ((r rW).length + 1) ^ 2 ≤ (N + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    cases hmod : clauseLeModel (r rW) acc with
    | none =>
      rw [hmod] at e1
      refine ⟨t1 + 1, r₁, ?_, ?_, ?_⟩
      · simpa [leLoopModel, hmod] using Exec.repeatFailure hK e1
      · have h2 : 50 * (N + 1) ^ 2 + 1 ≤ (m + 1) * (50 * (N + 1) ^ 2 + 1) :=
          Nat.le_mul_of_pos_left _ (by omega)
        omega
      · intro w' acc' h
        simp [leLoopModel, hmod] at h
    | some p =>
      obtain ⟨w1, acc1⟩ := p
      rw [hmod] at e1
      obtain ⟨g1, g2, g3, g4⟩ := h1 w1 acc1 hmod
      obtain ⟨ls, hls⟩ := clauseLeModel_acc hmod
      have g5 : (writeValues encodeLiteral acc).length ≤ (writeValues encodeLiteral acc1).length := by
        rw [hls, writeValues_append, List.length_append]; omega
      have hK1 : (r₁ rKC).length = m := by
        rw [exec_frame' e1 rKC (by decide)]
        simp [r₀]
        rw [hK] at hm; simpa using hm
      obtain ⟨t2, r₂, e2, ht2, h2⟩ := ih acc1 r₁ hK1 g2 g3 (by rw [g1]; omega)
      rw [g1] at e2 h2
      refine ⟨t1 + t2 + 1, r₂, ?_, ?_, ?_⟩
      · simpa [leLoopModel, hmod] using Exec.repeatNext hK e1 e2
      · rw [Nat.add_mul, Nat.one_mul]; omega
      · intro w' acc' h
        simp only [leLoopModel, hmod] at h
        obtain ⟨k1, k2, k3⟩ := h2 w' acc' h
        refine ⟨k1, k2, ?_⟩
        omega

/-! ### The extraction pass -/

def pass1 : Command 23 :=
  .seq (.copy rIn rW rS) (.seq (readUnaryC rW rKC rG) (.repeat rKC clauseLe))

def pass1Model (x : Word) : Option (List Literal) :=
  match readNat x with
  | none => none
  | some (m, rest) =>
    match leLoopModel m rest [] with
    | none => none
    | some (_, acc) => some acc

theorem pass1_writes : ∀ j : Fin 24, j ∉ [rW, rL, rA, rG, rR, rT1, rKC] →
    writes pass1 j = false := by decide

theorem cube_bound (n m : Nat) (hm : m ≤ n) :
    5 * n + 6 + (8 * n + 8 + (m * (50 * (n + 1) ^ 2 + 1) + 2)) ≤ 70 * (n + 1) ^ 3 := by
  have h1 := Nat.mul_le_mul_right (50 * (n + 1) ^ 2 + 1) hm
  have h2 : n * (50 * (n + 1) ^ 2 + 1) ≤ 50 * (n + 1) ^ 3 + n := by
    have hq : (n + 1) ^ 3 = (n + 1) ^ 2 * n + (n + 1) ^ 2 := by
      rw [Nat.pow_succ, Nat.mul_succ]
    have e1 : n * (50 * (n + 1) ^ 2) = 50 * ((n + 1) ^ 2 * n) := by
      rw [Nat.mul_left_comm, Nat.mul_comm n]
    rw [Nat.mul_add, Nat.mul_one, e1, hq]
    omega
  have h3 : n + 1 ≤ (n + 1) ^ 3 := Nat.le_self_pow (by decide) _
  omega

theorem pass1_spec (r : Regs) (hr : HighEmpty r) :
    ∃ t r', Exec pass1 r t ((pass1Model (r rIn)).isSome, r') ∧
      t ≤ 70 * ((r rIn).length + 1) ^ 3 ∧
      ∀ lits, pass1Model (r rIn) = some lits →
        r' rL = writeValues encodeLiteral lits ∧ CClean r' ∧ (r' rL).length ≤ (r rIn).length := by
  let r₁ := set r rW (r rIn)
  have ec : Exec (.copy rIn rW rS) r ((r rW).length + 5 * (r rIn).length + 6) (true, r₁) :=
    Exec.copy (by decide) (by decide) (by decide) (hr rS (by decide))
  have hW0 : (r rW).length = 0 := by simp [hr rW (by decide)]
  rw [hW0] at ec
  obtain ⟨t2, r₂, e2, ht2, h2w, h2k, h2g, fr2⟩ := readUnaryC_spec rW rKC rG (by decide)
    (by decide) (by decide) r₁ (by simp +decide [r₁, hr rG (by decide)])
  have e1w : r₁ rW = r rIn := by simp [r₁]
  have e1k : r₁ rKC = [] := by simp +decide [r₁, hr rKC (by decide)]
  rw [e1w, e1k] at e2 h2w h2k
  rw [e1w] at ht2
  have hz : ∀ j : Fin 24, j ∉ [rW, rKC, rG] → 7 ≤ j.val → r₂ j = [] := by
    intro j hj h7
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hj
    rw [fr2 j hj.1 hj.2.1 hj.2.2]
    simp [r₁, StackMachine.set_other _ hj.1, hr j h7]
  have hcube : (r rIn).length + 1 ≤ ((r rIn).length + 1) ^ 3 := Nat.le_self_pow (by decide) _
  cases hn : readNat (r rIn) with
  | none =>
    have hf := unaryModel_of_readNat_none [] hn
    rw [hf] at e2
    refine ⟨0 + 5 * (r rIn).length + 6 + t2, r₂, ?_, by omega, ?_⟩
    · have : pass1Model (r rIn) = none := by simp [pass1Model, hn]
      rw [this]
      exact Exec.seq ec (Exec.seqFailure (second := .repeat rKC clauseLe) e2)
    · intro lits h; simp [pass1Model, hn] at h
  | some p =>
    obtain ⟨m, rest⟩ := p
    have hu := unaryModel_of_readNat (d := []) hn
    rw [hu] at e2 h2w h2k
    simp only [List.append_nil] at h2w h2k
    have hlen := congrArg List.length (readNat_eq_some hn)
    simp only [List.length_append, SATBounds.writeNat_length] at hlen
    obtain ⟨t3, r₃, e3, ht3, h3⟩ := leLoop_spec (r rIn).length m [] r₂ (by rw [h2k]; simp)
      (by rw [hz rL (by decide) (by decide)]; rfl)
      ⟨hz rA (by decide) (by decide), h2g, hz rS (by decide) (by decide),
        hz rT1 (by decide) (by decide), hz rR (by decide) (by decide)⟩ (by rw [h2w]; omega)
    rw [h2w] at e3 h3
    refine ⟨0 + 5 * (r rIn).length + 6 + (t2 + t3), r₃, ?_, ?_, ?_⟩
    · have he := Exec.seq ec (Exec.seq e2 e3)
      cases hl : leLoopModel m rest [] with
      | none =>
        rw [hl] at he
        have : pass1Model (r rIn) = none := by simp [pass1Model, hn, hl]
        rw [this]; exact he
      | some q =>
        rw [hl] at he
        have : pass1Model (r rIn) = some q.2 := by simp [pass1Model, hn, hl]
        rw [this]; exact he
    · exact Nat.le_trans (by omega) (cube_bound (r rIn).length m (by omega))
    · intro lits h
      cases hl : leLoopModel m rest [] with
      | none => simp [pass1Model, hn, hl] at h
      | some q =>
        obtain ⟨w', acc⟩ := q
        simp only [pass1Model, hn, hl, Option.some.injEq] at h
        subst h
        obtain ⟨k1, k2, k3⟩ := h3 w' acc hl
        refine ⟨k1, k2, ?_⟩
        rw [k1]
        simp [writeValues] at k3
        omega

/-! ### Semantics on encoded formulas -/

theorem moveModel_encode (rest : Word) :
    ∀ (c : Clause) (acc : List Literal),
      moveModel c.length (writeValues encodeLiteral c ++ rest) acc = some (rest, c.reverse ++ acc)
  | [], acc => by simp [moveModel, writeValues]
  | l :: c, acc => by
    simp only [List.length_cons, moveModel, writeValues, List.append_assoc,
      readLiteral_encodeLiteral, moveModel_encode rest c (l :: acc)]
    simp

theorem clauseLeModel_encode (c : Clause) (rest : Word) (acc : List Literal) :
    clauseLeModel (encodeClause c ++ rest) acc =
      if c.length = 2 ∨ c.length = 3 then some (rest, c.reverse ++ acc) else none := by
  unfold encodeClause writeList
  rw [List.append_assoc, clauseLeModel, readNat_writeNat]
  dsimp only
  by_cases h : c.length = 2 ∨ c.length = 3
  · rw [ite_eq_left h, ite_eq_left h, moveModel_encode]
  · rw [ite_eq_right h, ite_eq_right h]

theorem leLoopModel_encode (rest : Word) :
    ∀ (f : CNF) (acc : List Literal),
      leLoopModel f.length (writeValues encodeClause f ++ rest) acc =
        if ∀ c ∈ f, c.length = 2 ∨ c.length = 3 then some (rest, f.flatten.reverse ++ acc)
        else none
  | [], acc => by simp [leLoopModel, writeValues]
  | c :: f, acc => by
    simp only [List.length_cons, leLoopModel, writeValues, List.append_assoc,
      clauseLeModel_encode, List.forall_mem_cons]
    by_cases hc : c.length = 2 ∨ c.length = 3
    · rw [ite_eq_left hc]
      dsimp only
      rw [leLoopModel_encode rest f]
      by_cases hf : ∀ a ∈ f, a.length = 2 ∨ a.length = 3
      · rw [ite_eq_left hf, ite_eq_left ⟨hc, hf⟩]
        simp
      · rw [ite_eq_right hf, ite_eq_right (fun h => hf h.2)]
    · rw [ite_eq_right hc]
      dsimp only
      rw [ite_eq_right (fun h => hc h.1)]

theorem pass1Model_encode (f : CNF) :
    pass1Model (encode f) =
      if ∀ c ∈ f, c.length = 2 ∨ c.length = 3 then some f.flatten.reverse else none := by
  unfold pass1Model encode writeList
  rw [readNat_writeNat]
  dsimp only
  have := leLoopModel_encode [] f []
  simp only [List.append_nil] at this
  rw [this]
  by_cases hf : ∀ c ∈ f, c.length = 2 ∨ c.length = 3
  · rw [ite_eq_left hf, ite_eq_left hf]
  · rw [ite_eq_right hf, ite_eq_right hf]

end Complexity.Restricted
