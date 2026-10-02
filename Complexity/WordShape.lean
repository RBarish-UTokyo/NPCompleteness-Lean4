module

public import Complexity.TapeEquiv
import Lean.Elab.Tactic.Omega

/-!
Local conditions describing a variable-length binary word followed by blanks.
These conditions allow certificates of every length up to a bound, rather than
silently replacing the NP verifier by one expecting fixed-length witnesses.
-/

@[expose] public section

namespace Complexity

def WordShaped (xs : List Symbol) : Prop :=
  (∀ i, xs.getD i .blank ≠ .sep) ∧
  (∀ i, xs.getD i .blank = .blank → xs.getD (i + 1) .blank = .blank)

theorem wordShaped_tail {a : Symbol} {xs : List Symbol}
    (h : WordShaped (a :: xs)) : WordShaped xs := by
  constructor
  · intro i
    simpa only [List.getD_cons_succ] using h.1 (i + 1)
  · intro i hi
    have hh := h.2 (i + 1)
    simpa only [List.getD_cons_succ] using hh hi

theorem wordShaped_blank {xs : List Symbol} (h : WordShaped xs)
    (hzero : xs.getD 0 .blank = .blank) : BlankEq xs [] := by
  intro i
  change xs.getD i .blank = .blank
  induction i with
  | zero => exact hzero
  | succ i ih => exact h.2 i ih

/-- The local shape rules exclude nonblank symbols after the first blank. -/
theorem wordShaped_bits {xs : List Symbol} (h : WordShaped xs) :
    BlankEq xs ((Tape.bits xs).map Symbol.bit) := by
  induction xs with
  | nil => exact BlankEq.refl []
  | cons a xs ih =>
    cases a with
    | blank => exact wordShaped_blank h rfl
    | bit b => exact (ih (wordShaped_tail h)).cons (.bit b)
    | sep => exact False.elim (h.1 0 rfl)

theorem wordShaped_bits_length {xs : List Symbol} (h : WordShaped xs) :
    ∃ word : List Bool, word.length ≤ xs.length ∧ BlankEq xs (word.map Symbol.bit) :=
  ⟨Tape.bits xs, Tape.bits_length_le xs, wordShaped_bits h⟩

theorem wordShaped_map_bits (word : List Bool) : WordShaped (word.map Symbol.bit) := by
  induction word with
  | nil => simp [WordShaped]
  | cons b word ih =>
    constructor
    · intro i
      cases i with
      | zero => simp
      | succ i => simpa only [List.map_cons, List.getD_cons_succ] using ih.1 i
    · intro i hi
      cases i with
      | zero => simp at hi
      | succ i =>
        simpa only [List.map_cons, List.getD_cons_succ] using ih.2 i hi

theorem wordShaped_of_blankEq {xs ys : List Symbol} (h : BlankEq xs ys)
    (hy : WordShaped ys) : WordShaped xs := by
  constructor
  · intro i
    simpa only [h i] using hy.1 i
  · intro i hi
    rw [h i] at hi
    rw [h (i + 1)]
    exact hy.2 i hi

theorem wordShaped_iff {xs : List Symbol} :
    WordShaped xs ↔ ∃ word : List Bool, BlankEq xs (word.map Symbol.bit) := by
  constructor
  · intro h
    exact ⟨Tape.bits xs, wordShaped_bits h⟩
  · intro ⟨word, h⟩
    exact wordShaped_of_blankEq h (wordShaped_map_bits word)

/-- Shape only needs to be checked inside the represented list: the infinite
implicit suffix is already entirely blank. -/
theorem wordShaped_of_local (xs : List Symbol)
    (hsym : ∀ i, i < xs.length → xs.getD i .blank ≠ .sep)
    (hblank : ∀ i, i + 1 < xs.length →
      xs.getD i .blank = .blank → xs.getD (i + 1) .blank = .blank) :
    WordShaped xs := by
  constructor
  · intro i
    by_cases hi : i < xs.length
    · exact hsym i hi
    · simp [List.getD, List.getElem?_eq_none (by omega : xs.length ≤ i)]
  · intro i hi
    by_cases hnext : i + 1 < xs.length
    · exact hblank i hnext hi
    · simp [List.getD, List.getElem?_eq_none (by omega : xs.length ≤ i + 1)]

end Complexity
