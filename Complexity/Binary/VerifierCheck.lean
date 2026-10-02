module

public import Complexity.Binary.VerifierParse
import Lean.Elab.Tactic.Omega

/-!
# The second phase of the binary SAT verifier

The first phase leaves the code of a list of entries `es` in `entries` and `|es|` ones in
`count`. The second phase checks `consistent es`: for every entry (outer loop over a copy
`list₁`), it loads the entry's bit into `bit` and its digits into `digits`, and compares it
with every entry (inner loop over a copy `list₂`). Two entries with the same digits must
carry the same bit.
-/

@[expose] public section

namespace Complexity.Binary

open Complexity.SAT (Word)

theorem readEntry_eq_some {xs : Word} {c : Bool} {ds : List Bool} {rest : Word}
    (h : readEntry xs = some ((c, ds), rest)) : xs = pairs ds ++ false :: c :: rest := by
  induction xs using readEntry.induct generalizing c ds rest with
  | case1 d tail hnone =>
    simp [readEntry, hnone] at h
  | case2 d tail c' ds' tail' hsome ih =>
    simp only [readEntry, hsome, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
    rw [ih hsome]
    rfl
  | case3 c' tail =>
    simp only [readEntry, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
    rfl
  | case4 xs h₁ h₂ =>
    match xs, h₁, h₂ with
    | [], _, _ => simp [readEntry] at h
    | [true], _, _ => simp [readEntry] at h
    | [false], _, _ => simp [readEntry] at h
    | true :: d :: tail, h₁, _ => exact absurd rfl (h₁ d tail)
    | false :: c :: tail, _, h₂ => exact absurd rfl (h₂ c tail)

theorem readEntry_length {xs : Word} {e : Bool × List Bool} {rest : Word}
    (h : readEntry xs = some (e, rest)) : rest.length + 2 * e.2.length + 2 = xs.length := by
  obtain ⟨c, ds⟩ := e
  rw [readEntry_eq_some h]
  simp
  omega

theorem skipSpec_length : ∀ {xs rest : Word}, skipSpec xs = some rest → rest.length ≤ xs.length
  | false :: _ :: tail, rest, h => by
    simp only [skipSpec, Option.some.injEq] at h
    subst h
    simp only [List.length_cons]
    omega
  | true :: _ :: tail, rest, h => by
    simp only [skipSpec] at h
    have := skipSpec_length h
    simp
    omega
  | [], _, h => by simp [skipSpec] at h
  | [_], _, h => by simp [skipSpec] at h

theorem cmpSpec_length (ci : Word) :
    ∀ {xs e rest : Word}, cmpSpec ci xs e = some rest → rest.length ≤ xs.length
  | false :: c :: tail, e, rest, h => by
    simp only [cmpSpec] at h
    split at h
    · split at h
      · simp at h
      · split at h
        · simp only [Option.some.injEq] at h; subst h; simp only [List.length_cons]; omega
        · simp at h
    · simp only [Option.some.injEq] at h; subst h; simp only [List.length_cons]; omega
  | true :: _ :: tail, [], rest, h => by
    simp only [cmpSpec] at h
    have := skipSpec_length h
    simp
    omega
  | true :: d :: tail, b :: e, rest, h => by
    simp only [cmpSpec] at h
    split at h
    · have := cmpSpec_length ci h
      simp
      omega
    · have := skipSpec_length h
      simp
      omega
  | [], _, _, h => by simp [cmpSpec] at h
  | [false], _, _, h => by simp [cmpSpec] at h
  | [true], _, _, h => by simp [cmpSpec] at h

end Complexity.Binary

namespace Complexity.Binary.Verify

open Complexity.StackMachine (Registers set branch)
open Complexity.StackProgram Complexity.StackWords
open Complexity.SAT (Word)
open Complexity.Binary

/-! ## The inner loop -/

/-- Compare the entry at the front of `list₂` with the stored entry. -/
def innerBody :=
  seq (copy digits digitsCmp scratch) (seq (cmpEntry list₂ digitsCmp bit) (clear digitsCmp))

def innerBodyEncoding := copyMapEncoding.sum (cmpEntryEncoding.sum Encoding.bool)

/-- The partial register semantics of `innerBody`. -/
def innerStep (r : Registers 17) : Option (Registers 17) :=
  match cmpSpec (r bit) (r list₂) (r digits) with
  | none => none
  | some rest => some (set (set r list₂ rest) digitsCmp [])

def innerCost (bound : Nat) : Nat := 9 * bound + 14

/-- Invariant of the inner loop: only `list₂`, `digitsCmp` and the counter change. -/
structure InnerInv (bound : Nat) (base : Registers 17) (q : Registers 17) : Prop where
  cmp_eq : q 15 = []
  list_le : (q 10).length ≤ bound
  frame : ∀ j : Reg, j ≠ list₂ → j ≠ digitsCmp → j ≠ count₂ → q j = base j

theorem inner_runs (bound : Nat) (base : Registers 17) (hs : base 17 = [])
    (hd : (base 14).length ≤ bound) (r : Registers 17) (hI : InnerInv bound base r) :
    ∃ t b out, t ≤ innerCost bound ∧ Exec innerBody innerBody.start r t (b, out) ∧
      Realizes (innerStep r) b out := by
  have hscratch : r scratch = [] := by rw [hI.frame scratch (by decide) (by decide) (by decide)]; exact hs
  have hdig : (r digits).length ≤ bound := by
    rw [hI.frame digits (by decide) (by decide) (by decide)]; exact hd
  have h₁ := exec_copy digits digitsCmp scratch (by decide) (by decide) (by decide) r hscratch
  let r₁ := set r digitsCmp (r digits)
  obtain ⟨t, b, out, ht, he, hres⟩ := exec_cmpEntry list₂ digitsCmp bit (by decide) (by decide)
    (by decide) (r₁ list₂) r₁ rfl
  have hspec : cmpSpec (r₁ bit) (r₁ list₂) (r₁ digitsCmp) = cmpSpec (r bit) (r list₂) (r digits) := by
    simp [r₁]
  rw [hspec] at hres
  have hcmp : (r digitsCmp).length = 0 := by simp [hI.cmp_eq]
  have hlist : (r₁ list₂).length ≤ bound := by simpa [r₁] using hI.list_le
  unfold innerStep
  cases hs : cmpSpec (r bit) (r list₂) (r digits) with
  | none =>
    have hb : b = false := by simpa [CmpResult, hs] using hres
    subst hb
    have hf := exec_seq _ _ h₁ (exec_seq_failure _ (clear digitsCmp) he)
    refine ⟨_, false, out, ?_, hf, rfl⟩
    unfold innerCost
    omega
  | some rest =>
    simp only [CmpResult, hs] at hres
    obtain ⟨rfl, hsrc, hE, hframe⟩ := hres
    have hfull := exec_seq _ _ h₁ (exec_seq _ _ he (exec_clear digitsCmp out))
    have hout : set out digitsCmp [] = set (set r list₂ rest) digitsCmp [] := by
      funext j
      by_cases hj : j = digitsCmp
      · subst hj; simp
      · by_cases hl : j = list₂
        · subst hl; simp [hsrc]
        · simp only [StackMachine.set, hj, hl, ite_false]
          rw [hframe j hl hj]
          simp [r₁, hj]
    rw [hout] at hfull
    refine ⟨_, true, _, ?_, hfull, by simp⟩
    have hE' : (out digitsCmp).length ≤ (r digits).length := by simpa [r₁] using hE
    unfold innerCost
    omega

theorem InnerInv.set_count {bound : Nat} {base q : Registers 17} (h : InnerInv bound base q)
    (xs : Word) : InnerInv bound base (set q count₂ xs) := by
  constructor
  · simpa using h.cmp_eq
  · simpa using h.list_le
  · intro j h₁ h₂ h₃
    simp only [StackMachine.set, h₃, ite_false]
    exact h.frame j h₁ h₂ h₃

theorem InnerInv.step {bound : Nat} {base q out : Registers 17} (h : InnerInv bound base q)
    (hs : innerStep q = some out) : InnerInv bound base out ∧ out count₂ = q count₂ := by
  unfold innerStep at hs
  cases hc : cmpSpec (q bit) (q list₂) (q digits) with
  | none => simp [hc] at hs
  | some rest =>
    simp only [hc, Option.some.injEq] at hs
    subst hs
    have hlen := cmpSpec_length _ hc
    have hl := h.list_le
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
    · simp
    · simp only [list₂] at hlen; simp; omega
    · intro j h₁ h₂ h₃
      simp only [StackMachine.set, h₁, h₂, ite_false]
      exact h.frame j h₁ h₂ h₃
    · simp

theorem inner_loop_runs (bound : Nat) (base : Registers 17) (hs : base 17 = [])
    (hd : (base 14).length ≤ bound) (n : Nat) (r : Registers 17)
    (hI : InnerInv bound base r) (hr : r count₂ = List.replicate n true) :
    ∃ t b out, t ≤ n * (innerCost bound + 1) + 2 ∧
      Exec (whileCounter count₂ innerBody) (.inl false) r t (b, out) ∧
      Realizes (iterStep count₂ innerStep n r) b out :=
  whileCounter_iter innerBody count₂ innerStep (InnerInv bound base) (innerCost bound)
    (fun _ tail hq _ => hq.set_count tail) (fun q hq => inner_runs bound base hs hd q hq)
    (fun _ _ hq hs => hq.step hs) n r hr hI

theorem inner_loop_invariant (bound : Nat) (base : Registers 17) (n : Nat)
    (r : Registers 17) (hI : InnerInv bound base r) (hr : r count₂ = List.replicate n true)
    (out : Registers 17) (h : iterStep count₂ innerStep n r = some out) :
    InnerInv bound base out ∧ out count₂ = [] :=
  iterStep_invariant count₂ innerStep (InnerInv bound base)
    (fun _ tail hq _ => hq.set_count tail) (fun _ _ hq hs => hq.step hs) n r hr hI out h

/-! ## The outer loop -/

/-- Load the entry at the front of `list₁` and compare it with all entries. -/
def outerBody :=
  seq (loadEntry list₁ digitsRev bit) (seq (transfer digitsRev digits)
    (seq (copy entries list₂ scratch) (seq (copy count count₂ scratch)
      (seq (whileCounter count₂ innerBody) (seq (clear digits) (pop bit))))))

def outerBodyEncoding :=
  loadEntryEncoding.sum ((Encoding.fin 3).sum (copyMapEncoding.sum (copyMapEncoding.sum
    ((Encoding.bool.sum innerBodyEncoding).sum (Encoding.bool.sum Encoding.bool)))))

def outerLoad (r : Registers 17) (c : Bool) (ds : List Bool) (rest : Word) : Registers 17 :=
  set (set (set (set (set r list₁ rest) bit [c]) digits ds) list₂ (r entries)) count₂ (r count)

/-- The partial register semantics of `outerBody`. -/
def outerStep (r : Registers 17) : Option (Registers 17) :=
  match readEntry (r list₁) with
  | none => none
  | some ((c, ds), rest) =>
    (iterStep count₂ innerStep (r count).length (outerLoad r c ds rest)).map
      (fun q => set (set q digits []) bit [])

def outerCost (bound : Nat) : Nat := bound * (innerCost bound + 1) + 20 * bound + 30

/-- Invariant of the outer loop. -/
structure OuterInv (bound : Nat) (q : Registers 17) : Prop where
  scratch_eq : q 17 = []
  rev_eq : q 13 = []
  digits_eq : q 14 = []
  bit_eq : q 16 = []
  cmp_eq : q 15 = []
  count_eq : q 8 = List.replicate (q 8).length true
  entries_le : (q 7).length ≤ bound
  count_le : (q 8).length ≤ bound
  list₁_le : (q 9).length ≤ bound
  list₂_le : (q 10).length ≤ bound
  count₂_le : (q 12).length ≤ bound

theorem OuterInv.inner {bound : Nat} {q : Registers 17} (h : OuterInv bound q) (c : Bool)
    (ds : List Bool) (rest : Word) :
    InnerInv bound (outerLoad q c ds rest) (outerLoad q c ds rest) := by
  constructor
  · simp [outerLoad, h.cmp_eq]
  · simpa [outerLoad] using h.entries_le
  · intro j _ _ _; rfl

theorem outer_runs (bound : Nat) (r : Registers 17) (hI : OuterInv bound r) :
    ∃ t b out, t ≤ outerCost bound ∧ Exec outerBody outerBody.start r t (b, out) ∧
      Realizes (outerStep r) b out := by
  have hl₁ := hI.list₁_le
  unfold outerStep
  cases hp : readEntry (r list₁) with
  | none =>
    obtain ⟨t, out, ht, he⟩ := exec_loadEntry_malformed list₁ digitsRev bit (by decide)
      (r list₁) r rfl hp
    have hf := exec_seq_failure _ (seq (transfer digitsRev digits)
      (seq (copy entries list₂ scratch) (seq (copy count count₂ scratch)
        (seq (whileCounter count₂ innerBody) (seq (clear digits) (pop bit)))))) he
    refine ⟨t, false, out, ?_, hf, rfl⟩
    unfold outerCost
    simp only [list₁] at ht
    omega
  | some pair =>
    obtain ⟨⟨c, ds⟩, rest⟩ := pair
    have hxs := readEntry_eq_some hp
    have hlen := readEntry_length hp
    simp only at hlen
    have h₁ := exec_loadEntry_pairs list₁ digitsRev bit (by decide) (by decide) (by decide)
      ds c rest r hxs
    let r₁ := set (set (set r list₁ rest) digitsRev (ds.reverse ++ r digitsRev)) bit (c :: r bit)
    have h₂ := exec_transfer digitsRev digits (by decide) r₁
    let r₂ := set (set r₁ digitsRev []) digits ((r₁ digitsRev).reverse ++ r₁ digits)
    have h₃ := exec_copy entries list₂ scratch (by decide) (by decide) (by decide) r₂
      (by simp [r₂, r₁, hI.scratch_eq])
    let r₃ := set r₂ list₂ (r₂ entries)
    have h₄ := exec_copy count count₂ scratch (by decide) (by decide) (by decide) r₃
      (by simp [r₃, r₂, r₁, hI.scratch_eq])
    let r₄ := set r₃ count₂ (r₃ count)
    have hr₄ : r₄ = outerLoad r c ds rest := by
      apply regs_ext <;> simp [r₄, r₃, r₂, r₁, outerLoad, hI.rev_eq, hI.digits_eq, hI.bit_eq]
    have hdsle : ds.length ≤ bound := by simp only [list₁] at hlen; omega
    have hIn : InnerInv bound (outerLoad r c ds rest) (outerLoad r c ds rest) := hI.inner c ds rest
    have hcount : (outerLoad r c ds rest) count₂ = List.replicate (r count).length true := by
      simpa [outerLoad] using hI.count_eq
    obtain ⟨t, b, mid, ht, he, hspec⟩ := inner_loop_runs bound (outerLoad r c ds rest)
      (by simp [outerLoad, hI.scratch_eq]) (by simpa [outerLoad] using hdsle)
      (r count).length _ hIn hcount
    rw [← hr₄] at he
    have hn : (r count).length ≤ bound := hI.count_le
    have hloop : (r count).length * (innerCost bound + 1) ≤ bound * (innerCost bound + 1) :=
      Nat.mul_le_mul_right _ hn
    have hcostPrefix : (3 * ds.length + 4) + (2 * (r₁ digitsRev).length + 2) +
        ((r₂ list₂).length + 5 * (r₂ entries).length + 6) +
        ((r₃ count₂).length + 5 * (r₃ count).length + 6) ≤ 18 * bound + 18 := by
      have h₇ := hI.entries_le
      have h₈ := hI.count_le
      have h₁₀ := hI.list₂_le
      have h₁₂ := hI.count₂_le
      simp [r₃, r₂, r₁, hI.rev_eq]
      omega
    cases hex : iterStep count₂ innerStep (r count).length (outerLoad r c ds rest) with
    | none =>
      have hfalse : b = false := by simpa [hex] using hspec
      subst b
      have hf := exec_seq _ _ h₁ (exec_seq _ _ h₂ (exec_seq _ _ h₃ (exec_seq _ _ h₄
        (exec_seq_failure _ (seq (clear digits) (pop bit)) he))))
      refine ⟨_, false, mid, ?_, hf, by simp [hex]⟩
      unfold outerCost
      omega
    | some q =>
      have hs : b = true ∧ mid = q := by simpa [hex] using hspec
      obtain ⟨rfl, rfl⟩ := hs
      obtain ⟨hIq, _⟩ := inner_loop_invariant bound _ (r count).length _ hIn hcount mid hex
      have h₆ := exec_clear digits mid
      have h₇ := exec_pop bit (set mid digits [])
      have hf := exec_seq _ _ h₁ (exec_seq _ _ h₂ (exec_seq _ _ h₃ (exec_seq _ _ h₄
        (exec_seq _ _ he (exec_seq _ _ h₆ h₇)))))
      have hmbit : mid bit = [c] := by
        rw [hIq.frame bit (by decide) (by decide) (by decide)]; simp [outerLoad]
      have hmdig : mid digits = ds := by
        rw [hIq.frame digits (by decide) (by decide) (by decide)]; simp [outerLoad]
      have hbit : (set mid digits []) bit = [c] := by simpa using hmbit
      have hout : set (set mid digits []) bit (set mid digits [] bit).tail =
          set (set mid digits []) bit [] := by rw [hbit]; rfl
      rw [hout] at hf
      refine ⟨_, true, _, ?_, hf, by simp [hex]⟩
      have hdig : (mid digits).length = ds.length := by rw [hmdig]
      unfold outerCost
      omega

theorem OuterInv.set_count {bound : Nat} {q : Registers 17} (h : OuterInv bound q)
    (xs : Word) : OuterInv bound (set q count₁ xs) := by
  constructor
  · simpa using h.scratch_eq
  · simpa using h.rev_eq
  · simpa using h.digits_eq
  · simpa using h.bit_eq
  · simpa using h.cmp_eq
  · simpa using h.count_eq
  · simpa using h.entries_le
  · simpa using h.count_le
  · simpa using h.list₁_le
  · simpa using h.list₂_le
  · simpa using h.count₂_le

theorem OuterInv.step {bound : Nat} {q out : Registers 17} (h : OuterInv bound q)
    (hs : outerStep q = some out) : OuterInv bound out ∧ out count₁ = q count₁ := by
  unfold outerStep at hs
  cases hp : readEntry (q list₁) with
  | none => simp [hp] at hs
  | some pair =>
    obtain ⟨⟨c, ds⟩, rest⟩ := pair
    simp only [hp] at hs
    have hlen := readEntry_length hp
    simp only at hlen
    have hl₁ := h.list₁_le
    have hIn := h.inner c ds rest
    have hcount : (outerLoad q c ds rest) count₂ = List.replicate (q count).length true := by
      simpa [outerLoad] using h.count_eq
    cases hex : iterStep count₂ innerStep (q count).length (outerLoad q c ds rest) with
    | none => simp [hex] at hs
    | some mid =>
      simp only [hex, Option.map_some, Option.some.injEq] at hs
      subst hs
      obtain ⟨hIm, hc₂⟩ := inner_loop_invariant bound _ (q count).length _ hIn hcount mid hex
      have hf := hIm.frame
      have hl₂ := hIm.list_le
      have e13 := hf 13 (by decide) (by decide) (by decide)
      have e17 := hf 17 (by decide) (by decide) (by decide)
      have e8 := hf 8 (by decide) (by decide) (by decide)
      have e7 := hf 7 (by decide) (by decide) (by decide)
      have e9 := hf 9 (by decide) (by decide) (by decide)
      have e11 := hf 11 (by decide) (by decide) (by decide)
      have h7 := h.entries_le
      have h8 := h.count_le
      simp only [outerLoad, StackMachine.set, list₁, bit, digits, list₂, count₂, entries,
        count] at e13 e17 e8 e7 e9 e11
      simp at e13 e17 e8 e7 e9 e11
      simp only [count₂] at hc₂
      refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
      · simp [e17, h.scratch_eq]
      · simp [e13, h.rev_eq]
      · simp
      · simp
      · simp [hIm.cmp_eq]
      · simp [e8]; exact h.count_eq
      · simp [e7]; exact h7
      · simp [e8]; exact h8
      · simp [e9]; simp only [list₁] at hlen; omega
      · simpa using hl₂
      · simp [hc₂]
      · simp [e11]

theorem outer_loop_runs (bound n : Nat) (r : Registers 17) (hI : OuterInv bound r)
    (hr : r count₁ = List.replicate n true) :
    ∃ t b out, t ≤ n * (outerCost bound + 1) + 2 ∧
      Exec (whileCounter count₁ outerBody) (.inl false) r t (b, out) ∧
      Realizes (iterStep count₁ outerStep n r) b out :=
  whileCounter_iter outerBody count₁ outerStep (OuterInv bound) (outerCost bound)
    (fun _ tail hq _ => hq.set_count tail) (fun q hq => outer_runs bound q hq)
    (fun _ _ hq hs => hq.step hs) n r hr hI

/-! ## The check -/

/-- Copy the entries and their count, then run the outer loop. -/
def check :=
  seq (copy entries list₁ scratch) (seq (copy count count₁ scratch) (whileCounter count₁ outerBody))

def checkEncoding :=
  copyMapEncoding.sum (copyMapEncoding.sum (Encoding.bool.sum outerBodyEncoding))

def checkLoad (r : Registers 17) : Registers 17 :=
  set (set r list₁ (r entries)) count₁ (r count)

def checkCost (bound : Nat) : Nat := bound * (outerCost bound + 1) + 12 * bound + 14

/-- Registers at the start of the check. -/
structure CheckInv (bound : Nat) (q : Registers 17) : Prop where
  scratch_eq : q 17 = []
  rev_eq : q 13 = []
  digits_eq : q 14 = []
  bit_eq : q 16 = []
  cmp_eq : q 15 = []
  list₁_eq : q 9 = []
  list₂_eq : q 10 = []
  count₁_eq : q 11 = []
  count₂_eq : q 12 = []
  count_eq : q 8 = List.replicate (q 8).length true
  entries_le : (q 7).length ≤ bound
  count_le : (q 8).length ≤ bound

theorem check_runs (bound : Nat) (r : Registers 17) (hI : CheckInv bound r) :
    ∃ t b out, t ≤ checkCost bound ∧ Exec check check.start r t (b, out) ∧
      Realizes (iterStep count₁ outerStep (r count).length (checkLoad r)) b out := by
  have h₁ := exec_copy entries list₁ scratch (by decide) (by decide) (by decide) r hI.scratch_eq
  let r₁ := set r list₁ (r entries)
  have h₂ := exec_copy count count₁ scratch (by decide) (by decide) (by decide) r₁
    (by simp [r₁, hI.scratch_eq])
  have hr₂ : set r₁ count₁ (r₁ count) = checkLoad r := by
    apply regs_ext <;> simp [r₁, checkLoad]
  rw [hr₂] at h₂
  have hO : OuterInv bound (checkLoad r) := by
    constructor
    · simp [checkLoad, hI.scratch_eq]
    · simp [checkLoad, hI.rev_eq]
    · simp [checkLoad, hI.digits_eq]
    · simp [checkLoad, hI.bit_eq]
    · simp [checkLoad, hI.cmp_eq]
    · simpa [checkLoad] using hI.count_eq
    · simpa [checkLoad] using hI.entries_le
    · simpa [checkLoad] using hI.count_le
    · simpa [checkLoad] using hI.entries_le
    · simp [checkLoad, hI.list₂_eq]
    · simp [checkLoad, hI.count₂_eq]
  obtain ⟨t, b, out, ht, he, hspec⟩ := outer_loop_runs bound (r count).length (checkLoad r) hO
    (by simpa [checkLoad] using hI.count_eq)
  have hf := exec_seq _ _ h₁ (exec_seq _ _ h₂ he)
  refine ⟨_, b, out, ?_, hf, hspec⟩
  have hn := hI.count_le
  have he' := hI.entries_le
  have hloop : (r count).length * (outerCost bound + 1) ≤ bound * (outerCost bound + 1) :=
    Nat.mul_le_mul_right _ hn
  simp [r₁, hI.list₁_eq, hI.count₁_eq]
  unfold checkCost
  omega

end Complexity.Binary.Verify
