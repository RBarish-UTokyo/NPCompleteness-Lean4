module

public import Complexity.FiniteRows
public import Complexity.WordShape
import Lean.Elab.Tactic.Omega

/-!
Initial-row constraints for a fixed binary pfx followed by an arbitrary
certificate of length at most a bound. The certificate may end early; local
blank-propagation constraints require the rest of the window to be blank.
-/

@[expose] public section

namespace Complexity.InitialWord

open CSPSAT LocalConstraint FiniteRows

def pin {m d : Nat} (slot : Fin m) (value : Fin (d + 1)) : Instance m d :=
  (Tree.value value).encode slot

@[simp] theorem pin_correct {m d : Nat} (r : Valuation m d)
    (slot : Fin m) (value : Fin (d + 1)) :
    Satisfied r (pin slot value) ↔ r slot = value := value_encode_correct r slot value

def allow {m d : Nat} (slot : Fin m) (values : List (Fin (d + 1))) : Instance m d :=
  ((List.finRange (d + 1)).filter (fun v => !values.contains v)).map
    (fun v => [(slot, v)])

theorem allow_correct {m d : Nat} (r : Valuation m d)
    (slot : Fin m) (values : List (Fin (d + 1))) :
    Satisfied r (allow slot values) ↔ r slot ∈ values := by
  constructor
  · intro h
    by_cases hm : r slot ∈ values
    · exact hm
    have hb : r slot ∈ (List.finRange (d + 1)).filter (fun v => !values.contains v) := by
      simp [hm]
    have hx := h [(slot, r slot)] (List.mem_map.mpr ⟨r slot, hb, rfl⟩)
    obtain ⟨atom, ha, hn⟩ := hx
    simp only [List.mem_singleton] at ha
    subst atom
    exact False.elim (hn rfl)
  · intro h tuple ht
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp ht
    have hn : v ∉ values := by simpa using (List.mem_filter.mp hv).2
    refine ⟨(slot, v), by simp, ?_⟩
    intro heq
    change r slot = v at heq
    exact hn (heq ▸ h)

theorem satisfied_append {m d : Nat} (r : Valuation m d) (a b : Instance m d) :
    Satisfied r (a ++ b) ↔ Satisfied r a ∧ Satisfied r b := by
  simp only [Satisfied, List.mem_append, or_imp, forall_and]

def witnessValues (M : Machine) : List (Value M) :=
  [symbolValue M .blank, symbolValue M (.bit false), symbolValue M (.bit true)]

def rightCell (M : Machine) (width : Nat) (pfx : List Bool) (bound : Nat)
    (i : Fin width) : Instance (2 * width + 1) (M.states + 3) :=
  if i.val < pfx.length then
    pin (rightSlot width i) (symbolValue M ((pfx.map Symbol.bit).getD i.val .blank))
  else if i.val < pfx.length + bound then
    allow (rightSlot width i) (witnessValues M)
  else pin (rightSlot width i) (symbolValue M .blank)

def blankCell (M : Machine) (width : Nat) (pfx : List Bool) (bound : Nat)
    (fit : pfx.length + bound ≤ width) (i : Fin width) :
    Instance (2 * width + 1) (M.states + 3) :=
  if h : pfx.length ≤ i.val ∧ i.val + 1 < pfx.length + bound then
    guard (rightSlot width i, symbolValue M .blank)
      (pin (rightSlot width ⟨i.val + 1, by omega⟩) (symbolValue M .blank))
  else []

def problem (M : Machine) (width : Nat) (pfx : List Bool) (bound : Nat)
    (fit : pfx.length + bound ≤ width) : Instance (2 * width + 1) (M.states + 3) :=
  pin (stateSlot width) (stateValue M M.start) ++
  (List.finRange width).flatMap (fun i => pin (leftSlot width i) (symbolValue M .blank)) ++
  (List.finRange width).flatMap (rightCell M width pfx bound) ++
  (List.finRange width).flatMap (blankCell M width pfx bound fit)

def Conditions (M : Machine) (width : Nat) (pfx : List Bool) (bound : Nat)
    (fit : pfx.length + bound ≤ width) (r : Row M width) : Prop :=
  r (stateSlot width) = stateValue M M.start ∧
  (∀ i, r (leftSlot width i) = symbolValue M .blank) ∧
  (∀ i, if i.val < pfx.length then
      r (rightSlot width i) = symbolValue M ((pfx.map Symbol.bit).getD i.val .blank)
    else if i.val < pfx.length + bound then
      r (rightSlot width i) ∈ witnessValues M
    else r (rightSlot width i) = symbolValue M .blank) ∧
  (∀ i : Fin width, ∀ h : pfx.length ≤ i.val ∧ i.val + 1 < pfx.length + bound,
    r (rightSlot width i) = symbolValue M .blank →
      r (rightSlot width ⟨i.val + 1, by omega⟩) = symbolValue M .blank)

theorem problem_correct (M : Machine) (width : Nat) (pfx : List Bool) (bound : Nat)
    (fit : pfx.length + bound ≤ width) (r : Row M width) :
    Satisfied r (problem M width pfx bound fit) ↔ Conditions M width pfx bound fit r := by
  have hr (i : Fin width) : Satisfied r (rightCell M width pfx bound i) ↔
      (if i.val < pfx.length then
        r (rightSlot width i) = symbolValue M ((pfx.map Symbol.bit).getD i.val .blank)
      else if i.val < pfx.length + bound then r (rightSlot width i) ∈ witnessValues M
      else r (rightSlot width i) = symbolValue M .blank) := by
    simp only [rightCell]
    split
    · exact pin_correct _ _ _
    · split
      · exact allow_correct _ _ _
      · exact pin_correct _ _ _
  have hb (i : Fin width) : Satisfied r (blankCell M width pfx bound fit i) ↔
      (∀ h : pfx.length ≤ i.val ∧ i.val + 1 < pfx.length + bound,
        r (rightSlot width i) = symbolValue M .blank →
          r (rightSlot width ⟨i.val + 1, by omega⟩) = symbolValue M .blank) := by
    by_cases hc : pfx.length ≤ i.val ∧ i.val + 1 < pfx.length + bound
    · simp [blankCell, hc, satisfied_guard_iff]
    · simp [blankCell, hc, Satisfied]
  simp only [problem, satisfied_append, pin_correct, satisfied_flatMap_iff,
    List.mem_finRange, true_implies, hr, hb, Conditions]
  simp only [and_assoc]

def witnessSymbols (M : Machine) (width : Nat) (pfx : List Bool) (bound : Nat)
    (fit : pfx.length + bound ≤ width) (r : Row M width) : List Symbol :=
  List.ofFn (fun i : Fin bound =>
    decodeSymbol M (r (rightSlot width ⟨pfx.length + i.val, by omega⟩)))

@[simp] theorem witnessSymbols_length (M : Machine) (width : Nat) (pfx : List Bool)
    (bound : Nat) (fit : pfx.length + bound ≤ width) (r : Row M width) :
    (witnessSymbols M width pfx bound fit r).length = bound := by
  simp [witnessSymbols]

theorem witnessSymbols_getD (M : Machine) (width : Nat) (pfx : List Bool)
    (bound : Nat) (fit : pfx.length + bound ≤ width) (r : Row M width)
    (i : Fin bound) :
    (witnessSymbols M width pfx bound fit r).getD i.val .blank =
      decodeSymbol M (r (rightSlot width ⟨pfx.length + i.val, by omega⟩)) := by
  simp [witnessSymbols, List.getD, i.isLt]

theorem symbolValue_decode_of_mem (M : Machine) (value : Value M)
    (h : value ∈ witnessValues M) : symbolValue M (decodeSymbol M value) = value := by
  simp only [witnessValues, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl <;> simp

theorem decode_ne_sep_of_mem (M : Machine) (value : Value M)
    (h : value ∈ witnessValues M) : decodeSymbol M value ≠ .sep := by
  simp only [witnessValues, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl <;> simp

theorem witnessSymbols_shaped (M : Machine) (width : Nat) (pfx : List Bool)
    (bound : Nat) (fit : pfx.length + bound ≤ width) (r : Row M width)
    (h : Conditions M width pfx bound fit r) :
    WordShaped (witnessSymbols M width pfx bound fit r) := by
  have hm (i : Fin bound) :
      r (rightSlot width ⟨pfx.length + i.val, by omega⟩) ∈ witnessValues M := by
    have hi := h.2.2.1 (⟨pfx.length + i.val, by omega⟩ : Fin width)
    simpa [show ¬ pfx.length + i.val < pfx.length by omega,
      show pfx.length + i.val < pfx.length + bound by omega] using hi
  apply wordShaped_of_local
  · intro i hi
    have hib : i < bound := by simpa using hi
    rw [witnessSymbols_getD M width pfx bound fit r ⟨i, hib⟩]
    exact decode_ne_sep_of_mem M _ (hm ⟨i, hib⟩)
  · intro i hi hblank
    have hib : i < bound := by simpa using Nat.lt_trans (Nat.lt_succ_self i) hi
    have hinext : i + 1 < bound := by simpa using hi
    rw [witnessSymbols_getD M width pfx bound fit r ⟨i, hib⟩] at hblank
    rw [witnessSymbols_getD M width pfx bound fit r ⟨i + 1, hinext⟩]
    have hraw : r (rightSlot width ⟨pfx.length + i, by omega⟩) = symbolValue M .blank := by
      rw [← symbolValue_decode_of_mem M _ (hm ⟨i, hib⟩), hblank]
    have hnext := h.2.2.2 (⟨pfx.length + i, by omega⟩ : Fin width) (by constructor <;> dsimp <;> omega) hraw
    have hidx : pfx.length + (i + 1) = (pfx.length + i) + 1 := by omega
    simp [hidx, hnext]


theorem getD_append_left {xs ys : List Symbol} {i : Nat} (hi : i < xs.length) :
    (xs ++ ys).getD i .blank = xs.getD i .blank := by
  simp only [List.getD, List.getElem?_append_left hi]

theorem getD_append_right {xs ys : List Symbol} {i : Nat} (hi : xs.length ≤ i) :
    (xs ++ ys).getD i .blank = ys.getD (i - xs.length) .blank := by
  simp only [List.getD, List.getElem?_append_right hi]

theorem getD_map_bit_cases (word : List Bool) (i : Nat) :
    (word.map Symbol.bit).getD i .blank = .blank ∨
      (word.map Symbol.bit).getD i .blank = .bit false ∨
      (word.map Symbol.bit).getD i .blank = .bit true := by
  simp only [List.getD, List.getElem?_map]
  cases word[i]? with
  | none => simp
  | some b => cases b <;> simp

theorem encode_window (M : Machine) (width : Nat) (s : Status M) :
    FiniteRows.encode M width (s.window width) = FiniteRows.encode M width s := by
  funext slot
  rcases slot_cases slot with rfl | ⟨i, rfl⟩ | ⟨i, rfl⟩
  · cases s <;> rfl
  · simp only [encode_left, Status.window_tape, Tape.window_left_getD_lt _ _ _ i.isLt]
  · simp only [encode_right, Status.window_tape, Tape.window_right_getD_lt _ _ _ i.isLt]

theorem initial_conditions (M : Machine) (width : Nat) (pfx word : List Bool)
    (bound : Nat) (fit : pfx.length + bound ≤ width) (hw : word.length ≤ bound) :
    Conditions M width pfx bound fit
      (FiniteRows.encode M width (.running (initial M (pfx ++ word)))) := by
  refine ⟨rfl, ?_, ?_, ?_⟩
  · intro i
    simp [Status.tape, initial, Tape.ofInput]
  · intro i
    simp only [encode_right, Status.tape, initial, Tape.ofInput, List.map_append]
    by_cases hp : i.val < pfx.length
    · simp only [hp, ↓reduceIte]
      rw [getD_append_left (by simpa using hp)]
    · simp only [hp, ↓reduceIte]
      rw [getD_append_right (by simpa using (by omega : pfx.length ≤ i.val))]
      simp only [List.length_map]
      by_cases hb : i.val < pfx.length + bound
      · simp only [hb, ↓reduceIte]
        rcases getD_map_bit_cases word (i.val - pfx.length) with h | h | h <;>
          simp only [h, witnessValues, List.mem_cons, List.not_mem_nil, or_false, true_or, or_true, eq_self]
      · simp only [hb, ↓reduceIte]
        have hlen : (word.map Symbol.bit).length ≤ i.val - pfx.length := by
          simp only [List.length_map]; omega
        simp [List.getD, List.getElem?_eq_none hlen]
  · intro i hi hblank
    simp only [encode_right, Status.tape, initial, Tape.ofInput] at hblank ⊢
    apply congrArg (symbolValue M)
    exact (wordShaped_map_bits (pfx ++ word)).2 i.val
      (symbolValue_injective M hblank)

theorem conditions_initial (M : Machine) (width : Nat) (pfx : List Bool)
    (bound : Nat) (fit : pfx.length + bound ≤ width) (r : Row M width)
    (h : Conditions M width pfx bound fit r) :
    ∃ word : List Bool, word.length ≤ bound ∧
      r = FiniteRows.encode M width (.running (initial M (pfx ++ word))) := by
  obtain ⟨word, hlen, heq⟩ := wordShaped_bits_length
    (witnessSymbols_shaped M width pfx bound fit r h)
  have hw : word.length ≤ bound := by simpa using hlen
  refine ⟨word, hw, ?_⟩
  funext slot
  rcases slot_cases slot with rfl | ⟨i, rfl⟩ | ⟨i, rfl⟩
  · exact h.1
  · simpa [Status.tape, initial, Tape.ofInput] using h.2.1 i
  · simp only [encode_right, Status.tape, initial, Tape.ofInput, List.map_append]
    have hc := h.2.2.1 i
    by_cases hp : i.val < pfx.length
    · simp only [hp, ↓reduceIte] at hc
      rw [getD_append_left (by simpa using hp)]
      exact hc
    · simp only [hp, ↓reduceIte] at hc
      rw [getD_append_right (by simpa using (by omega : pfx.length ≤ i.val))]
      simp only [List.length_map]
      by_cases hb : i.val < pfx.length + bound
      · simp only [hb, ↓reduceIte] at hc
        have hj : i.val - pfx.length < bound := by omega
        have hval := heq (i.val - pfx.length)
        rw [witnessSymbols_getD M width pfx bound fit r ⟨i.val - pfx.length, hj⟩] at hval
        have hi : (⟨pfx.length + (i.val - pfx.length), by omega⟩ : Fin width) = i := by
          apply Fin.ext; dsimp; omega
        rw [hi] at hval
        rw [← hval]
        exact (symbolValue_decode_of_mem M _ hc).symm
      · simp only [hb, ↓reduceIte] at hc
        have hout : (word.map Symbol.bit).length ≤ i.val - pfx.length := by
          simp only [List.length_map]; omega
        simpa only [List.getD, List.getElem?_eq_none hout, Option.getD_none] using hc

/-- Every satisfying initial row is precisely a fixed input prefix followed by
one binary certificate of permitted length, with blank cells elsewhere. -/
theorem problem_iff (M : Machine) (width : Nat) (pfx : List Bool)
    (bound : Nat) (fit : pfx.length + bound ≤ width) (r : Row M width) :
    Satisfied r (problem M width pfx bound fit) ↔
      ∃ word : List Bool, word.length ≤ bound ∧
        r = FiniteRows.encode M width
          ((Status.running (initial M (pfx ++ word))).window width) := by
  rw [problem_correct]
  constructor
  · intro h
    obtain ⟨word, hw, heq⟩ := conditions_initial M width pfx bound fit r h
    exact ⟨word, hw, (encode_window M width _).symm ▸ heq⟩
  · rintro ⟨word, hw, rfl⟩
    rw [encode_window]
    exact initial_conditions M width pfx word bound fit hw

end Complexity.InitialWord
