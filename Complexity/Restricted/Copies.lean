module

public import Complexity.Restricted.Chain
import Lean.Elab.Tactic.Omega

/-!
# Occurrence copies and implication cycles

The list-level core of the restricted-SAT reductions. The input is a list of *entries*
`(c, r, lits)`: a clause `lits` whose literal number `i` sits at the static position `c + i`
of a clause program, emitted at the dynamic *slot* `r`. Distinct entries own distinct
position–slot pairs.

Every literal occurrence `⟨v, s⟩` at position `p` and slot `r` is replaced by the negative
literal of a copy variable `wVal v p r`, which stands for `x_v` if `s` is negative and for
`¬x_v` if `s` is positive. Long clauses are split by implication chains with chain variables
`zVal q r`. For every variable `v < N`, a cycle of two-literal implications through all
positions and slots forces all copies of `v` to agree. The resulting formula `output` is
equisatisfiable with the clauses of the entries, its clauses have two or three literals on
distinct variables, and (see `Complexity.Restricted.Counting`) every variable occurs at most
once positively and at most twice negatively.
-/

@[expose] public section

namespace Complexity.Restricted

open Complexity.SAT

/-- The copy of variable `v` at literal position `p` and slot `r` (even). -/
def wVal (Pt R v p r : Nat) : Nat := 2 * ((v * Pt + p) * R + r)

/-- The chain variable of literal position `q` and slot `r` (odd). -/
def zVal (R q r : Nat) : Nat := 2 * (q * R + r) + 1

theorem divR {q r R : Nat} (h : r < R) : (q * R + r) / R = q := by
  rw [Nat.add_comm, Nat.add_mul_div_right r q (by omega), Nat.div_eq_of_lt h, Nat.zero_add]

theorem modR {q r R : Nat} (h : r < R) : (q * R + r) % R = r := by
  rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt h]

theorem wVal_mod_two (Pt R v p r : Nat) : wVal Pt R v p r % 2 = 0 := by
  unfold wVal; omega

theorem wVal_div_two (Pt R v p r : Nat) : wVal Pt R v p r / 2 = (v * Pt + p) * R + r := by
  unfold wVal; omega

theorem zVal_mod_two (R q r : Nat) : zVal R q r % 2 = 1 := by
  unfold zVal; omega

theorem zVal_div_two (R q r : Nat) : zVal R q r / 2 = q * R + r := by
  unfold zVal; omega

theorem wVal_ne_zVal (Pt R v p r q r' : Nat) : wVal Pt R v p r ≠ zVal R q r' := by
  unfold wVal zVal; omega

theorem wVal_inj {Pt R v p r v' p' r' : Nat} (hp : p < Pt) (hp' : p' < Pt) (hr : r < R)
    (hr' : r' < R) (h : wVal Pt R v p r = wVal Pt R v' p' r') : v = v' ∧ p = p' ∧ r = r' := by
  have h2 : (v * Pt + p) * R + r = (v' * Pt + p') * R + r' := by unfold wVal at h; omega
  have hq : v * Pt + p = v' * Pt + p' := by
    have := congrArg (· / R) h2
    simpa only [divR hr, divR hr'] using this
  have hrr : r = r' := by
    have := congrArg (· % R) h2
    simpa only [modR hr, modR hr'] using this
  have hpp : p = p' := by
    have := congrArg (· % Pt) hq
    simpa only [Nat.mul_comm v Pt, Nat.mul_comm v' Pt, Nat.mul_add_mod, Nat.mod_eq_of_lt hp,
      Nat.mod_eq_of_lt hp'] using this
  have hvv : v = v' := by
    have := congrArg (· / Pt) hq
    have hPt : 0 < Pt := by omega
    simp only [Nat.mul_comm v Pt, Nat.mul_comm v' Pt] at this
    rwa [Nat.mul_add_div hPt, Nat.mul_add_div hPt, Nat.div_eq_of_lt hp, Nat.div_eq_of_lt hp',
      Nat.add_zero, Nat.add_zero] at this
  exact ⟨hvv, hpp, hrr⟩

theorem zVal_inj {R q r q' r' : Nat} (hr : r < R) (hr' : r' < R)
    (h : zVal R q r = zVal R q' r') : q = q' ∧ r = r' := by
  have h2 : q * R + r = q' * R + r' := by unfold zVal at h; omega
  constructor
  · have := congrArg (· / R) h2
    simpa only [divR hr, divR hr'] using this
  · have := congrArg (· % R) h2
    simpa only [modR hr, modR hr'] using this

/-- An emitted clause: its first literal position, its slot, and its literals. -/
abbrev Entry := Nat × Nat × Clause

/-- The negative copy literals of a clause whose first literal sits at position `p`. -/
def copiesV (Pt R r : Nat) : Nat → Clause → Clause
  | _, [] => []
  | p, l :: ls => ⟨wVal Pt R l.var p r, false⟩ :: copiesV Pt R r (p + 1) ls

@[simp] theorem copiesV_length (Pt R r p : Nat) (lits : Clause) :
    (copiesV Pt R r p lits).length = lits.length := by
  induction lits generalizing p with
  | nil => rfl
  | cons l ls ih => simp [copiesV, ih]

def zpV (R c r j : Nat) : Literal := ⟨zVal R (c + j) r, true⟩
def znV (R c r j : Nat) : Literal := ⟨zVal R (c + j) r, false⟩

/-- The clauses replacing one entry. -/
def gadgetVal (Pt R : Nat) (e : Entry) : CNF :=
  gadget (zpV R e.1 e.2.1) (znV R e.1 e.2.1) (copiesV Pt R e.2.1 e.1 e.2.2)

/-- The successor of a position–slot pair in the cycle order. -/
def nextSlot (Pt R p r : Nat) : Nat × Nat :=
  if r + 2 ≤ R then (p, r + 1) else ((p + 1) % Pt, 0)

/-- The implication from the copy of `v` at `(p, r)` to the copy at the next pair. -/
def cycleClause (Pt R : Nat) (σ : Nat → Bool) (v p r : Nat) : Clause :=
  [⟨wVal Pt R v p r, σ p⟩,
    ⟨wVal Pt R v (nextSlot Pt R p r).1 (nextSlot Pt R p r).2, !σ (nextSlot Pt R p r).1⟩]

/-- All implication cycles, in the order of the emitting program. -/
def cyclesVal (N Pt R : Nat) (σ : Nat → Bool) : CNF :=
  (List.range N).reverse.flatMap (fun v => (List.range Pt).flatMap (fun p =>
    (List.range R).reverse.map (fun r => cycleClause Pt R σ v p r)))

theorem mem_cyclesVal {N Pt R : Nat} {σ : Nat → Bool} {c : Clause} :
    c ∈ cyclesVal N Pt R σ ↔ ∃ v < N, ∃ p < Pt, ∃ r < R, c = cycleClause Pt R σ v p r := by
  simp only [cyclesVal, List.mem_flatMap, List.mem_reverse, List.mem_range, List.mem_map]
  constructor
  · rintro ⟨v, hv, p, hp, r, hr, rfl⟩
    exact ⟨v, hv, p, hp, r, hr, rfl⟩
  · rintro ⟨v, hv, p, hp, r, hr, rfl⟩
    exact ⟨v, hv, p, hp, r, hr, rfl⟩

/-- `e` owns literal position `p` at slot `r`. -/
def owns (p r : Nat) (e : Entry) : Bool :=
  decide (e.1 ≤ p ∧ p < e.1 + e.2.2.length ∧ e.2.1 = r)

/-- The signs of the literals of a clause starting at position `p` are given by `σ`. -/
def SignsFrom (σ : Nat → Bool) : Nat → Clause → Prop
  | _, [] => True
  | p, l :: ls => l.positive = σ p ∧ SignsFrom σ (p + 1) ls

/-- Well-formed entry lists. -/
structure WF (Pt R N : Nat) (σ : Nat → Bool) (L : List Entry) : Prop where
  len : ∀ e ∈ L, 2 ≤ e.2.2.length
  pos : ∀ e ∈ L, e.1 + e.2.2.length ≤ Pt
  slot : ∀ e ∈ L, e.2.1 < R
  var : ∀ e ∈ L, ∀ l ∈ e.2.2, l.var < N
  sign : ∀ e ∈ L, SignsFrom σ e.1 e.2.2
  unique : ∀ p r, L.countP (owns p r) ≤ 1

/-- The transformed formula. -/
def output (Pt R N : Nat) (σ : Nat → Bool) (L : List Entry) : CNF :=
  L.flatMap (gadgetVal Pt R) ++ cyclesVal N Pt R σ

theorem find?_owner {L : List Entry} {p r : Nat} (hu : L.countP (owns p r) ≤ 1) {e : Entry}
    (he : e ∈ L) (ho : owns p r e = true) : L.find? (owns p r) = some e := by
  induction L with
  | nil => simp at he
  | cons x xs ih =>
    cases hx : owns p r x with
    | true =>
      rw [List.find?_cons_of_pos hx]
      rcases List.mem_cons.mp he with h | h
      · rw [h]
      · exfalso
        have h1 : 0 < xs.countP (owns p r) := List.countP_pos_iff.mpr ⟨e, h, ho⟩
        rw [List.countP_cons, hx] at hu
        simp only [↓reduceIte] at hu
        omega
    | false =>
      rw [List.find?_cons_of_neg (by simp [hx])]
      rcases List.mem_cons.mp he with h | h
      · subst h; rw [ho] at hx; cases hx
      · rw [List.countP_cons, hx] at hu
        exact ih (by simpa using hu) h

/-! ### Satisfying the output from a satisfying assignment -/

/-- The assignment of the output induced by an assignment of the input. -/
def liftAssign (Pt R : Nat) (σ : Nat → Bool) (L : List Entry) (a : Assignment) : Assignment :=
  fun u =>
    if u % 2 = 0 then
      (if σ (u / 2 / R % Pt) then !(a (u / 2 / R / Pt)) else a (u / 2 / R / Pt))
    else
      match L.find? (owns (u / 2 / R) (u / 2 % R)) with
      | none => false
      | some e => !((e.2.2.take (u / 2 / R - e.1 + 1)).any (evalLiteral a))

theorem liftAssign_w {Pt R : Nat} (σ : Nat → Bool) (L : List Entry) (a : Assignment)
    {v p r : Nat} (hp : p < Pt) (hr : r < R) :
    liftAssign Pt R σ L a (wVal Pt R v p r) = if σ p then !(a v) else a v := by
  have hPt : 0 < Pt := by omega
  have h1 : (v * Pt + p) % Pt = p := by
    rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hp]
  have h2 : (v * Pt + p) / Pt = v := by
    rw [Nat.mul_comm, Nat.mul_add_div hPt, Nat.div_eq_of_lt hp, Nat.add_zero]
  simp only [liftAssign, wVal_mod_two, wVal_div_two, divR hr, h1, h2, ite_true]

theorem liftAssign_z {Pt R : Nat} (σ : Nat → Bool) (L : List Entry) (a : Assignment)
    {q r : Nat} (hr : r < R) :
    liftAssign Pt R σ L a (zVal R q r) =
      match L.find? (owns q r) with
      | none => false
      | some e => !((e.2.2.take (q - e.1 + 1)).any (evalLiteral a)) := by
  simp only [liftAssign, zVal_mod_two, zVal_div_two, divR hr, modR hr]
  rfl

/-- The values of the copy literals agree with the values of the original literals. -/
theorem copiesV_map_eval (Pt R r : Nat) (σ : Nat → Bool) (a' b : Assignment) :
    ∀ (lits : Clause) (p : Nat), SignsFrom σ p lits →
      (∀ l ∈ lits, ∀ q, p ≤ q → q < p + lits.length →
        evalLiteral a' ⟨wVal Pt R l.var q r, false⟩ = (if σ q then b l.var else !(b l.var))) →
      (copiesV Pt R r p lits).map (evalLiteral a') = lits.map (evalLiteral b) := by
  intro lits
  induction lits with
  | nil => intro p _ _; rfl
  | cons l ls ih =>
    intro p hs h
    simp only [SignsFrom] at hs
    simp only [copiesV, List.map_cons]
    congr 1
    · rw [h l (by simp) p (Nat.le_refl p) (by simp)]
      rcases l with ⟨v, s⟩
      have hs1 : s = σ p := hs.1
      subst hs1
      cases σ p <;> simp [evalLiteral]
    · apply ih (p + 1) hs.2
      intro l' hl' q hq1 hq2
      exact h l' (by simp [hl']) q (by omega) (by simp; omega)

theorem any_eq_of_map_eq {α β : Type} {f : α → Bool} {g : β → Bool} {xs : List α} {ys : List β}
    (h : xs.map f = ys.map g) : xs.any f = ys.any g := by
  have h1 : xs.any f = (xs.map f).any id := by simp [List.any_map]
  have h2 : ys.any g = (ys.map g).any id := by simp [List.any_map]
  rw [h1, h2, h]

theorem take_any_eq_of_map_eq {α β : Type} {f : α → Bool} {g : β → Bool} {xs : List α}
    {ys : List β} (h : xs.map f = ys.map g) (n : Nat) :
    (xs.take n).any f = (ys.take n).any g := by
  apply any_eq_of_map_eq
  rw [List.map_take, List.map_take, h]

theorem evalLiteral_flip (a : Assignment) (u : Nat) (s : Bool) :
    evalLiteral a ⟨u, s⟩ = !evalLiteral a ⟨u, !s⟩ := by
  cases s <;> simp [evalLiteral]

theorem nextSlot_lt {Pt R p r : Nat} (hp : p < Pt) (hR : 0 < R) :
    (nextSlot Pt R p r).1 < Pt ∧ (nextSlot Pt R p r).2 < R := by
  unfold nextSlot
  split
  · exact ⟨hp, by omega⟩
  · exact ⟨Nat.mod_lt _ (by omega), hR⟩

theorem evalLiteral_mk (a : Assignment) (u : Nat) (s : Bool) :
    evalLiteral a ⟨u, s⟩ = if s then a u else !(a u) := rfl

theorem evalClause_eq_any (a : Assignment) (c : Clause) :
    evalClause a c = c.any (evalLiteral a) := rfl

theorem exists_copies_cons (Pt R r c0 : Nat) {lits : Clause} (hlen : 2 ≤ lits.length) :
    ∃ m0 ms', copiesV Pt R r c0 lits = m0 :: ms' ∧ ms'.length + 1 = lits.length := by
  cases lits with
  | nil => simp at hlen
  | cons l ls => exact ⟨_, _, rfl, by simp⟩

theorem gadget_complete {Pt R N : Nat} {σ : Nat → Bool} {L : List Entry}
    (hWF : WF Pt R N σ L) (a : Assignment) {e : Entry} (he : e ∈ L)
    (hsat : evalClause a e.2.2 = true) :
    ∀ c ∈ gadgetVal Pt R e, evalClause (liftAssign Pt R σ L a) c = true := by
  obtain ⟨c0, r, lits⟩ := e
  have hlen := hWF.len _ he
  have hpos := hWF.pos _ he
  have hr := hWF.slot _ he
  have hsign := hWF.sign _ he
  simp only at hlen hpos hr hsign hsat
  have hmap : (copiesV Pt R r c0 lits).map (evalLiteral (liftAssign Pt R σ L a)) =
      lits.map (evalLiteral a) := by
    apply copiesV_map_eval Pt R r σ _ a lits c0 hsign
    intro l _ q hq1 hq2
    rw [evalLiteral_mk, liftAssign_w σ L a (by omega) hr]
    cases σ q <;> simp
  obtain ⟨m0, ms', hms, hlen'⟩ := exists_copies_cons Pt R r c0 hlen
  have hgad : gadgetVal Pt R (c0, r, lits) = chainFrom (zpV R c0 r) (znV R c0 r) m0 ms' 1 := by
    simp only [gadgetVal, hms, gadget]
  rw [hgad]
  rw [hms] at hmap
  intro c hc
  rw [evalClause_eq_any]
  refine chainFrom_complete (evalLiteral (liftAssign Pt R σ L a)) (zpV R c0 r) (znV R c0 r)
    m0 ms' 1 ?_ ?_ c hc
  · intro i hi
    have hown : owns (c0 + (1 + i)) r (c0, r, lits) = true := by
      simp [owns]; omega
    have hfind := find?_owner (hWF.unique _ _) he hown
    have hz : liftAssign Pt R σ L a (zVal R (c0 + (1 + i)) r) =
        !((lits.take (i + 2)).any (evalLiteral a)) := by
      rw [liftAssign_z σ L a hr, hfind]
      have e1 : c0 + (1 + i) - c0 + 1 = i + 2 := by omega
      simp only [e1]
    have hpre : (evalLiteral (liftAssign Pt R σ L a) m0 ||
        (ms'.take (i + 1)).any (evalLiteral (liftAssign Pt R σ L a))) =
        (lits.take (i + 2)).any (evalLiteral a) := by
      have := take_any_eq_of_map_eq hmap (i + 2)
      simpa [List.take_succ_cons] using this
    simp only [zpV, znV, evalLiteral_mk, ite_true, Bool.false_eq_true, ite_false]
    rw [hpre, hz]
    simp
  · have := any_eq_of_map_eq hmap
    simp only [List.any_cons] at this
    rw [this]
    exact hsat

theorem cycle_complete {Pt R : Nat} (σ : Nat → Bool) (L : List Entry) (hR : 0 < R)
    (a : Assignment) {v p r : Nat} (hp : p < Pt) (hr : r < R) :
    evalClause (liftAssign Pt R σ L a) (cycleClause Pt R σ v p r) = true := by
  obtain ⟨h1, h2⟩ := nextSlot_lt (Pt := Pt) (R := R) (p := p) (r := r) hp hR
  simp only [cycleClause, evalClause_cons, evalClause_nil, Bool.or_false, evalLiteral_mk]
  rw [liftAssign_w σ L a hp hr, liftAssign_w σ L a h1 h2]
  cases σ p <;> cases σ (nextSlot Pt R p r).1 <;> cases a v <;> rfl

theorem output_complete {Pt R N : Nat} {σ : Nat → Bool} {L : List Entry}
    (hWF : WF Pt R N σ L) (hR : 0 < R) (a : Assignment)
    (ha : ∀ e ∈ L, evalClause a e.2.2 = true) :
    ∀ c ∈ output Pt R N σ L, evalClause (liftAssign Pt R σ L a) c = true := by
  intro c hc
  simp only [output, List.mem_append, List.mem_flatMap] at hc
  rcases hc with ⟨e, he, hc⟩ | hc
  · exact gadget_complete hWF a he (ha e he) c hc
  · obtain ⟨v, _, p, hp, r, hr, rfl⟩ := mem_cyclesVal.mp hc
    exact cycle_complete σ L hR a hp hr

/-! ### Reading a satisfying assignment of the input from one of the output -/

/-- The assignment of the input read from the copies at position `0`, slot `0`. -/
def lowerAssign (Pt R : Nat) (σ : Nat → Bool) (a' : Assignment) : Assignment :=
  fun v => evalLiteral a' ⟨wVal Pt R v 0 0, !σ 0⟩

/-- A cycle of implications through all position–slot pairs forces equal values. -/
theorem cycle_const (Pt R : Nat) (hR : 0 < R) (T : Nat → Nat → Bool)
    (step : ∀ p < Pt, ∀ r < R, T p r = true →
      T (nextSlot Pt R p r).1 (nextSlot Pt R p r).2 = true) :
    ∀ p < Pt, ∀ r < R, T p r = T 0 0 := by
  have row : ∀ p < Pt, T p 0 = true → ∀ r < R, T p r = true := by
    intro p hp h0 r
    induction r with
    | zero => intro _; exact h0
    | succ r ih =>
      intro hr
      have hs := step p hp r (by omega) (ih (by omega))
      simpa [nextSlot, show r + 2 ≤ R by omega] using hs
  have fwd : T 0 0 = true → ∀ p < Pt, T p 0 = true := by
    intro h00 p
    induction p with
    | zero => intro _; exact h00
    | succ p ih =>
      intro hp
      have hlast := row p (by omega) (ih (by omega)) (R - 1) (by omega)
      have hs := step p (by omega) (R - 1) (by omega) hlast
      have hn : ¬ (R - 1 + 2 ≤ R) := by omega
      simpa [nextSlot, hn, Nat.mod_eq_of_lt hp] using hs
  have rowEnd : ∀ p < Pt, ∀ k r, r + k = R - 1 → T p r = true → T p (R - 1) = true := by
    intro p hp k
    induction k with
    | zero => intro r hr h; rw [← hr]; simpa using h
    | succ k ih =>
      intro r hr h
      have hs := step p hp r (by omega) h
      have hs' : T p (r + 1) = true := by simpa [nextSlot, show r + 2 ≤ R by omega] using hs
      exact ih (r + 1) (by omega) hs'
  have bwd : ∀ k p, p + k = Pt - 1 → p < Pt → T p (R - 1) = true →
      T (Pt - 1) (R - 1) = true := by
    intro k
    induction k with
    | zero => intro p hp _ h; rw [← hp]; simpa using h
    | succ k ih =>
      intro p hp hlt h
      have hs := step p hlt (R - 1) (by omega) h
      have hn : ¬ (R - 1 + 2 ≤ R) := by omega
      have hs' : T (p + 1) 0 = true := by
        simpa [nextSlot, hn, Nat.mod_eq_of_lt (show p + 1 < Pt by omega)] using hs
      exact ih (p + 1) (by omega) (by omega)
        (rowEnd (p + 1) (by omega) (R - 1) 0 (by omega) hs')
  intro p hp r hr
  cases h00 : T 0 0 with
  | true => exact row p hp (fwd h00 p hp) r hr
  | false =>
    cases hpr : T p r with
    | false => rfl
    | true =>
      exfalso
      have h1 := rowEnd p hp (R - 1 - r) r (by omega) hpr
      have h2 := bwd (Pt - 1 - p) p (by omega) hp h1
      have hs := step (Pt - 1) (by omega) (R - 1) (by omega) h2
      have hn : ¬ (R - 1 + 2 ≤ R) := by omega
      have hm : (Pt - 1 + 1) % Pt = 0 := by
        rw [show Pt - 1 + 1 = Pt by omega, Nat.mod_self]
      simp [nextSlot, hn, hm, h00] at hs

theorem output_sound {Pt R N : Nat} {σ : Nat → Bool} {L : List Entry}
    (hWF : WF Pt R N σ L) (hR : 0 < R) (a' : Assignment)
    (h : ∀ c ∈ output Pt R N σ L, evalClause a' c = true) :
    ∀ e ∈ L, evalClause (lowerAssign Pt R σ a') e.2.2 = true := by
  have hconst : ∀ v < N, ∀ p < Pt, ∀ r < R,
      evalLiteral a' ⟨wVal Pt R v p r, !σ p⟩ = lowerAssign Pt R σ a' v := by
    intro v hv
    apply cycle_const Pt R hR (fun p r => evalLiteral a' ⟨wVal Pt R v p r, !σ p⟩)
    intro p hp r hr hT
    have hc := h (cycleClause Pt R σ v p r)
      (by simp only [output, List.mem_append]; exact Or.inr (mem_cyclesVal.mpr ⟨v, hv, p, hp, r, hr, rfl⟩))
    simp only [cycleClause, evalClause_cons, evalClause_nil, Bool.or_false] at hc
    rw [evalLiteral_flip a' _ (σ p), hT] at hc
    simpa using hc
  intro e he
  obtain ⟨c0, r, lits⟩ := e
  have hlen := hWF.len _ he
  have hpos := hWF.pos _ he
  have hr := hWF.slot _ he
  have hsign := hWF.sign _ he
  have hvar := hWF.var _ he
  simp only at hlen hpos hr hsign hvar ⊢
  have hmap : (copiesV Pt R r c0 lits).map (evalLiteral a') =
      lits.map (evalLiteral (lowerAssign Pt R σ a')) := by
    apply copiesV_map_eval Pt R r σ a' _ lits c0 hsign
    intro l hl q hq1 hq2
    rw [← hconst l.var (hvar l hl) q (by omega) r hr]
    cases σ q <;> simp [evalLiteral_mk]
  obtain ⟨m0, ms', hms, hlen'⟩ := exists_copies_cons Pt R r c0 hlen
  have hgad : gadgetVal Pt R (c0, r, lits) = chainFrom (zpV R c0 r) (znV R c0 r) m0 ms' 1 := by
    simp only [gadgetVal, hms, gadget]
  have hall : ∀ c ∈ chainFrom (zpV R c0 r) (znV R c0 r) m0 ms' 1, c.any (evalLiteral a') = true := by
    intro c hc
    rw [← evalClause_eq_any]
    apply h c
    simp only [output, List.mem_append, List.mem_flatMap]
    exact Or.inl ⟨(c0, r, lits), he, by rw [hgad]; exact hc⟩
  have hs := chainFrom_sound (evalLiteral a') (zpV R c0 r) (znV R c0 r)
    (by intro i; simp [zpV, znV, evalLiteral_mk]) m0 ms' 1 hall
  rw [hms] at hmap
  have := any_eq_of_map_eq hmap
  simp only [List.any_cons] at this
  rw [evalClause_eq_any, ← this]
  exact hs

/-! ### Clause shapes -/

theorem mem_copiesV_var {Pt R r : Nat} :
    ∀ (lits : Clause) (p x : Nat), x ∈ (copiesV Pt R r p lits).map Literal.var →
      ∃ v q, p ≤ q ∧ q < p + lits.length ∧ x = wVal Pt R v q r := by
  intro lits
  induction lits with
  | nil => intro p x hx; simp [copiesV] at hx
  | cons l ls ih =>
    intro p x hx
    simp only [copiesV, List.map_cons, List.mem_cons] at hx
    rcases hx with hx | hx
    · exact ⟨l.var, p, Nat.le_refl p, by simp, hx⟩
    · obtain ⟨v, q, h1, h2, h3⟩ := ih (p + 1) x hx
      exact ⟨v, q, by omega, by simp; omega, h3⟩

theorem copiesV_vars_nodup {Pt R r : Nat} (hr : r < R) :
    ∀ (lits : Clause) (p : Nat), p + lits.length ≤ Pt →
      ((copiesV Pt R r p lits).map Literal.var).Nodup := by
  intro lits
  induction lits with
  | nil => intro p _; simp [copiesV]
  | cons l ls ih =>
    intro p hp
    simp only [List.length_cons] at hp
    simp only [copiesV, List.map_cons]
    refine List.nodup_cons.mpr ⟨?_, ih (p + 1) (by omega)⟩
    intro hx
    obtain ⟨v, q, h1, h2, h3⟩ := mem_copiesV_var ls (p + 1) _ hx
    have := (wVal_inj (by omega) (by omega) hr hr h3).2.1
    omega

theorem gadget_shape {Pt R N : Nat} {σ : Nat → Bool} {L : List Entry}
    (hWF : WF Pt R N σ L) {e : Entry} (he : e ∈ L) :
    ∀ c ∈ gadgetVal Pt R e, (c.length = 2 ∨ c.length = 3) ∧ (c.map Literal.var).Nodup := by
  obtain ⟨c0, r, lits⟩ := e
  have hlen := hWF.len _ he
  have hpos := hWF.pos _ he
  have hr := hWF.slot _ he
  simp only at hlen hpos hr
  obtain ⟨m0, ms', hms, hlen'⟩ := exists_copies_cons Pt R r c0 hlen
  have hgad : gadgetVal Pt R (c0, r, lits) = chainFrom (zpV R c0 r) (znV R c0 r) m0 ms' 1 := by
    simp only [gadgetVal, hms, gadget]
  rw [hgad]
  intro c hc
  constructor
  · apply chainFrom_length _ _ m0 ms' 1 _ c hc
    intro h
    rw [h] at hlen'
    simp at hlen'
    omega
  · have hnd := copiesV_vars_nodup hr lits c0 hpos
    rw [hms] at hnd
    refine chainFrom_nodup Literal.var (zpV R c0 r) (znV R c0 r) (fun _ => rfl) ?_ m0 ms' 1 hnd
      ?_ c hc
    · intro i i' h
      have := (zVal_inj hr hr h).1
      omega
    · intro i _ hx
      rw [← hms] at hx
      obtain ⟨v, q, _, _, h3⟩ := mem_copiesV_var lits c0 _ hx
      exact wVal_ne_zVal Pt R v q r (c0 + i) r h3.symm

theorem cycle_shape {Pt R : Nat} (σ : Nat → Bool) (hR : 2 ≤ R) {v p r : Nat} (hp : p < Pt)
    (hr : r < R) :
    (cycleClause Pt R σ v p r).length = 2 ∧
      ((cycleClause Pt R σ v p r).map Literal.var).Nodup := by
  obtain ⟨h1, h2⟩ := nextSlot_lt (Pt := Pt) (R := R) (p := p) (r := r) hp (by omega)
  refine ⟨rfl, ?_⟩
  simp only [cycleClause, List.map_cons, List.map_nil, List.nodup_cons, List.mem_cons,
    List.not_mem_nil, or_false, List.nodup_nil, and_true, not_false_eq_true]
  intro h
  have := wVal_inj hp h1 hr h2 h
  unfold nextSlot at this
  split at this
  · simp at this
  · simp at this
    omega

theorem output_shape {Pt R N : Nat} {σ : Nat → Bool} {L : List Entry}
    (hWF : WF Pt R N σ L) (hR : 2 ≤ R) :
    ∀ c ∈ output Pt R N σ L, (c.length = 2 ∨ c.length = 3) ∧ (c.map Literal.var).Nodup := by
  intro c hc
  simp only [output, List.mem_append, List.mem_flatMap] at hc
  rcases hc with ⟨e, he, hc⟩ | hc
  · exact gadget_shape hWF he c hc
  · obtain ⟨v, _, p, hp, r, hr, rfl⟩ := mem_cyclesVal.mp hc
    obtain ⟨h1, h2⟩ := cycle_shape σ hR (v := v) hp hr
    exact ⟨Or.inl h1, h2⟩

end Complexity.Restricted
