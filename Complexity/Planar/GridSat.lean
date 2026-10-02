module

public import Complexity.Planar.GridComb
import Lean.Elab.Tactic.Omega

/-!
# Satisfiability of the grid formula

The grid formula `gridCNF W m bits` is satisfiable exactly when some assignment `a` satisfies,
for every clause `j < m`, the literal of some variable `v < W` that occurs in it according to
`bits j v`.

In a satisfying assignment of the grid formula the crossover forces the outgoing copy of a
variable to equal the incoming one and the chain after a cell to equal the chain after its
literal; rainbows equate copies in consecutive columns, so all copies of `v` carry one value
`a v`; the chain of a column starts false and ends true, so it switches in some cell, whose
literal is then satisfied.  Conversely the chain of a column can be set false up to the first
satisfied literal and true afterwards, and the crossover variables are determined.
-/

@[expose] public section

namespace Complexity.Planar.Grid

open SAT

/-! ## Local semantics of the templates -/

/-- A template clause under local values of the spine positions. -/
def evalT (L : Nat → Bool) (t : TCl) : Bool := t.1.any fun p => if p.2 then L p.1 else !L p.1

theorem evalClause_inst (g : Assignment) (o : Nat) (odd : Bool) (t : TCl) :
    evalClause g (inst o odd t) = evalT (fun p => g (o + p)) t := by
  unfold evalClause inst evalT
  split <;> simp [List.any_map, Function.comp_def, evalLiteral]

/-- Whether the literal of a variable with value `x` occurs, given the occurrence bits. -/
def litSat (bp bn x : Bool) : Bool := bp && x || bn && !x

/-- Values of the ten positions of a cell. -/
def cellVals (cin x cmid : Bool) : List Bool :=
  [cin, x, cmid, x && cmid, x && !cmid, !x && !cmid, !x, !x && cmid, x, cmid]

theorem cell_complete : ∀ bp bn cin x : Bool, ∀ t ∈ cellT bp bn,
    evalT (fun p => (cellVals cin x (cin || litSat bp bn x)).getD p false) t = true := by
  decide

theorem cross_sound : ∀ b1 b2 b3 b4 b5 b6 b7 b8 b9 : Bool, ∀ b0 : Bool,
    (∀ t ∈ crossT, evalT (fun p => [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9].getD p false) t = true) →
      b8 = b1 ∧ b9 = b2 := by
  decide

theorem or_sound : ∀ bp bn b0 b1 b2 b3 b4 b5 b6 b7 : Bool,
    (∀ t ∈ orT bp bn,
      evalT (fun p => [b0, b1, b2, b3, b4, b5, b6, b7, b1, b2].getD p false) t = true) →
      b0 = false → b2 = true → litSat bp bn b1 = true := by
  decide


theorem any_congr_mem {α : Type} {l : List α} {f g : α → Bool} (h : ∀ x ∈ l, f x = g x) :
    l.any f = l.any g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.any_cons, h a List.mem_cons_self,
      ih (fun x hx => h x (List.mem_cons_of_mem _ hx))]

theorem getD_ten (L : Nat → Bool) {q : Nat} (hq : q < 10) :
    L q = [L 0, L 1, L 2, L 3, L 4, L 5, L 6, L 7, L 8, L 9].getD q false := by
  match q, hq with
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rfl
  | 4, _ => rfl
  | 5, _ => rfl
  | 6, _ => rfl
  | 7, _ => rfl
  | 8, _ => rfl
  | 9, _ => rfl
  | q + 10, h => exact absurd h (by omega)

/-- Templates read only the first ten positions. -/
theorem evalT_congr {L L' : Nat → Bool} {t : TCl} (ht : ∀ p ∈ tpos t, p < 10)
    (h : ∀ p, p < 10 → L p = L' p) : evalT L t = evalT L' t := by
  unfold evalT
  apply any_congr_mem
  intro x hx
  have : x.1 < 10 := ht _ (List.mem_map.mpr ⟨x, hx, rfl⟩)
  rw [h _ this]

theorem pos_lt_ten {bp bn : Bool} {t : TCl} (ht : t ∈ cellT bp bn) : ∀ p ∈ tpos t, p < 10 :=
  (cellT_shape bp bn t ht).2.2.2.1

/-- What the clauses of a cell force. -/
theorem cell_sound {bp bn : Bool} (L : Nat → Bool) (h : ∀ t ∈ cellT bp bn, evalT L t = true) :
    L 8 = L 1 ∧ L 9 = L 2 ∧ (L 0 = false → L 2 = true → litSat bp bn (L 1) = true) := by
  have hc : ∀ t ∈ crossT,
      evalT (fun p => [L 0, L 1, L 2, L 3, L 4, L 5, L 6, L 7, L 8, L 9].getD p false) t = true := by
    intro t ht
    have ht' : t ∈ cellT bp bn := List.mem_append_right _ ht
    rw [← h t ht']
    exact evalT_congr (pos_lt_ten ht') (fun p hp => (getD_ten L hp).symm)
  obtain ⟨h81, h92⟩ := cross_sound (L 1) (L 2) (L 3) (L 4) (L 5) (L 6) (L 7) (L 8) (L 9) (L 0) hc
  refine ⟨h81, h92, ?_⟩
  apply or_sound bp bn (L 0) (L 1) (L 2) (L 3) (L 4) (L 5) (L 6) (L 7)
  intro t ht
  have ht' : t ∈ cellT bp bn := List.mem_append_left _ ht
  have := h t ht'
  rw [evalT_congr (pos_lt_ten ht') (fun p hp => getD_ten L hp), h81, h92] at this
  exact this

/-! ## Membership in the grid formula -/

/-- The parity of a column. -/
def par (j : Nat) : Bool := j % 2 == 1

theorem par_even (k : Nat) : par (2 * k) = false := by
  unfold par; rw [show 2 * k % 2 = 0 by omega]; rfl

theorem par_odd (k : Nat) : par (2 * k + 1) = true := by
  unfold par; rw [show (2 * k + 1) % 2 = 1 by omega]; rfl

theorem column_mem {W m j : Nat} {bits : Nat → Nat → Bool × Bool} (hj : j < m) {c : Clause}
    (hc : c ∈ column W j (par j) bits) : c ∈ gridCNF W m bits := by
  rw [gridCNF_eq]
  simp only [List.mem_append]
  obtain ⟨k, rfl | rfl⟩ : ∃ k, j = 2 * k ∨ j = 2 * k + 1 := ⟨j / 2, by omega⟩
  · rw [par_even] at hc
    exact Or.inl (Or.inl (Or.inl (mem_colsE.mpr ⟨k, by omega, hc⟩)))
  · rw [par_odd] at hc
    exact Or.inl (Or.inl (Or.inr (mem_colsO.mpr ⟨k, by omega, hc⟩)))

theorem rbEven_mem {W m k v : Nat} {bits : Nat → Nat → Bool × Bool} (hk : 2 * k + 2 ≤ m)
    (hv : v < W) {c : Clause} (hc : c ∈ rbEven W (2 * k) v) : c ∈ gridCNF W m bits := by
  rw [gridCNF_eq]
  simp only [List.mem_append]
  exact Or.inl (Or.inr (mem_rbsE.mpr ⟨k, hk, v, hv, hc⟩))

theorem rbOdd_mem {W m k v : Nat} {bits : Nat → Nat → Bool × Bool} (hk : 2 * k + 3 ≤ m)
    (hv : v < W) {c : Clause} (hc : c ∈ rbOdd W (2 * k + 1) v) : c ∈ gridCNF W m bits := by
  rw [gridCNF_eq]
  simp only [List.mem_append]
  exact Or.inr (mem_rbsO.mpr ⟨k, hk, v, hv, hc⟩)

theorem cell_mem {W j idx : Nat} {odd : Bool} {bits : Nat → Nat → Bool × Bool} (hidx : idx < W)
    {t : TCl} (ht : t ∈ cellT (bits j (row W odd idx)).1 (bits j (row W odd idx)).2) :
    inst (cellOff W j idx) odd t ∈ column W j odd bits := by
  unfold column
  simp only [List.mem_append, List.mem_flatMap, List.mem_reverse, List.mem_range]
  exact Or.inl (Or.inr ⟨idx, hidx, by unfold cellCNF; exact List.mem_map.mpr ⟨t, ht, rfl⟩⟩)

theorem start_mem {W j : Nat} {odd : Bool} {bits : Nat → Nat → Bool × Bool} {c : Clause}
    (hc : c ∈ startG W j) : c ∈ column W j odd bits := by
  unfold column
  exact List.mem_append_left _ (List.mem_append_left _ hc)

theorem end_mem {W j : Nat} {odd : Bool} {bits : Nat → Nat → Bool × Bool} {c : Clause}
    (hc : c ∈ endG W j) : c ∈ column W j odd bits := by
  unfold column
  exact List.mem_append_right _ hc

theorem row_true {W idx : Nat} : row W true idx = W - 1 - idx := rfl

theorem row_false {W idx : Nat} : row W false idx = idx := rfl

theorem row_lt {W : Nat} (odd : Bool) {idx : Nat} (h : idx < W) : row W odd idx < W := by
  unfold row; split <;> omega

theorem row_row {W : Nat} (odd : Bool) {idx : Nat} (h : idx < W) : row W odd (row W odd idx) = idx := by
  unfold row; split <;> omega

/-! ## Soundness -/

theorem two_equal {g : Assignment} {x y : Nat}
    (h1 : evalClause g [⟨x, false⟩, ⟨y, true⟩] = true)
    (h2 : evalClause g [⟨x, true⟩, ⟨y, false⟩] = true) : g y = g x := by
  simp only [evalClause, evalLiteral, List.any_cons, List.any_nil, Bool.or_false] at h1 h2
  cases hx : g x <;> cases hy : g y <;> simp_all

theorem two_equal' {g : Assignment} {x y : Nat}
    (h1 : evalClause g [⟨y, true⟩, ⟨x, false⟩] = true)
    (h2 : evalClause g [⟨y, false⟩, ⟨x, true⟩] = true) : g y = g x := by
  simp only [evalClause, evalLiteral, List.any_cons, List.any_nil, Bool.or_false] at h1 h2
  cases hx : g x <;> cases hy : g y <;> simp_all

theorem switch_exists (f : Nat → Bool) :
    ∀ W, f 0 = false → f W = true → ∃ i, i < W ∧ f i = false ∧ f (i + 1) = true
  | 0, h0, hW => by rw [h0] at hW; cases hW
  | W + 1, h0, hW => by
    cases h : f W
    · exact ⟨W, by omega, h, hW⟩
    · obtain ⟨i, hi, h1, h2⟩ := switch_exists f W h0 h
      exact ⟨i, by omega, h1, h2⟩

section sound

variable {W m : Nat} {bits : Nat → Nat → Bool × Bool} {g : Assignment}
  (hg : ∀ c ∈ gridCNF W m bits, evalClause g c = true)
include hg

theorem cell_local {j idx : Nat} (hj : j < m) (hidx : idx < W) :
    ∀ t ∈ cellT (bits j (row W (par j) idx)).1 (bits j (row W (par j) idx)).2,
      evalT (fun p => g (cellOff W j idx + p)) t = true := by
  intro t ht
  rw [← evalClause_inst]
  exact hg _ (column_mem hj (cell_mem hidx ht))

theorem copy_eq {j idx : Nat} (hj : j < m) (hidx : idx < W) :
    g (cellOff W j idx + 8) = g (cellOff W j idx + 1) :=
  (cell_sound _ (cell_local hg hj hidx)).1

theorem copies {j : Nat} (hj : j < m) :
    ∀ idx, idx < W → g (cellOff W j idx + 1) = g (cellOff W 0 (row W (par j) idx) + 1) := by
  induction j with
  | zero => intro idx _; rfl
  | succ j ih =>
    intro idx hidx
    obtain ⟨k, rfl | rfl⟩ : ∃ k, j = 2 * k ∨ j = 2 * k + 1 := ⟨j / 2, by omega⟩
    · -- an even column and the odd column after it
      have hv : W - 1 - idx < W := by omega
      have m1 := rbEven_mem (bits := bits) (show 2 * k + 2 ≤ m by omega) hv
        (c := [⟨cellOff W (2 * k) (W - 1 - idx) + 8, false⟩,
          ⟨cellOff W (2 * k + 1) (W - 1 - (W - 1 - idx)) + 1, true⟩]) (by simp [rbEven])
      have m2 := rbEven_mem (bits := bits) (show 2 * k + 2 ≤ m by omega) hv
        (c := [⟨cellOff W (2 * k) (W - 1 - idx) + 8, true⟩,
          ⟨cellOff W (2 * k + 1) (W - 1 - (W - 1 - idx)) + 1, false⟩]) (by simp [rbEven])
      have h := two_equal (hg _ m1) (hg _ m2)
      rw [show W - 1 - (W - 1 - idx) = idx by omega] at h
      rw [h, copy_eq hg (by omega) hv, ih (by omega) _ hv, par_even, par_odd, row_true, row_false]
    · -- an odd column and the even column after it
      have hv : W - 1 - idx < W := by omega
      have m1 := rbOdd_mem (bits := bits) (show 2 * k + 3 ≤ m by omega) hidx
        (c := [⟨cellOff W (2 * k + 1 + 1) idx + 1, true⟩,
          ⟨cellOff W (2 * k + 1) (W - 1 - idx) + 8, false⟩]) (by simp [rbOdd])
      have m2 := rbOdd_mem (bits := bits) (show 2 * k + 3 ≤ m by omega) hidx
        (c := [⟨cellOff W (2 * k + 1 + 1) idx + 1, false⟩,
          ⟨cellOff W (2 * k + 1) (W - 1 - idx) + 8, true⟩]) (by simp [rbOdd])
      have h := two_equal' (hg _ m1) (hg _ m2)
      rw [h, copy_eq hg (by omega) hv, ih (by omega) _ hv, par_odd,
        show 2 * k + 1 + 1 = 2 * (k + 1) by omega, par_even, row_true, row_false,
        show W - 1 - (W - 1 - idx) = idx by omega]

theorem start_false {j : Nat} (hj : j < m) : g (cellOff W j 0) = false := by
  have m1 := column_mem (W := W) (bits := bits) hj (start_mem (odd := par j) (bits := bits)
    (c := [⟨colBase W j, true⟩, ⟨colBase W j + 1, false⟩]) (by simp [startG]))
  have m2 := column_mem (W := W) (bits := bits) hj (start_mem (odd := par j) (bits := bits)
    (c := [⟨colBase W j + 1, false⟩, ⟨colBase W j, false⟩]) (by simp [startG]))
  have h1 := hg _ m1
  have h2 := hg _ m2
  simp only [evalClause, evalLiteral, List.any_cons, List.any_nil, Bool.or_false] at h1 h2
  have : cellOff W j 0 = colBase W j + 1 := by unfold cellOff; omega
  rw [this]
  cases hx : g (colBase W j) <;> cases hy : g (colBase W j + 1) <;> simp_all

theorem end_true {j : Nat} (hj : j < m) : g (cellOff W j W) = true := by
  have m1 := column_mem (W := W) (bits := bits) hj (end_mem (odd := par j) (bits := bits)
    (c := [⟨cellOff W j W, true⟩, ⟨cellOff W j W + 1, true⟩]) (by simp [endG]))
  have m2 := column_mem (W := W) (bits := bits) hj (end_mem (odd := par j) (bits := bits)
    (c := [⟨cellOff W j W + 1, false⟩, ⟨cellOff W j W, true⟩]) (by simp [endG]))
  have h1 := hg _ m1
  have h2 := hg _ m2
  simp only [evalClause, evalLiteral, List.any_cons, List.any_nil, Bool.or_false] at h1 h2
  cases hx : g (cellOff W j W) <;> cases hy : g (cellOff W j W + 1) <;> simp_all

/-- **Soundness**: a satisfying assignment of the grid formula satisfies every clause. -/
theorem grid_sound {j : Nat} (hj : j < m) :
    ∃ v, v < W ∧ litSat (bits j v).1 (bits j v).2 (g (cellOff W 0 v + 1)) = true := by
  obtain ⟨idx, hidx, h1, h2⟩ := switch_exists (fun i => g (cellOff W j i)) W
    (start_false hg hj) (end_true hg hj)
  have hs := cell_sound _ (cell_local hg hj hidx)
  have e9 : cellOff W j (idx + 1) = cellOff W j idx + 9 := by unfold cellOff; omega
  rw [e9] at h2
  have h3 : litSat (bits j (row W (par j) idx)).1 (bits j (row W (par j) idx)).2
      (g (cellOff W j idx + 1)) = true :=
    hs.2.2 (by simpa using h1) (by rw [← hs.2.1]; simpa using h2)
  refine ⟨row W (par j) idx, row_lt _ hidx, ?_⟩
  rw [← copies hg hj idx hidx]
  exact h3

end sound

/-! ## Completeness -/

section complete

variable (W : Nat) (bits : Nat → Nat → Bool × Bool) (a : Assignment)

/-- Whether the cell at position `idx` of column `j` sees a satisfied literal. -/
def cellSatB (j idx : Nat) : Bool :=
  litSat (bits j (row W (par j) idx)).1 (bits j (row W (par j) idx)).2 (a (row W (par j) idx))

/-- The chain variable entering cell `idx` of column `j`: some earlier cell sees a satisfied
literal. -/
def chainV (j idx : Nat) : Bool := (List.range idx).any (cellSatB W bits a j)

/-- The assignment of the grid formula built from an assignment `a` of the variables. -/
def gridAsg : Assignment := fun x =>
  if x % (9 * W + 3) = 0 ∨ x % (9 * W + 3) = 9 * W + 2 then false else
    (cellVals (chainV W bits a (x / (9 * W + 3)) ((x % (9 * W + 3) - 1) / 9))
      (a (row W (par (x / (9 * W + 3))) ((x % (9 * W + 3) - 1) / 9)))
      (chainV W bits a (x / (9 * W + 3)) ((x % (9 * W + 3) - 1) / 9 + 1))).getD
      ((x % (9 * W + 3) - 1) % 9) false

omit a in
theorem decomp {j r : Nat} (hr : r < 9 * W + 3) :
    (colBase W j + r) / (9 * W + 3) = j ∧ (colBase W j + r) % (9 * W + 3) = r := by
  unfold colBase colLen
  rw [Nat.mul_comm j, Nat.mul_add_div (by omega), Nat.mul_add_mod, Nat.div_eq_of_lt hr,
    Nat.mod_eq_of_lt hr]
  exact ⟨by omega, rfl⟩

theorem chainV_succ (j idx : Nat) :
    chainV W bits a j (idx + 1) = (chainV W bits a j idx || cellSatB W bits a j idx) := by
  unfold chainV
  rw [List.range_succ, List.any_append]
  simp

theorem gridAsg_chain {j idx : Nat} (h : idx ≤ W) :
    gridAsg W bits a (cellOff W j idx) = chainV W bits a j idx := by
  have hd := decomp W (j := j) (show 1 + 9 * idx < 9 * W + 3 by omega)
  have e : cellOff W j idx = colBase W j + (1 + 9 * idx) := by unfold cellOff; omega
  unfold gridAsg
  rw [e, hd.1, hd.2, ite_eq_right (by omega), show (1 + 9 * idx - 1) / 9 = idx by omega,
    show (1 + 9 * idx - 1) % 9 = 0 by omega]
  rfl

theorem gridAsg_cell {j idx p : Nat} (h : idx < W) (hp : p < 9) :
    gridAsg W bits a (cellOff W j idx + p) =
      (cellVals (chainV W bits a j idx) (a (row W (par j) idx))
        (chainV W bits a j (idx + 1))).getD p false := by
  have hd := decomp W (j := j) (show 1 + 9 * idx + p < 9 * W + 3 by omega)
  have e : cellOff W j idx + p = colBase W j + (1 + 9 * idx + p) := by unfold cellOff; omega
  unfold gridAsg
  rw [e, hd.1, hd.2, ite_eq_right (by omega), show (1 + 9 * idx + p - 1) / 9 = idx by omega,
    show (1 + 9 * idx + p - 1) % 9 = p by omega]

theorem gridAsg_local {j idx p : Nat} (h : idx < W) (hp : p < 10) :
    gridAsg W bits a (cellOff W j idx + p) =
      (cellVals (chainV W bits a j idx) (a (row W (par j) idx))
        (chainV W bits a j (idx + 1))).getD p false := by
  rcases Nat.lt_or_ge p 9 with hp9 | hp9
  · exact gridAsg_cell W bits a h hp9
  · have : p = 9 := by omega
    subst this
    rw [show cellOff W j idx + 9 = cellOff W j (idx + 1) by unfold cellOff; omega,
      gridAsg_chain W bits a (by omega)]
    rfl

theorem gridAsg_cellClause {j idx : Nat} (h : idx < W) {t : TCl}
    (ht : t ∈ cellT (bits j (row W (par j) idx)).1 (bits j (row W (par j) idx)).2) :
    evalClause (gridAsg W bits a) (inst (cellOff W j idx) (par j) t) = true := by
  rw [evalClause_inst, evalT_congr (pos_lt_ten ht) (fun p hp => gridAsg_local W bits a h hp),
    chainV_succ]
  exact cell_complete _ _ _ _ t ht

theorem gridAsg_column {j : Nat}
    (hsat : ∃ v, v < W ∧ litSat (bits j v).1 (bits j v).2 (a v) = true) {c : Clause}
    (hc : c ∈ column W j (par j) bits) : evalClause (gridAsg W bits a) c = true := by
  rcases mem_column hc with hs | ⟨idx, hidx, t, ht, rfl⟩ | he
  · have h0 : gridAsg W bits a (colBase W j + 1) = false := by
      rw [show colBase W j + 1 = cellOff W j 0 by unfold cellOff; omega,
        gridAsg_chain W bits a (Nat.zero_le _)]
      rfl
    unfold startG at hs
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hs
    rcases hs with rfl | rfl <;> simp [evalClause, evalLiteral, h0]
  · exact gridAsg_cellClause W bits a hidx ht
  · have h1 : gridAsg W bits a (cellOff W j W) = true := by
      rw [gridAsg_chain W bits a (Nat.le_refl _)]
      obtain ⟨v, hv, hs⟩ := hsat
      unfold chainV
      rw [List.any_eq_true]
      refine ⟨row W (par j) v, List.mem_range.mpr (row_lt _ hv), ?_⟩
      unfold cellSatB
      rw [row_row _ hv]
      exact hs
    unfold endG at he
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at he
    rcases he with rfl | rfl <;> simp [evalClause, evalLiteral, h1]

theorem gridAsg_rbEven {k v : Nat} (hv : v < W) {c : Clause} (hc : c ∈ rbEven W (2 * k) v) :
    evalClause (gridAsg W bits a) c = true := by
  have h1 : gridAsg W bits a (cellOff W (2 * k) v + 8) = a v := by
    rw [gridAsg_cell W bits a hv (by omega), par_even, row_false]
    rfl
  have h2 : gridAsg W bits a (cellOff W (2 * k + 1) (W - 1 - v) + 1) = a v := by
    rw [gridAsg_cell W bits a (by omega) (by omega), par_odd, row_true,
      show W - 1 - (W - 1 - v) = v by omega]
    rfl
  unfold rbEven at hc
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hc
  rcases hc with rfl | rfl <;> simp [evalClause, evalLiteral, h1, h2]

theorem gridAsg_rbOdd {k v : Nat} (hv : v < W) {c : Clause} (hc : c ∈ rbOdd W (2 * k + 1) v) :
    evalClause (gridAsg W bits a) c = true := by
  have h1 : gridAsg W bits a (cellOff W (2 * k + 1 + 1) v + 1) = a v := by
    rw [gridAsg_cell W bits a hv (by omega), show 2 * k + 1 + 1 = 2 * (k + 1) by omega,
      par_even, row_false]
    rfl
  have h2 : gridAsg W bits a (cellOff W (2 * k + 1) (W - 1 - v) + 8) = a v := by
    rw [gridAsg_cell W bits a (by omega) (by omega), par_odd, row_true,
      show W - 1 - (W - 1 - v) = v by omega]
    rfl
  unfold rbOdd at hc
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hc
  rcases hc with rfl | rfl <;> simp [evalClause, evalLiteral, h1, h2]

end complete

theorem grid_complete {W m : Nat} {bits : Nat → Nat → Bool × Bool} {a : Assignment}
    (ha : ∀ j, j < m → ∃ v, v < W ∧ litSat (bits j v).1 (bits j v).2 (a v) = true) :
    evalCNF (gridAsg W bits a) (gridCNF W m bits) = true := by
  unfold evalCNF
  rw [List.all_eq_true]
  intro c hc
  rw [gridCNF_eq] at hc
  simp only [List.mem_append] at hc
  rcases hc with ((hc | hc) | hc) | hc
  · obtain ⟨k, hk, hc⟩ := mem_colsE.mp hc
    exact gridAsg_column W bits a (ha (2 * k) (by omega)) (by rw [par_even]; exact hc)
  · obtain ⟨k, hk, hc⟩ := mem_colsO.mp hc
    exact gridAsg_column W bits a (ha (2 * k + 1) (by omega)) (by rw [par_odd]; exact hc)
  · obtain ⟨k, _, v, hv, hc⟩ := mem_rbsE.mp hc
    exact gridAsg_rbEven W bits a hv hc
  · obtain ⟨k, _, v, hv, hc⟩ := mem_rbsO.mp hc
    exact gridAsg_rbOdd W bits a hv hc

/-- **Satisfiability of the grid formula.** -/
theorem grid_satisfiable_iff (W m : Nat) (bits : Nat → Nat → Bool × Bool) :
    Satisfiable (gridCNF W m bits) ↔
      ∃ a : Assignment, ∀ j, j < m → ∃ v, v < W ∧ litSat (bits j v).1 (bits j v).2 (a v) = true := by
  constructor
  · rintro ⟨g, hg⟩
    unfold evalCNF at hg
    rw [List.all_eq_true] at hg
    exact ⟨fun v => g (cellOff W 0 v + 1), fun j hj => grid_sound hg hj⟩
  · rintro ⟨a, ha⟩
    exact ⟨gridAsg W bits a, grid_complete ha⟩
end Complexity.Planar.Grid
