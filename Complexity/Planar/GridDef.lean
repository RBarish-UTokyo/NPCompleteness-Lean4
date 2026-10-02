module

public import Complexity.Planar.CombIface
import Lean.Elab.Tactic.Omega

/-!
# The grid formula

Given `m` clauses over `W` variables, described by the occurrence bits `bits j v` (does the
positive, resp. negative, literal of `v` occur in clause `j`), the grid formula lays out one
column per clause along the spine.  A column consists of a start gadget forcing a chain variable
false, one cell per variable and an end gadget forcing the chain true; even columns list the
variables upwards, odd columns downwards.  A cell carries a copy of its variable from left to
right through a crossover gadget built from AND gates, and lets the chain absorb the literal of
the clause on that variable.  Copies of a variable in consecutive columns are equated by
nested pairs of two-literal clauses (rainbows), on top between an even column and the next,
below between an odd column and the next.

Spine positions inside a cell, relative to the chain variable entering it:
`0` chain in, `1` variable in, `2` chain after the literal, `3..7` the gadget variables
`w₁ w₂ w₃ h w₄`, `8` variable out, `9` chain out (the next cell's chain in).
-/

@[expose] public section

namespace Complexity.Planar.Grid

open SAT Comb

/-- A template clause: literals by relative position and sign (in increasing position) and
its page (`false`: the side of the incoming variable, `true`: the side of the outgoing one). -/
abbrev TCl := List (Nat × Bool) × Bool

/-- The two clauses letting the chain absorb the literal. -/
def orT : Bool → Bool → List TCl
  | false, false => [([(0, true), (1, true), (2, false)], true), ([(0, true), (2, false), (8, false)], true)]
  | true, false => [([(0, true), (1, true), (2, false)], true), ([(0, true), (2, false), (8, true)], true)]
  | false, true => [([(0, true), (1, false), (2, false)], true), ([(0, true), (2, false), (8, false)], true)]
  | true, true => [([(0, true), (1, true), (2, true)], true), ([(0, true), (2, true), (8, false)], true)]

/-- The crossover gadget: `w₁ ↔ a ∧ b`, `w₂ ↔ a ∧ ¬b'`, `w₃ ↔ ¬a' ∧ ¬b'`, `w₄ ↔ ¬a' ∧ b`, at most
one of consecutive `w`s, and `w₁ ∨ w₂ ∨ h`, `¬h ∨ w₃ ∨ w₄`; here `a, b, a', b'` are the positions
`1, 2, 8, 9`. -/
def crossT : List TCl :=
  [([(1, true), (3, false)], false), ([(2, true), (3, false)], false),
   ([(1, false), (2, false), (3, true)], false),
   ([(1, true), (4, false)], false), ([(4, false), (9, false)], false),
   ([(1, false), (4, true), (9, true)], false),
   ([(5, false), (8, false)], false), ([(5, false), (9, false)], false),
   ([(5, true), (8, true), (9, true)], false),
   ([(7, false), (8, false)], false), ([(2, true), (7, false)], true),
   ([(2, false), (7, true), (8, true)], true),
   ([(3, false), (4, false)], false), ([(4, false), (5, false)], false),
   ([(5, false), (7, false)], false), ([(3, false), (7, false)], true),
   ([(3, true), (4, true), (6, true)], true), ([(5, true), (6, false), (7, true)], false)]

/-- The template of a cell. -/
def cellT (bp bn : Bool) : List TCl := orT bp bn ++ crossT

/-- A template clause at offset `o` in a column of parity `odd`: top clauses (page different from
the parity) list their literals in increasing order, bottom clauses in decreasing order. -/
def inst (o : Nat) (odd : Bool) (c : TCl) : Clause :=
  if c.2 != odd then c.1.map (fun l => (⟨o + l.1, l.2⟩ : Literal))
  else (c.1.map (fun l => (⟨o + l.1, l.2⟩ : Literal))).reverse

/-! ## Layout -/

/-- The number of spine positions of a column. -/
def colLen (W : Nat) : Nat := 9 * W + 3

/-- The first spine position of column `j`. -/
def colBase (W j : Nat) : Nat := j * colLen W

/-- The chain variable entering cell `idx` of column `j`. -/
def cellOff (W j idx : Nat) : Nat := colBase W j + 1 + 9 * idx

/-- The variable of the cell at position `idx` of a column. -/
def row (W : Nat) (odd : Bool) (idx : Nat) : Nat := if odd then W - 1 - idx else idx

/-- Start gadget: the chain variable `s` (position `1`) is false, using `y` (position `0`). -/
def startG (W j : Nat) : CNF :=
  [[⟨colBase W j, true⟩, ⟨colBase W j + 1, false⟩], [⟨colBase W j + 1, false⟩, ⟨colBase W j, false⟩]]

/-- End gadget: the last chain variable `p` is true, using the next position `y`. -/
def endG (W j : Nat) : CNF :=
  [[⟨cellOff W j W, true⟩, ⟨cellOff W j W + 1, true⟩],
   [⟨cellOff W j W + 1, false⟩, ⟨cellOff W j W, true⟩]]

/-- The clauses of a cell. -/
def cellCNF (W j idx : Nat) (odd : Bool) (b : Bool × Bool) : CNF :=
  (cellT b.1 b.2).map (inst (cellOff W j idx) odd)

/-- A column. -/
def column (W j : Nat) (odd : Bool) (bits : Nat → Nat → Bool × Bool) : CNF :=
  startG W j ++ (List.range W).reverse.flatMap (fun idx =>
    cellCNF W j idx odd (bits j (row W odd idx))) ++ endG W j

/-- The rainbow pair joining row `v` of the even column `j` to the odd column `j + 1` (top). -/
def rbEven (W j v : Nat) : CNF :=
  [[⟨cellOff W j v + 8, false⟩, ⟨cellOff W (j + 1) (W - 1 - v) + 1, true⟩],
   [⟨cellOff W j v + 8, true⟩, ⟨cellOff W (j + 1) (W - 1 - v) + 1, false⟩]]

/-- The rainbow pair joining row `v` of the odd column `j` to the even column `j + 1` (bottom). -/
def rbOdd (W j v : Nat) : CNF :=
  [[⟨cellOff W (j + 1) v + 1, true⟩, ⟨cellOff W j (W - 1 - v) + 8, false⟩],
   [⟨cellOff W (j + 1) v + 1, false⟩, ⟨cellOff W j (W - 1 - v) + 8, true⟩]]

/-- **The grid formula**, in the order in which it is emitted. -/
def gridCNF (W m : Nat) (bits : Nat → Nat → Bool × Bool) : CNF :=
  ((List.range m).reverse.flatMap fun k =>
    if 2 * k + 1 ≤ m then column W (2 * k) false bits else []) ++
  ((List.range m).reverse.flatMap fun k =>
    if 2 * k + 2 ≤ m then column W (2 * k + 1) true bits else []) ++
  ((List.range m).reverse.flatMap fun k =>
    if 2 * k + 2 ≤ m then (List.range W).reverse.flatMap (rbEven W (2 * k)) else []) ++
  ((List.range m).reverse.flatMap fun k =>
    if 2 * k + 3 ≤ m then (List.range W).reverse.flatMap (rbOdd W (2 * k + 1)) else [])

/-! ## Template checks -/

/-- A Boolean test for `NestRaw`. -/
def nestB (a b : List Nat) : Bool :=
  (List.range (b.length - 1)).any fun t => decide (b[t]! ≤ a.headD 0 ∧ a.getLastD 0 ≤ b[t + 1]!)

/-- A Boolean test for `LamRaw`. -/
def lamB (a b : List Nat) : Bool :=
  nestB a b || nestB b a || decide (a.getLastD 0 ≤ b.headD 0 ∨ b.getLastD 0 ≤ a.headD 0)

theorem nestRaw_of_nestB {a b : List Nat} (h : nestB a b = true) : NestRaw a b := by
  unfold nestB at h
  rw [List.any_eq_true] at h
  obtain ⟨t, ht, hd⟩ := h
  rw [List.mem_range] at ht
  rw [decide_eq_true_eq] at hd
  refine ⟨t, by omega, ?_, ?_⟩
  · have := hd.1; rwa [getElem!_pos b t (by omega)] at this
  · have := hd.2; rwa [getElem!_pos b (t + 1) (by omega)] at this

theorem lamRaw_of_lamB {a b : List Nat} (h : lamB a b = true) : LamRaw a b := by
  unfold lamB at h
  simp only [Bool.or_eq_true, decide_eq_true_eq] at h
  rcases h with (h | h) | h
  · exact Or.inl (nestRaw_of_nestB h)
  · exact Or.inr (Or.inl (nestRaw_of_nestB h))
  · exact Or.inr (Or.inr h)

/-- The positions of a template clause. -/
def tpos (c : TCl) : List Nat := c.1.map Prod.fst

/-- Template clauses on the same page are laminar. -/
theorem cellT_lam (bp bn : Bool) :
    (cellT bp bn).Pairwise (fun c d => c.2 = d.2 → lamB (tpos c) (tpos d) = true) := by
  cases bp <;> cases bn <;> decide

/-- No clause on page `false` passes over position `1`, none on page `true` over position `8`;
every clause has two to three literals in strictly increasing position below `10`. -/
theorem cellT_shape (bp bn : Bool) :
    ∀ c ∈ cellT bp bn, 2 ≤ c.1.length ∧ c.1.length ≤ 3 ∧ (tpos c).Pairwise (· < ·) ∧
      (∀ p ∈ tpos c, p < 10) ∧
      (c.2 = false → ¬ ((tpos c).headD 0 < 1 ∧ 1 < (tpos c).getLastD 0)) ∧
      (c.2 = true → ¬ ((tpos c).headD 0 < 8 ∧ 8 < (tpos c).getLastD 0)) := by
  cases bp <;> cases bn <;> decide

end Complexity.Planar.Grid
