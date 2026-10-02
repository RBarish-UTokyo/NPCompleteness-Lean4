module

public import Complexity.SAT
import Lean.Elab.Tactic.Omega

/-!
# Reading a formula code with the help of a certificate

A verifier cannot run a parser, but it can check a parse supplied in its certificate: the
number of clauses `m`, clause lengths `kk`, prefix sums `O`, the start positions `P` of the
clauses and `Q` of the literals, and for every literal occurrence its clause `J`, slot `T`,
variable `V` and sign `S`.  `ParseOK` collects the local checks; `ParseOK.encode_eq` shows that
they force the word to be the code of the formula `fml` read off the tables, and
`parseOK_of_encode` builds tables for the code of any formula.
-/

@[expose] public section

namespace Complexity.Planar

open SAT

/-- The parsing tables of a certificate. -/
structure ParseTables where
  m : Nat
  M : Nat
  kk : Nat → Nat
  O : Nat → Nat
  P : Nat → Nat
  J : Nat → Nat
  T : Nat → Nat
  V : Nat → Nat
  S : Nat → Nat
  Q : Nat → Nat

/-- The local checks of a parse of the word with bits `xb` and length `L`. -/
structure ParseOK (L : Nat) (xb : Nat → Option Bool) (t : ParseTables) : Prop where
  m_le : t.m ≤ L
  M_le : t.M ≤ L
  head : ∀ i, i < t.m → xb i = some true
  headEnd : xb t.m = some false
  O_zero : t.O 0 = 0
  O_succ : ∀ j, j < t.m → t.O (j + 1) = t.O j + t.kk j
  O_last : t.O t.m = t.M
  P_zero : t.P 0 = t.m + 1
  len : ∀ j, j < t.m → ∀ i, i < t.kk j → xb (t.P j + i) = some true
  lenEnd : ∀ j, j < t.m → xb (t.P j + t.kk j) = some false
  empty : ∀ j, j < t.m → t.kk j = 0 → t.P (j + 1) = t.P j + 1
  first : ∀ j, j < t.m → 0 < t.kk j → t.Q (t.O j) = t.P j + t.kk j + 1
  occ : ∀ e, e < t.M → t.J e < t.m ∧ t.T e < t.kk (t.J e) ∧ t.O (t.J e) + t.T e = e
  sign : ∀ e, e < t.M → t.S e ≤ 1 ∧ xb (t.Q e) = some (t.S e == 1)
  var : ∀ e, e < t.M → ∀ i, i < t.V e → xb (t.Q e + 1 + i) = some true
  varEnd : ∀ e, e < t.M → xb (t.Q e + 1 + t.V e) = some false
  next : ∀ e, e < t.M → t.T e + 1 < t.kk (t.J e) → t.Q (e + 1) = t.Q e + t.V e + 2
  last : ∀ e, e < t.M → t.T e + 1 = t.kk (t.J e) → t.P (t.J e + 1) = t.Q e + t.V e + 2
  P_last : t.P t.m = L

/-- The literal of occurrence `e`. -/
def ParseTables.lit (t : ParseTables) (e : Nat) : Literal := ⟨t.V e, t.S e == 1⟩

/-- The `j`-th clause. -/
def ParseTables.clause (t : ParseTables) (j : Nat) : Clause :=
  (List.range (t.kk j)).map fun i => t.lit (t.O j + i)

/-- The formula read off the tables. -/
def ParseTables.fml (t : ParseTables) : CNF := (List.range t.m).map t.clause

/-! ## Words from bits -/

/-- A word agrees with `w` from position `p` on. -/
theorem drop_eq_append {x w : List Bool} {p : Nat}
    (h : ∀ i, i < w.length → x[p + i]? = some w[i]!) :
    x.drop p = w ++ x.drop (p + w.length) := by
  induction w generalizing p with
  | nil => simp
  | cons b w ih =>
    have h0 := h 0 (by simp)
    simp only [Nat.add_zero, List.getElem!_cons_zero] at h0
    have hrest : ∀ i, i < w.length → x[p + 1 + i]? = some w[i]! := by
      intro i hi
      have := h (i + 1) (by simp; omega)
      simpa [Nat.add_assoc, Nat.add_comm 1 i] using this
    have ih' := ih hrest
    have hp : p < x.length := by
      rcases Nat.lt_or_ge p x.length with hp | hp
      · exact hp
      · simp [List.getElem?_eq_none hp] at h0
    rw [List.drop_eq_getElem_cons hp, ih']
    have : x[p] = b := by
      have := List.getElem?_eq_getElem hp
      rw [h0] at this; exact (Option.some.inj this).symm
    simp [this, Nat.add_assoc, Nat.add_comm 1 w.length]

theorem getElem!_replicate_append (k i : Nat) (hi : i < k) (w : List Bool) :
    (List.replicate k true ++ w)[i]! = true := by
  rw [List.getElem!_eq_getElem?_getD, List.getElem?_append_left (by simpa using hi)]
  simp [hi]

theorem writeNat_eq_replicate' (k : Nat) : writeNat k = List.replicate k true ++ [false] := by
  induction k with
  | zero => rfl
  | succ k ih => simp [writeNat, ih, List.replicate_succ]

/-- Reading a unary number. -/
theorem drop_writeNat {x : List Bool} {p k : Nat} (h1 : ∀ i, i < k → x[p + i]? = some true)
    (h2 : x[p + k]? = some false) : x.drop p = writeNat k ++ x.drop (p + k + 1) := by
  have hw := writeNat_eq_replicate' k
  have := drop_eq_append (x := x) (w := writeNat k) (p := p) (by
    intro i hi
    rw [hw] at hi ⊢
    simp at hi
    rcases Nat.lt_or_ge i k with hik | hik
    · rw [h1 i hik, getElem!_replicate_append k i hik]
    · have : i = k := by omega
      subst this
      rw [h2]
      simp)
  rw [this, hw]; simp [Nat.add_assoc]

/-! ## Offsets -/

section offsets

variable {L : Nat} {xb : Nat → Option Bool} {t : ParseTables}

theorem ParseOK.O_mono (h : ParseOK L xb t) {j j' : Nat} (hj : j ≤ j') (hj' : j' ≤ t.m) :
    t.O j ≤ t.O j' := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hj
  induction d with
  | zero => exact Nat.le_refl _
  | succ d ih =>
    have h1 := h.O_succ (j + d) (by omega)
    have h2 := ih (by omega) (by omega)
    rw [show j + (d + 1) = j + d + 1 by omega]
    omega

/-- Occurrence `O j + i` belongs to clause `j`. -/
theorem ParseOK.occ_of (h : ParseOK L xb t) {j i : Nat} (hj : j < t.m) (hi : i < t.kk j) :
    t.O j + i < t.M ∧ t.J (t.O j + i) = j ∧ t.T (t.O j + i) = i := by
  have hlt : t.O j + i < t.M := by
    have h1 := h.O_succ j hj
    have h2 := h.O_mono (j := j + 1) (j' := t.m) (by omega) (Nat.le_refl _)
    rw [h.O_last] at h2
    omega
  refine ⟨hlt, ?_⟩
  obtain ⟨hJ, hT, hsum⟩ := h.occ _ hlt
  have hJj : t.J (t.O j + i) = j := by
    rcases Nat.lt_trichotomy (t.J (t.O j + i)) j with hlt' | heq | hgt
    · have h1 := h.O_succ _ hJ
      have h2 := h.O_mono (j := t.J (t.O j + i) + 1) (j' := j) (by omega) (by omega)
      omega
    · exact heq
    · have h1 := h.O_succ j hj
      have h2 := h.O_mono (j := j + 1) (j' := t.J (t.O j + i)) (by omega) (by omega)
      omega
  refine ⟨hJj, ?_⟩
  rw [hJj] at hsum
  omega

end offsets

/-! ## The word is the code of the formula -/

theorem ParseOK.drop_literal {L : Nat} {x : List Bool} {t : ParseTables}
    (h : ParseOK L (fun p => x[p]?) t) {e : Nat} (he : e < t.M) :
    x.drop (t.Q e) = encodeLiteral (t.lit e) ++ x.drop (t.Q e + t.V e + 2) := by
  obtain ⟨_, hsign⟩ := h.sign e he
  have hp : t.Q e < x.length := by
    rcases Nat.lt_or_ge (t.Q e) x.length with hp | hp
    · exact hp
    · simp [List.getElem?_eq_none hp] at hsign
  have hx : x[t.Q e] = (t.S e == 1) := by
    have := List.getElem?_eq_getElem hp
    rw [hsign] at this; exact (Option.some.inj this).symm
  rw [List.drop_eq_getElem_cons hp, hx]
  have hrest := drop_writeNat (x := x) (p := t.Q e + 1) (k := t.V e)
    (fun i hi => h.var e he i hi) (h.varEnd e he)
  rw [hrest]
  simp [encodeLiteral, ParseTables.lit, Nat.add_assoc]
  omega

/-- The literals of clause `j` from slot `i` on. -/
theorem ParseOK.drop_literals {L : Nat} {x : List Bool} {t : ParseTables}
    (h : ParseOK L (fun p => x[p]?) t) {j : Nat} (hj : j < t.m) :
    ∀ r i, i + r = t.kk j → 0 < r →
      x.drop (t.Q (t.O j + i)) = writeValues encodeLiteral
        (((List.range (t.kk j)).map fun i => t.lit (t.O j + i)).drop i) ++ x.drop (t.P (j + 1)) := by
  intro r
  induction r with
  | zero => intro i _ h0; omega
  | succ r ih =>
    intro i hir _
    have hi : i < t.kk j := by omega
    obtain ⟨he, hJ, hT⟩ := h.occ_of hj hi
    rw [h.drop_literal he]
    have hdrop : ((List.range (t.kk j)).map fun i => t.lit (t.O j + i)).drop i =
        t.lit (t.O j + i) :: ((List.range (t.kk j)).map fun i => t.lit (t.O j + i)).drop (i + 1) := by
      rw [List.drop_eq_getElem_cons (by simpa using hi)]
      simp
    rw [hdrop, writeValues, List.append_assoc]
    congr 1
    by_cases hr : r = 0
    · subst hr
      have hlast := h.last _ he (by rw [hJ, hT]; omega)
      rw [hJ] at hlast
      rw [hlast]
      have : ((List.range (t.kk j)).map fun i => t.lit (t.O j + i)).drop (i + 1) = [] := by
        apply List.drop_eq_nil_of_le; simp; omega
      simp [this, writeValues]
    · have hnext := h.next _ he (by rw [hJ, hT]; omega)
      rw [← hnext, show t.O j + i + 1 = t.O j + (i + 1) by omega]
      exact ih (i + 1) (by omega) (by omega)

theorem ParseOK.drop_clause {L : Nat} {x : List Bool} {t : ParseTables}
    (h : ParseOK L (fun p => x[p]?) t) {j : Nat} (hj : j < t.m) :
    x.drop (t.P j) = encodeClause (t.clause j) ++ x.drop (t.P (j + 1)) := by
  rw [drop_writeNat (fun i hi => h.len j hj i hi) (h.lenEnd j hj)]
  simp only [encodeClause, writeList, ParseTables.clause, List.length_map, List.length_range,
    List.append_assoc]
  congr 1
  by_cases hk : t.kk j = 0
  · rw [h.empty j hj hk, hk]
    simp [writeValues]
  · rw [← h.first j hj (by omega)]
    have := h.drop_literals hj (t.kk j) 0 (by omega) (by omega)
    simpa using this

theorem ParseOK.drop_clauses {L : Nat} {x : List Bool} {t : ParseTables}
    (h : ParseOK L (fun p => x[p]?) t) (hL : x.length = L) :
    ∀ r j, j + r = t.m → x.drop (t.P j) = writeValues encodeClause (t.fml.drop j) := by
  intro r
  induction r with
  | zero =>
    intro j hj
    have : j = t.m := by omega
    subst this
    rw [h.P_last, ← hL, List.drop_length]
    have : t.fml.drop t.m = [] := by apply List.drop_eq_nil_of_le; simp [ParseTables.fml]
    simp [this, writeValues]
  | succ r ih =>
    intro j hj
    have hjm : j < t.m := by omega
    rw [h.drop_clause hjm, ih (j + 1) (by omega)]
    have : t.fml.drop j = t.clause j :: t.fml.drop (j + 1) := by
      rw [List.drop_eq_getElem_cons (by simp [ParseTables.fml]; omega)]
      simp [ParseTables.fml]
    rw [this, writeValues]

/-- **The checks force the word to be a formula code.** -/
theorem ParseOK.encode_eq {x : List Bool} {t : ParseTables}
    (h : ParseOK x.length (fun p => x[p]?) t) : encode t.fml = x := by
  have hhead := drop_writeNat (x := x) (p := 0) (k := t.m) (by simpa using h.head)
    (by simpa using h.headEnd)
  have hcl := h.drop_clauses rfl t.m 0 (by omega)
  rw [h.P_zero] at hcl
  simp only [List.drop_zero, Nat.zero_add] at hhead hcl
  rw [hcl] at hhead
  rw [hhead]
  simp [encode, writeList, ParseTables.fml]

theorem ParseTables.three {t : ParseTables}
    (h3 : ∀ j, j < t.m → t.kk j ≤ 3) : IsThreeCNF t.fml := by
  intro c hc
  simp only [ParseTables.fml, List.mem_map, List.mem_range] at hc
  obtain ⟨j, hj, rfl⟩ := hc
  simpa [ParseTables.clause] using h3 j hj

/-! ## Canonical tables of a formula code -/

theorem writeValues_append' {α : Type} (enc : α → List Bool) (xs ys : List α) :
    writeValues enc (xs ++ ys) = writeValues enc xs ++ writeValues enc ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [writeValues, ih, List.append_assoc]

theorem writeValues_take_drop {α : Type} (enc : α → List Bool) (xs : List α) (j : Nat) :
    writeValues enc xs = writeValues enc (xs.take j) ++ writeValues enc (xs.drop j) := by
  rw [← writeValues_append', List.take_append_drop]

theorem writeValues_drop_cons {α : Type} (enc : α → List Bool) (xs : List α) (j : Nat)
    (hj : j < xs.length) :
    writeValues enc (xs.drop j) = enc xs[j] ++ writeValues enc (xs.drop (j + 1)) := by
  rw [List.drop_eq_getElem_cons hj, writeValues]

/-- Split an index of a concatenation of blocks into (block, offset). -/
def locate : List Nat → Nat → Nat × Nat
  | [], e => (0, e)
  | k :: ks, e => if e < k then (0, e) else ((locate ks (e - k)).1 + 1, (locate ks (e - k)).2)

theorem locate_spec (ks : List Nat) (e : Nat) (he : e < ks.sum) :
    (locate ks e).1 < ks.length ∧ (locate ks e).2 < ks[(locate ks e).1]! ∧
      (ks.take (locate ks e).1).sum + (locate ks e).2 = e := by
  induction ks generalizing e with
  | nil => simp at he
  | cons k ks ih =>
    by_cases hek : e < k
    · simp [locate, hek]
    · simp only [List.sum_cons] at he
      obtain ⟨h1, h2, h3⟩ := ih (e - k) (by omega)
      simp only [locate, hek, ite_false, List.length_cons, List.take_succ_cons, List.sum_cons]
      refine ⟨by omega, ?_, by omega⟩
      simpa using h2

/-- The canonical parse of the code of `f`. -/
def canonTables (f : CNF) : ParseTables where
  m := f.length
  M := (f.map List.length).sum
  kk j := (f[j]?.getD []).length
  O j := ((f.take j).map List.length).sum
  P j := f.length + 1 + (writeValues encodeClause (f.take j)).length
  J e := (locate (f.map List.length) e).1
  T e := (locate (f.map List.length) e).2
  V e := ((f[(locate (f.map List.length) e).1]?.getD [])[(locate (f.map List.length) e).2]?.getD
    ⟨0, true⟩).var
  S e := if ((f[(locate (f.map List.length) e).1]?.getD [])[(locate (f.map List.length) e).2]?.getD
    ⟨0, true⟩).positive then 1 else 0
  Q e := f.length + 1 + (writeValues encodeClause (f.take (locate (f.map List.length) e).1)).length
    + (f[(locate (f.map List.length) e).1]?.getD []).length + 1
    + (writeValues encodeLiteral ((f[(locate (f.map List.length) e).1]?.getD []).take
        (locate (f.map List.length) e).2)).length

theorem encode_drop_P (f : CNF) (j : Nat) :
    (encode f).drop ((canonTables f).P j) = writeValues encodeClause (f.drop j) := by
  have : encode f = writeNat f.length ++ (writeValues encodeClause (f.take j) ++
      writeValues encodeClause (f.drop j)) := by
    rw [← writeValues_take_drop]; rfl
  rw [this, ← List.append_assoc, List.drop_append]
  simp [canonTables, SATBounds_writeNat_length_aux]
where
  SATBounds_writeNat_length_aux : (writeNat f.length).length = f.length + 1 := by
    rw [writeNat_eq_replicate']; simp

theorem locate_eq (ks : List Nat) (j t : Nat) (hj : j < ks.length) (ht : t < ks[j]) :
    locate ks ((ks.take j).sum + t) = (j, t) := by
  induction ks generalizing j with
  | nil => simp at hj
  | cons k ks ih =>
    cases j with
    | zero => simp at ht; simp [locate, ht]
    | succ j =>
      simp only [List.take_succ_cons, List.sum_cons]
      have hlt : ¬ (k + (ks.take j).sum + t < k) := by omega
      simp only [locate, hlt, ite_false]
      have := ih j (by simpa using hj) (by simpa using ht)
      rw [show k + (ks.take j).sum + t - k = (ks.take j).sum + t by omega, this]

theorem sum_take_succ (ks : List Nat) (j : Nat) (hj : j < ks.length) :
    (ks.take (j + 1)).sum = (ks.take j).sum + ks[j] := by
  rw [List.take_add_one, List.sum_append]
  simp [List.getElem?_eq_getElem hj]

theorem length_writeValues_take_succ {α : Type} (enc : α → List Bool) (xs : List α) (j : Nat)
    (hj : j < xs.length) :
    (writeValues enc (xs.take (j + 1))).length =
      (writeValues enc (xs.take j)).length + (enc xs[j]).length := by
  rw [List.take_add_one, writeValues_append']
  simp [List.getElem?_eq_getElem hj, writeValues]

theorem length_writeValues_le {α : Type} (enc : α → List Bool) (xs : List α)
    (h : ∀ x, 1 ≤ (enc x).length) : xs.length ≤ (writeValues enc xs).length := by
  induction xs with
  | nil => simp [writeValues]
  | cons x xs ih => simp [writeValues]; have := h x; omega

theorem length_encodeLiteral (l : Literal) : (encodeLiteral l).length = l.var + 2 := by
  simp [encodeLiteral, writeNat_eq_replicate']

theorem length_writeNat (k : Nat) : (writeNat k).length = k + 1 := by
  simp [writeNat_eq_replicate']

theorem length_encodeClause_ge (c : Clause) : c.length + 1 ≤ (encodeClause c).length := by
  simp only [encodeClause, writeList, List.length_append, length_writeNat]
  have := length_writeValues_le encodeLiteral c (fun l => by rw [length_encodeLiteral]; omega)
  omega

theorem getElem?_writeNat_lt (k i : Nat) (hi : i < k) (w : List Bool) :
    (writeNat k ++ w)[i]? = some true := by
  rw [writeNat_eq_replicate', List.append_assoc, List.getElem?_append_left (by simpa using hi)]
  simp [hi]

theorem getElem?_writeNat_eq (k : Nat) (w : List Bool) :
    (writeNat k ++ w)[k]? = some false := by
  rw [writeNat_eq_replicate', List.append_assoc, List.getElem?_append_right (by simp)]
  simp

section canon

variable (f : CNF)

/-- Abbreviation for the clause lengths. -/
def lens : List Nat := f.map List.length

theorem canon_O (j : Nat) : (canonTables f).O j = ((lens f).take j).sum := by
  simp [canonTables, lens, List.map_take]

theorem canon_drop_clause (j : Nat) (hj : j < f.length) :
    (encode f).drop ((canonTables f).P j) =
      encodeClause f[j] ++ writeValues encodeClause (f.drop (j + 1)) := by
  rw [encode_drop_P, writeValues_drop_cons _ _ _ hj]

theorem canon_kk (j : Nat) (hj : j < f.length) : (canonTables f).kk j = f[j].length := by
  simp [canonTables, List.getElem?_eq_getElem hj]

theorem canon_P_succ (j : Nat) (hj : j < f.length) :
    (canonTables f).P (j + 1) = (canonTables f).P j + (encodeClause f[j]).length := by
  simp only [canonTables]
  rw [length_writeValues_take_succ _ _ _ hj]
  omega

/-- The occurrence `O j + t` is literal `t` of clause `j`. -/
theorem canon_locate (j t : Nat) (hj : j < f.length) (ht : t < f[j].length) :
    locate (lens f) ((canonTables f).O j + t) = (j, t) := by
  rw [canon_O]
  exact locate_eq (lens f) j t (by simpa [lens] using hj) (by simpa [lens] using ht)

theorem canon_lit (j t : Nat) (hj : j < f.length) (ht : t < f[j].length) :
    (canonTables f).lit ((canonTables f).O j + t) = f[j][t] := by
  have hl := canon_locate f j t hj ht
  simp only [ParseTables.lit, canonTables, lens] at hl ⊢
  rw [hl]
  simp only [List.getElem?_eq_getElem hj, Option.getD_some, List.getElem?_eq_getElem ht]
  cases h : f[j][t] with
  | mk v pos => cases pos <;> simp

theorem canon_fml : (canonTables f).fml = f := by
  apply List.ext_getElem
  · simp [ParseTables.fml, canonTables]
  · intro j h1 h2
    simp only [ParseTables.fml, List.getElem_map, List.getElem_range, ParseTables.clause]
    apply List.ext_getElem
    · simp [canon_kk f j h2]
    · intro t ht1 ht2
      simp only [List.getElem_map, List.getElem_range]
      exact canon_lit f j t h2 ht2

end canon

section canon2

variable (f : CNF)

theorem drop_three (A B C : List Bool) (k : Nat) (hk : k = A.length) :
    (A ++ (B ++ C)).drop k = B ++ C := by
  subst hk; simp

/-- From a literal start on, the code continues with that literal. -/
theorem canon_drop_Q (e : Nat) (he : e < (canonTables f).M) :
    ∃ j t, ∃ hj : j < f.length, ∃ ht : t < f[j].length, (canonTables f).O j + t = e ∧
      locate (f.map List.length) e = (j, t) ∧
      (encode f).drop ((canonTables f).Q e) =
        encodeLiteral f[j][t] ++ (writeValues encodeLiteral (f[j].drop (t + 1)) ++
          writeValues encodeClause (f.drop (j + 1))) := by
  have hsum : e < (f.map List.length).sum := by simpa [canonTables] using he
  obtain ⟨hj, ht, hsumj⟩ := locate_spec _ e hsum
  generalize hl : locate (f.map List.length) e = p at hj ht hsumj
  obtain ⟨j, t⟩ := p
  simp only at hj ht hsumj
  have hj' : j < f.length := by simpa using hj
  have ht' : t < f[j].length := by
    rw [List.getElem!_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hj'] at ht
    simpa using ht
  refine ⟨j, t, hj', ht', ?_, rfl, ?_⟩
  · rw [canon_O]; simpa [lens] using hsumj
  · have hQ : (canonTables f).Q e = (canonTables f).P j + (f[j].length + 1 +
        (writeValues encodeLiteral (f[j].take t)).length) := by
      simp only [canonTables, hl, List.getElem?_eq_getElem hj', Option.getD_some]
      omega
    rw [hQ, ← List.drop_drop, canon_drop_clause f j hj']
    simp only [encodeClause, writeList]
    rw [writeValues_take_drop encodeLiteral f[j] t, writeValues_drop_cons _ _ _ ht']
    have : writeNat f[j].length ++ (writeValues encodeLiteral (f[j].take t) ++
        (encodeLiteral f[j][t] ++ writeValues encodeLiteral (f[j].drop (t + 1)))) ++
        writeValues (writeList encodeLiteral) (f.drop (j + 1)) =
        (writeNat f[j].length ++ writeValues encodeLiteral (f[j].take t)) ++
        (encodeLiteral f[j][t] ++ (writeValues encodeLiteral (f[j].drop (t + 1)) ++
        writeValues (writeList encodeLiteral) (f.drop (j + 1)))) := by
      simp [List.append_assoc]
    rw [this, show f[j].length + 1 + (writeValues encodeLiteral (f[j].take t)).length =
      (writeNat f[j].length ++ writeValues encodeLiteral (f[j].take t)).length by
        simp [length_writeNat], List.drop_left]

end canon2

section canon3

variable (f : CNF)

theorem canon_M : (canonTables f).M = (f.map List.length).sum := rfl

theorem canon_O' (j : Nat) : (canonTables f).O j = ((f.map List.length).take j).sum := by
  rw [canon_O]; rfl

theorem canon_Q_of_locate (e j t : Nat) (hl : locate (f.map List.length) e = (j, t))
    (hj : j < f.length) :
    (canonTables f).Q e = (canonTables f).P j + f[j].length + 1 +
      (writeValues encodeLiteral (f[j].take t)).length := by
  simp only [canonTables, hl, List.getElem?_eq_getElem hj, Option.getD_some]

theorem canon_locate' (j t : Nat) (hj : j < f.length) (ht : t < f[j].length) :
    locate (f.map List.length) ((canonTables f).O j + t) = (j, t) :=
  canon_locate f j t hj ht

theorem canon_VS_of_locate (e j t : Nat) (hl : locate (f.map List.length) e = (j, t))
    (hj : j < f.length) (ht : t < f[j].length) :
    (canonTables f).V e = f[j][t].var ∧ ((canonTables f).S e == 1) = f[j][t].positive ∧
      (canonTables f).J e = j ∧ (canonTables f).T e = t := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [canonTables, hl, List.getElem?_eq_getElem hj, List.getElem?_eq_getElem ht]
  · simp only [canonTables, hl, List.getElem?_eq_getElem hj, List.getElem?_eq_getElem ht,
      Option.getD_some]
    cases f[j][t].positive <;> simp
  · simp [canonTables, hl]
  · simp [canonTables, hl]

theorem canon_Q_lit (e : Nat) (he : e < (canonTables f).M) :
    (encode f)[(canonTables f).Q e]? = some ((canonTables f).S e == 1) ∧
    (∀ i, i < (canonTables f).V e → (encode f)[(canonTables f).Q e + 1 + i]? = some true) ∧
    (encode f)[(canonTables f).Q e + 1 + (canonTables f).V e]? = some false := by
  obtain ⟨j, t, hj, ht, _, hl, hd⟩ := canon_drop_Q f e he
  obtain ⟨hV, hS, _, _⟩ := canon_VS_of_locate f e j t hl hj ht
  refine ⟨?_, ?_, ?_⟩
  · rw [← Nat.add_zero ((canonTables f).Q e), ← List.getElem?_drop, hd, hS]
    simp [encodeLiteral]
  · intro i hi
    rw [hV] at hi
    rw [show (canonTables f).Q e + 1 + i = (canonTables f).Q e + (i + 1) by omega,
      ← List.getElem?_drop, hd]
    simp only [encodeLiteral, List.cons_append, List.getElem?_cons_succ]
    exact getElem?_writeNat_lt _ _ hi _
  · rw [show (canonTables f).Q e + 1 + (canonTables f).V e =
      (canonTables f).Q e + ((canonTables f).V e + 1) by omega, ← List.getElem?_drop, hd, hV]
    simp only [encodeLiteral, List.cons_append, List.getElem?_cons_succ]
    exact getElem?_writeNat_eq _ _

theorem canon_ok : ParseOK (encode f).length (fun p => (encode f)[p]?) (canonTables f) := by
  have hlenE : (encode f).length = f.length + 1 + (writeValues encodeClause f).length := by
    simp [encode, writeList, length_writeNat]
  constructor
  · simp only [canonTables]; omega
  · simp only [canonTables]
    have : ∀ g : CNF, (g.map List.length).sum ≤ (writeValues encodeClause g).length := by
      intro g
      induction g with
      | nil => simp [writeValues]
      | cons c g ih =>
        simp [writeValues]; have := length_encodeClause_ge c; omega
    have := this f; omega
  · intro i hi
    simp only [canonTables] at hi
    exact getElem?_writeNat_lt _ _ hi _
  · exact getElem?_writeNat_eq _ _
  · simp [canonTables]
  · intro j hj
    simp only [canonTables] at hj
    rw [canon_O', canon_O', sum_take_succ _ _ (by simpa using hj), canon_kk f j hj]
    simp
  · rw [canon_O', List.take_of_length_le (by simp [canonTables])]; rfl
  · simp [canonTables, writeValues]
  · intro j hj i hi
    simp only [canonTables] at hj
    rw [canon_kk f j hj] at hi
    rw [← List.getElem?_drop, canon_drop_clause f j hj]
    simp only [encodeClause, writeList, List.append_assoc]
    exact getElem?_writeNat_lt _ _ hi _
  · intro j hj
    simp only [canonTables] at hj
    rw [canon_kk f j hj, ← List.getElem?_drop, canon_drop_clause f j hj]
    simp only [encodeClause, writeList, List.append_assoc]
    exact getElem?_writeNat_eq _ _
  · intro j hj hk
    simp only [canonTables] at hj
    rw [canon_kk f j hj] at hk
    rw [canon_P_succ f j hj]
    have : f[j] = [] := List.eq_nil_of_length_eq_zero hk
    simp [this, encodeClause, writeList, length_writeNat, writeValues]
  · intro j hj hk
    simp only [canonTables] at hj
    rw [canon_kk f j hj] at hk ⊢
    have hl := canon_locate' f j 0 hj hk
    rw [Nat.add_zero] at hl
    rw [canon_Q_of_locate f _ j 0 hl hj]
    simp [writeValues]
  · intro e he
    have hsum : e < (f.map List.length).sum := by simpa [canonTables] using he
    obtain ⟨h1, h2, h3⟩ := locate_spec _ e hsum
    have hj' : (locate (f.map List.length) e).1 < f.length := by simpa using h1
    refine ⟨by simpa [canonTables] using h1, ?_, ?_⟩
    · simp only [canonTables, List.getElem?_eq_getElem hj', Option.getD_some]
      rw [List.getElem!_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hj'] at h2
      simpa using h2
    · rw [canon_O']; simpa [canonTables] using h3
  · intro e he
    refine ⟨by simp only [canonTables]; split <;> omega, (canon_Q_lit f e he).1⟩
  · intro e he i hi
    exact (canon_Q_lit f e he).2.1 i hi
  · intro e he
    exact (canon_Q_lit f e he).2.2
  · intro e he hT
    obtain ⟨j, t, hj, ht, hsum, hl, _⟩ := canon_drop_Q f e he
    obtain ⟨hV, _, hJ, hTt⟩ := canon_VS_of_locate f e j t hl hj ht
    rw [hJ, hTt, canon_kk f j hj] at hT
    have hl1 := canon_locate' f j (t + 1) hj hT
    rw [← Nat.add_assoc, hsum] at hl1
    rw [canon_Q_of_locate f _ j t hl hj, canon_Q_of_locate f _ j (t + 1) hl1 hj, hV,
      length_writeValues_take_succ _ _ _ ht, length_encodeLiteral]
    omega
  · intro e he hT
    obtain ⟨j, t, hj, ht, _, hl, _⟩ := canon_drop_Q f e he
    obtain ⟨hV, _, hJ, hTt⟩ := canon_VS_of_locate f e j t hl hj ht
    rw [hJ, hTt, canon_kk f j hj] at hT
    rw [hJ, canon_P_succ f j hj, canon_Q_of_locate f _ j t hl hj, hV]
    simp only [encodeClause, writeList, List.length_append, length_writeNat]
    have := length_writeValues_take_succ encodeLiteral f[j] t ht
    rw [hT, List.take_length] at this
    rw [this, length_encodeLiteral]
    omega
  · simp only [canonTables]
    rw [List.take_length]
    omega

end canon3

end Complexity.Planar
