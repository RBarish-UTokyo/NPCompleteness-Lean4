module

public import Complexity.Planar.ParseCert
public import Complexity.Planar.EmbedComplete
public import Complexity.Planar.Incidence
import Lean.Elab.Tactic.Omega

/-!
# The planar 3-SAT verifier, mathematically

A certificate for a word `x` consists of parsing tables (`ParseTables`), the variable count `K`
with a literal attaining it, an assignment `A` with a satisfied slot `tsel` in every clause,
and embedding tables (`EmbedTables`) for the incidence graph, together with the variable cycle
when `cyc` is set.  `VSpec` collects all local checks.  `VSpec.sound` derives membership in
(cyclic) planar 3-SAT; `vspec_complete` builds a certificate for every member.
-/

@[expose] public section

namespace Complexity.Planar

open SAT

/-- A certificate. -/
structure VCert where
  pt : ParseTables
  K : Nat
  estar : Nat
  A : Nat → Nat
  tsel : Nat → Nat
  et : EmbedTables

/-- The local checks on a certificate for the word with bits `xb` and length `L`. -/
structure VSpec (cyc : Bool) (L : Nat) (xb : Nat → Option Bool) (c : VCert) : Prop where
  parse : ParseOK L xb c.pt
  three : ∀ j, j < c.pt.m → c.pt.kk j ≤ 3
  sat : ∀ j, j < c.pt.m → c.tsel j < c.pt.kk j ∧
    (c.A (c.pt.V (c.pt.O j + c.tsel j)) = 1 ↔ c.pt.S (c.pt.O j + c.tsel j) = 1)
  varLt : ∀ e, e < c.pt.M → c.pt.V e < c.K
  varZero : c.pt.M = 0 → c.K = 0
  varMax : 0 < c.pt.M → c.estar < c.pt.M ∧ c.pt.V c.estar + 1 = c.K
  n2 : c.et.n2 = c.pt.M + (if cyc then c.K else 0)
  endOcc : ∀ e, e < c.pt.M →
    c.et.EN (2 * e) = 2 * c.pt.V e ∧ c.et.EN (2 * e + 1) = 2 * c.pt.J e + 1
  endCyc : cyc = true → ∀ i, i < c.K →
    c.et.EN (2 * (c.pt.M + i)) = 2 * i ∧
      c.et.EN (2 * (c.pt.M + i) + 1) = (if i + 1 = c.K then 0 else 2 * (i + 1))
  embed : EmbedOK c.et

/-- The graph to embed. -/
def targetGraph (cyc : Bool) (f : CNF) : List (Sum Nat Nat × Sum Nat Nat) :=
  incidenceGraph f ++ (if cyc then variableCycle f else [])

/-- The code of a vertex. -/
def encodeEnd : Sum Nat Nat → Nat
  | .inl v => 2 * v
  | .inr j => 2 * j + 1

theorem decodeEnd_encodeEnd (v : Sum Nat Nat) : decodeEnd (encodeEnd v) = v := by
  cases v with
  | inl v => simp [decodeEnd, encodeEnd]
  | inr j =>
    simp only [decodeEnd, encodeEnd]
    simp; omega

theorem decodeEnd_injective' : ∀ a b, decodeEnd a = decodeEnd b → a = b :=
  fun _ _ h => decodeEnd_injective h

/-! ## Facts about the formula read off parsing tables -/

section fml

variable {L : Nat} {xb : Nat → Option Bool} {t : ParseTables} (h : ParseOK L xb t)
include h

theorem fml_prefix (j : Nat) (hj : j ≤ t.m) :
    ((t.fml.map List.length).take j).sum = t.O j := by
  induction j with
  | zero => simp [h.O_zero]
  | succ j ih =>
    rw [sum_take_succ _ _ (by simp [ParseTables.fml]; omega), ih (by omega), h.O_succ j (by omega)]
    simp [ParseTables.fml, ParseTables.clause]

theorem fml_incidence (e : Nat) (he : e < t.M) :
    (incidenceGraph t.fml)[e]? = some (Sum.inl (t.V e), Sum.inr (t.J e)) := by
  obtain ⟨hJ, hT, hsum⟩ := h.occ e he
  have hj : t.J e < t.fml.length := by simp [ParseTables.fml]; exact hJ
  have ht : t.T e < t.fml[t.J e].length := by
    simp [ParseTables.fml, ParseTables.clause]; exact hT
  have := incidenceGraph_getElem? t.fml (t.J e) (t.T e) hj ht
  rw [fml_prefix h _ (by omega), hsum] at this
  rw [this]
  simp [ParseTables.fml, ParseTables.clause, ParseTables.lit, hsum]

theorem fml_incidence_length : (incidenceGraph t.fml).length = t.M := by
  rw [incidenceGraph_length]
  have := fml_prefix h t.m (Nat.le_refl _)
  rw [List.take_of_length_le (by simp [ParseTables.fml])] at this
  rw [this, h.O_last]

theorem fml_mem (c : Clause) (hc : c ∈ t.fml) (l : Literal) (hl : l ∈ c) :
    ∃ e, e < t.M ∧ l = t.lit e := by
  simp only [ParseTables.fml, List.mem_map, List.mem_range] at hc
  obtain ⟨j, hj, rfl⟩ := hc
  simp only [ParseTables.clause, List.mem_map, List.mem_range] at hl
  obtain ⟨i, hi, rfl⟩ := hl
  exact ⟨t.O j + i, (h.occ_of hj hi).1, rfl⟩

end fml

/-! ## Soundness -/

theorem VSpec.sound {cyc : Bool} {x : Word} {c : VCert}
    (h : VSpec cyc x.length (fun p => x[p]?) c) :
    ∃ f, encode f = x ∧ IsThreeCNF f ∧ Satisfiable f ∧ PlanarGraph (targetGraph cyc f) := by
  have hp := h.parse
  refine ⟨c.pt.fml, hp.encode_eq, ParseTables.three h.three, ?_, ?_⟩
  · -- satisfiability
    refine ⟨fun v => c.A v == 1, ?_⟩
    simp only [evalCNF, List.all_eq_true]
    intro cl hcl
    simp only [ParseTables.fml, List.mem_map, List.mem_range] at hcl
    obtain ⟨j, hj, rfl⟩ := hcl
    obtain ⟨hts, hiff⟩ := h.sat j hj
    simp only [evalClause, List.any_eq_true]
    refine ⟨c.pt.lit (c.pt.O j + c.tsel j), ?_, ?_⟩
    · simp only [ParseTables.clause, List.mem_map, List.mem_range]
      exact ⟨c.tsel j, hts, rfl⟩
    · simp only [ParseTables.lit, evalLiteral]
      by_cases hS : c.pt.S (c.pt.O j + c.tsel j) = 1
      · simp [hS, hiff.mpr hS]
      · have : c.A (c.pt.V (c.pt.O j + c.tsel j)) ≠ 1 := fun hA => hS (hiff.mp hA)
        simp [hS, this]
  · -- planarity
    have hK : variableCount c.pt.fml = c.K := by
      apply variableCount_eq
      · intro cl hcl l hl
        obtain ⟨e, he, rfl⟩ := fml_mem hp cl hcl l hl
        exact h.varLt e he
      · by_cases hM : c.pt.M = 0
        · exact Or.inl (h.varZero hM)
        · right
          obtain ⟨hes, hV⟩ := h.varMax (by omega)
          obtain ⟨hJ, hT, hsum⟩ := hp.occ _ hes
          refine ⟨c.pt.clause (c.pt.J c.estar), ?_, c.pt.lit c.estar, ?_, ?_⟩
          · simp only [ParseTables.fml, List.mem_map, List.mem_range]
            exact ⟨_, hJ, rfl⟩
          · simp only [ParseTables.clause, List.mem_map, List.mem_range]
            exact ⟨c.pt.T c.estar, hT, by rw [hsum]⟩
          · simpa [ParseTables.lit] using hV
    have hlen : (targetGraph cyc c.pt.fml).length = c.et.n2 := by
      rw [h.n2, targetGraph, List.length_append, fml_incidence_length hp]
      cases cyc <;> simp [variableCycle_length, hK]
    apply h.embed.planarGraph hlen decodeEnd decodeEnd_injective'
    intro d hd
    have hinc := fml_incidence_length hp
    by_cases hdM : d < 2 * c.pt.M
    · rw [targetGraph, halfEdgeEnd_append_left _ _ _ (by rw [hinc]; exact hdM)]
      obtain ⟨e, he⟩ : ∃ e, d = 2 * e ∨ d = 2 * e + 1 := ⟨d / 2, by omega⟩
      have heM : e < c.pt.M := by omega
      obtain ⟨h0, h1⟩ := halfEdgeEnd_of_getElem? _ e _ _ (fml_incidence hp e heM)
      obtain ⟨hE0, hE1⟩ := h.endOcc e heM
      rcases he with rfl | rfl
      · rw [h0, hE0]; simp [decodeEnd]
      · rw [h1, hE1]; simp only [decodeEnd]
        simp; omega
    · have hcyc : cyc = true := by
        cases cyc
        · rw [h.n2] at hd; simp at hd; omega
        · rfl
      subst hcyc
      rw [targetGraph, halfEdgeEnd_append_right _ _ _ (by rw [hinc]; omega)]
      simp only [ite_true]
      rw [h.n2] at hd
      simp only [ite_true] at hd
      obtain ⟨i, hi⟩ : ∃ i, d = 2 * (c.pt.M + i) ∨ d = 2 * (c.pt.M + i) + 1 :=
        ⟨d / 2 - c.pt.M, by omega⟩
      have hiK : i < c.K := by omega
      have hcyc := variableCycle_getElem? c.pt.fml i (by rw [hK]; exact hiK)
      rw [hK] at hcyc
      obtain ⟨h0, h1⟩ := halfEdgeEnd_of_getElem? _ i _ _ hcyc
      obtain ⟨hE0, hE1⟩ := h.endCyc rfl i hiK
      rw [hinc]
      rcases hi with rfl | rfl
      · rw [show 2 * (c.pt.M + i) - 2 * c.pt.M = 2 * i by omega, h0, hE0]; simp [decodeEnd]
      · rw [show 2 * (c.pt.M + i) + 1 - 2 * c.pt.M = 2 * i + 1 by omega, h1, hE1]
        by_cases hlast : i + 1 = c.K
        · simp [hlast, decodeEnd]
        · simp only [hlast, ite_false, decodeEnd]; simp

/-! ## Completeness -/

/-- The certificate tables, numbered: `0` holds the scalars `m, M, K, estar, n2`. -/
def VCert.tab (c : VCert) : Nat → Nat → Nat
  | 0, i => if i = 0 then c.pt.m else if i = 1 then c.pt.M else if i = 2 then c.K
      else if i = 3 then c.estar else if i = 4 then c.et.n2 else 0
  | 1, i => c.pt.kk i
  | 2, i => c.pt.O i
  | 3, i => c.pt.P i
  | 4, i => c.tsel i
  | 5, i => c.pt.J i
  | 6, i => c.pt.T i
  | 7, i => c.pt.V i
  | 8, i => c.pt.S i
  | 9, i => c.pt.Q i
  | 10, i => c.A i
  | 11, i => c.et.EN i
  | 12, i => c.et.N i
  | 13, i => c.et.F i
  | 14, i => c.et.R i
  | 15, i => c.et.FL i
  | 16, i => c.et.CL i
  | 17, i => c.et.D i
  | 18, i => c.et.SU i
  | 19, i => c.et.cR i
  | 20, i => c.et.cF i
  | 21, i => c.et.cC i
  | _, _ => 0

/-- Number of tables. -/
def numTables : Nat := 22

/-- Entries per table, for a word of length `L`. -/
def tableSize (L : Nat) : Nat := 4 * L + 4

/-- Width of each entry. -/
def fieldWidth (L : Nat) : Nat := 8 * L + 8

/-- All entries are below the field width. -/
def VCert.Bounded (L : Nat) (c : VCert) : Prop :=
  ∀ τ, τ < numTables → ∀ i, i < tableSize L → c.tab τ i < fieldWidth L

theorem length_wv_le_of_mem {α : Type} (enc : α → List Bool) (xs : List α) (a : α)
    (h : a ∈ xs) : (enc a).length ≤ (writeValues enc xs).length := by
  induction xs with
  | nil => simp at h
  | cons b xs ih =>
    rcases List.mem_cons.mp h with rfl | h'
    · simp [writeValues]
    · have := ih h'; simp [writeValues]; omega

theorem length_wv_take_le {α : Type} (enc : α → List Bool) (xs : List α) (i : Nat) :
    (writeValues enc (xs.take i)).length ≤ (writeValues enc xs).length := by
  rw [writeValues_take_drop enc xs i, List.length_append]; omega

theorem length_encodeClause' (c : Clause) :
    (encodeClause c).length = c.length + 1 + (writeValues encodeLiteral c).length := by
  simp [encodeClause, writeList, length_writeNat]

theorem length_encode' (f : CNF) :
    (encode f).length = f.length + 1 + (writeValues encodeClause f).length := by
  simp [encode, writeList, length_writeNat]

theorem var_lt_length (f : CNF) (cl : Clause) (hc : cl ∈ f) (l : Literal) (hl : l ∈ cl) :
    l.var + 2 ≤ (encode f).length := by
  have h1 := length_wv_le_of_mem encodeLiteral cl l hl
  have h2 := length_wv_le_of_mem encodeClause f cl hc
  rw [length_encodeLiteral] at h1
  rw [length_encodeClause'] at h2
  rw [length_encode']; omega

theorem sum_take_le (ks : List Nat) (i : Nat) : (ks.take i).sum ≤ ks.sum := by
  rw [← List.take_append_drop i ks, List.sum_append]
  simp only [List.take_append_drop]
  omega

theorem locate_fst_le (ks : List Nat) (e : Nat) : (locate ks e).1 ≤ ks.length := by
  induction ks generalizing e with
  | nil => simp [locate]
  | cons k ks ih =>
    simp only [locate]
    split
    · simp
    · simp; have := ih (e - k); omega

theorem locate_snd_le (ks : List Nat) (e : Nat) : (locate ks e).2 ≤ e := by
  induction ks generalizing e with
  | nil => simp [locate]
  | cons k ks ih =>
    simp only [locate]
    split
    · simp
    · simp only; have := ih (e - k); omega

section canonBounds

variable (f : CNF)

theorem canon_kk_le (i : Nat) : (canonTables f).kk i ≤ (encode f).length := by
  simp only [canonTables]
  cases h : f[i]? with
  | none => simp
  | some cl =>
    simp only [Option.getD_some]
    have hc : cl ∈ f := List.mem_of_getElem? h
    have h2 := length_wv_le_of_mem encodeClause f cl hc
    have h3 := length_encodeClause_ge cl
    rw [length_encode']; omega

theorem canon_V_le (e : Nat) : (canonTables f).V e ≤ (encode f).length := by
  simp only [canonTables]
  cases h : f[(locate (f.map List.length) e).1]? with
  | none => simp
  | some cl =>
    simp only [Option.getD_some]
    cases h2 : cl[(locate (f.map List.length) e).2]? with
    | none => simp
    | some l =>
      simp only [Option.getD_some]
      have := var_lt_length f cl (List.mem_of_getElem? h) l (List.mem_of_getElem? h2)
      omega

theorem canon_Q_le (e : Nat) : (canonTables f).Q e ≤ (encode f).length + 1 := by
  simp only [canonTables]
  rw [length_encode']
  cases h : f[(locate (f.map List.length) e).1]? with
  | none =>
    simp only [Option.getD_none, List.length_nil, List.take_nil]
    have := length_wv_take_le encodeClause f (locate (f.map List.length) e).1
    simp only [writeValues, List.length_nil]; omega
  | some cl =>
    simp only [Option.getD_some]
    have hj : (locate (f.map List.length) e).1 < f.length := by
      rcases Nat.lt_or_ge (locate (f.map List.length) e).1 f.length with h' | h'
      · exact h'
      · simp [List.getElem?_eq_none h'] at h
    have hcl : f[(locate (f.map List.length) e).1] = cl := by
      rw [List.getElem?_eq_getElem hj] at h; exact Option.some.inj h
    have hsucc := length_writeValues_take_succ encodeClause f _ hj
    have hle := length_wv_take_le encodeClause f ((locate (f.map List.length) e).1 + 1)
    rw [hcl, length_encodeClause'] at hsucc
    have hlit := length_wv_take_le encodeLiteral cl (locate (f.map List.length) e).2
    omega

theorem canon_P_le (j : Nat) : (canonTables f).P j ≤ (encode f).length := by
  simp only [canonTables]
  have := length_wv_take_le encodeClause f j
  rw [length_encode']; omega

theorem canon_O_le (j : Nat) : (canonTables f).O j ≤ (canonTables f).M := by
  rw [canon_O', canon_M]; exact sum_take_le _ _

end canonBounds

theorem mem_incidenceGraph {f : CNF} {u w : Sum Nat Nat} (h : (u, w) ∈ incidenceGraph f) :
    ∃ j, j < f.length ∧ ∃ l ∈ f[j]?.getD [], u = Sum.inl l.var ∧ w = Sum.inr j := by
  unfold incidenceGraph at h
  obtain ⟨⟨cl, j⟩, hp, he⟩ := List.mem_flatMap.mp h
  rw [List.mem_zipIdx_iff_getElem?] at hp
  simp only at hp
  obtain ⟨l, hl, hle⟩ := List.mem_map.mp he
  have hj : j < f.length := by
    rcases Nat.lt_or_ge j f.length with h' | h'
    · exact h'
    · simp [List.getElem?_eq_none h'] at hp
  refine ⟨j, hj, l, by rw [hp]; exact hl, ?_⟩
  simp only [Prod.mk.injEq] at hle
  exact ⟨hle.1.symm, hle.2.symm⟩

theorem targetGraph_end_bound {cyc : Bool} {f : CNF} {d : Nat} {v : Sum Nat Nat}
    (h : halfEdgeEnd (targetGraph cyc f) d = some v) :
    encodeEnd v ≤ 2 * (encode f).length + 1 := by
  unfold halfEdgeEnd at h
  cases he : (targetGraph cyc f)[d / 2]? with
  | none => simp [he] at h
  | some e =>
    rw [he] at h
    simp only [Option.map_some, Option.some.injEq] at h
    have hmem : e ∈ targetGraph cyc f := List.mem_of_getElem? he
    have hv : v = e.1 ∨ v = e.2 := by
      cases hb : Nat.beq (d % 2) 0 <;> simp [hb] at h <;> simp [h]
    rw [targetGraph, List.mem_append] at hmem
    rcases hmem with hinc | hcyc
    · obtain ⟨j, hj, l, hl, hu, hw⟩ := mem_incidenceGraph (u := e.1) (w := e.2) hinc
      have hlv : l.var + 2 ≤ (encode f).length := by
        rw [List.getElem?_eq_getElem hj, Option.getD_some] at hl
        exact var_lt_length f f[j] (List.getElem_mem hj) l hl
      have hjL : j < (encode f).length := by
        have := (canon_ok f).m_le
        simp only [canonTables] at this; omega
      rcases hv with rfl | rfl
      · rw [hu]; simp [encodeEnd]; omega
      · rw [hw]; simp [encodeEnd]; omega
    · cases cyc
      · simp at hcyc
      · simp only [ite_true, variableCycle, List.mem_map, List.mem_range] at hcyc
        obtain ⟨i, hi, rfl⟩ := hcyc
        have hK : variableCount f ≤ (encode f).length := by
          rcases (variableCount_spec f).2 with h0 | ⟨cl, hcl, l, hl, hlK⟩
          · omega
          · have := var_lt_length f cl hcl l hl; omega
        have hmod : (i + 1) % variableCount f < variableCount f := Nat.mod_lt _ (by omega)
        rcases hv with rfl | rfl
        · simp [encodeEnd]; omega
        · simp [encodeEnd]; omega

theorem canon_occ_lit (f : CNF) (j t : Nat) (hj : j < f.length) (ht : t < f[j].length) :
    (canonTables f).O j + t < (canonTables f).M ∧
      (canonTables f).V ((canonTables f).O j + t) = f[j][t].var ∧
      ((canonTables f).S ((canonTables f).O j + t) = 1 ↔ f[j][t].positive = true) := by
  have hok := canon_ok f
  have hl := canon_locate' f j t hj ht
  obtain ⟨hV, hS, _, _⟩ := canon_VS_of_locate f _ j t hl hj ht
  refine ⟨(hok.occ_of (by simp [canonTables]; exact hj) (by rw [canon_kk f j hj]; exact ht)).1,
    hV, ?_⟩
  rw [← hS]; simp

theorem vspec_complete {cyc : Bool} {f : CNF} (h3 : IsThreeCNF f) (hs : Satisfiable f)
    (hp : PlanarGraph (targetGraph cyc f)) :
    ∃ c : VCert, VSpec cyc (encode f).length (fun p => (encode f)[p]?) c ∧
      VCert.Bounded (encode f).length c := by
  obtain ⟨a, ha⟩ := hs
  have hok := canon_ok f
  have hfml := canon_fml f
  let pt := canonTables f
  let K := variableCount f
  obtain ⟨hKlt, hKmax⟩ := variableCount_spec f
  -- a literal attaining the variable count
  have hest : ∃ e, (0 < pt.M → e < pt.M ∧ pt.V e + 1 = K) ∧ e ≤ pt.M := by
    rcases hKmax with h0 | ⟨cl, hcl, l, hl, hlK⟩
    · refine ⟨0, fun hM => ?_, Nat.zero_le _⟩
      exfalso
      -- a literal exists, so the count is positive
      have : ∃ cl ∈ f, ∃ l, l ∈ cl := by
        have hsum : 0 < (f.map List.length).sum := hM
        obtain ⟨j, hj, hpos⟩ : ∃ j, ∃ hj : j < f.length, 0 < f[j].length := by
          apply Classical.byContradiction
          intro hno
          have hz : ∀ g : CNF, (∀ cl ∈ g, cl.length = 0) → (g.map List.length).sum = 0 := by
            intro g hg
            induction g with
            | nil => rfl
            | cons cl g ih =>
              simp only [List.map_cons, List.sum_cons]
              rw [hg cl List.mem_cons_self, ih (fun c hc => hg c (List.mem_cons_of_mem cl hc))]
          have : (f.map List.length).sum = 0 := by
            apply hz
            intro cl hcl
            obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hcl
            apply Classical.byContradiction
            intro hne
            exact hno ⟨j, hj, by omega⟩
          omega
        exact ⟨f[j], List.getElem_mem hj, f[j][0], List.getElem_mem hpos⟩
      obtain ⟨cl, hcl, l, hl⟩ := this
      have := hKlt cl hcl l hl
      omega
    · obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hcl
      obtain ⟨t, ht, rfl⟩ := List.mem_iff_getElem.mp hl
      obtain ⟨he, hV, _⟩ := canon_occ_lit f j t hj ht
      exact ⟨pt.O j + t, fun _ => ⟨he, by rw [hV]; exact hlK⟩, Nat.le_of_lt he⟩
  let estar := Classical.choose hest
  have hestar := Classical.choose_spec hest
  -- satisfied slots
  have hsel : ∀ j (hj : j < f.length), ∃ t, ∃ ht : t < f[j].length,
      evalLiteral a (f[j][t]'ht) = true := by
    intro j hj
    have hc : evalClause a f[j] = true := by
      simp only [evalCNF, List.all_eq_true] at ha
      exact ha f[j] (List.getElem_mem hj)
    simp only [evalClause, List.any_eq_true] at hc
    obtain ⟨l, hl, hle⟩ := hc
    obtain ⟨t, ht, rfl⟩ := List.mem_iff_getElem.mp hl
    exact ⟨t, ht, hle⟩
  let tsel : Nat → Nat := fun j => if hj : j < f.length then Classical.choose (hsel j hj) else 0
  have htsel : ∀ j (hj : j < f.length), ∃ ht : tsel j < f[j].length,
      evalLiteral a (f[j][tsel j]'ht) = true := by
    intro j hj
    simp only [tsel, hj, dite_true]
    exact Classical.choose_spec (hsel j hj)
  -- the embedding
  obtain ⟨et, hn2, hemb, hends, hbnd, hcnt, hzero⟩ :=
    embed_complete encodeEnd decodeEnd decodeEnd_encodeEnd hp
  have hinc_len : (incidenceGraph f).length = pt.M := by
    rw [incidenceGraph_length]; rfl
  have hinc : ∀ e, e < pt.M → (incidenceGraph f)[e]? = some (Sum.inl (pt.V e), Sum.inr (pt.J e)) := by
    intro e he
    have := fml_incidence hok e he
    rw [hfml] at this; exact this
  have hlenT : (targetGraph cyc f).length = pt.M + (if cyc then K else 0) := by
    rw [targetGraph, List.length_append, hinc_len]
    cases cyc <;> simp [variableCycle_length, K]
  refine ⟨⟨pt, K, estar, fun v => if a v then 1 else 0, tsel, et⟩, ?_, ?_⟩
  · constructor
    · exact hok
    · intro j hj
      simp only [pt, canonTables] at hj
      simp only [pt, canon_kk f j hj]
      exact h3 f[j] (List.getElem_mem hj)
    · intro j hj
      simp only [pt, canonTables] at hj
      obtain ⟨hts, hev⟩ := htsel j hj
      obtain ⟨_, hV, hS⟩ := canon_occ_lit f j (tsel j) hj hts
      refine ⟨by simp only [pt]; rw [canon_kk f j hj]; exact hts, ?_⟩
      simp only [pt]
      rw [hV, hS]
      simp only [evalLiteral] at hev
      cases hpos : f[j][tsel j].positive <;> simp [hpos] at hev ⊢ <;> simp [hev]
    · intro e he
      have hsum : e < (f.map List.length).sum := he
      obtain ⟨h1, h2, h3'⟩ := locate_spec _ e hsum
      have hj : (locate (f.map List.length) e).1 < f.length := by simpa using h1
      have ht : (locate (f.map List.length) e).2 < f[(locate (f.map List.length) e).1].length := by
        rw [List.getElem!_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hj] at h2
        simpa using h2
      obtain ⟨hV, _, _, _⟩ := canon_VS_of_locate f e _ _ rfl hj ht
      simp only [pt]; rw [hV]
      exact hKlt _ (List.getElem_mem hj) _ (List.getElem_mem ht)
    · intro hM
      rcases hKmax with h0 | ⟨cl, hcl, l, hl, _⟩
      · exact h0
      · exfalso
        obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hcl
        obtain ⟨t, ht, rfl⟩ := List.mem_iff_getElem.mp hl
        have := (canon_occ_lit f j t hj ht).1
        simp only [pt] at hM; omega
    · exact hestar.1
    · simp only; rw [hn2, hlenT]
    · intro e he
      dsimp only at he ⊢
      have hti := hinc e he
      obtain ⟨h0, h1⟩ := halfEdgeEnd_of_getElem? _ e _ _ hti
      rw [targetGraph] at hends
      have he0 : 2 * e < 2 * et.n2 := by rw [hn2, hlenT]; omega
      have he1 : 2 * e + 1 < 2 * et.n2 := by rw [hn2, hlenT]; omega
      obtain ⟨v0, hv0, hE0⟩ := hends (2 * e) he0
      obtain ⟨v1, hv1, hE1⟩ := hends (2 * e + 1) he1
      rw [halfEdgeEnd_append_left _ _ _ (by rw [hinc_len]; omega), h0] at hv0
      rw [halfEdgeEnd_append_left _ _ _ (by rw [hinc_len]; omega), h1] at hv1
      rw [← Option.some.inj hv0] at hE0
      rw [← Option.some.inj hv1] at hE1
      exact ⟨hE0, hE1⟩
    · intro hcyc i hi
      subst hcyc
      dsimp only at hi ⊢
      have hcy := variableCycle_getElem? f i hi
      obtain ⟨h0, h1⟩ := halfEdgeEnd_of_getElem? _ i _ _ hcy
      rw [targetGraph] at hends
      simp only [ite_true] at hends hlenT
      have he0 : 2 * (pt.M + i) < 2 * et.n2 := by rw [hn2, hlenT]; omega
      have he1 : 2 * (pt.M + i) + 1 < 2 * et.n2 := by rw [hn2, hlenT]; omega
      obtain ⟨v0, hv0, hE0⟩ := hends _ he0
      obtain ⟨v1, hv1, hE1⟩ := hends _ he1
      rw [halfEdgeEnd_append_right _ _ _ (by rw [hinc_len]; omega), hinc_len,
        show 2 * (pt.M + i) - 2 * pt.M = 2 * i by omega, h0] at hv0
      rw [halfEdgeEnd_append_right _ _ _ (by rw [hinc_len]; omega), hinc_len,
        show 2 * (pt.M + i) + 1 - 2 * pt.M = 2 * i + 1 by omega, h1] at hv1
      rw [← Option.some.inj hv0] at hE0
      rw [← Option.some.inj hv1] at hE1
      refine ⟨hE0, ?_⟩
      rw [hE1]
      by_cases hlast : i + 1 = variableCount f
      · simp [hlast, encodeEnd, K]
      · simp [hlast, encodeEnd, K]
    · exact hemb
  · -- bounds
    intro τ hτ i hi
    simp only [numTables] at hτ
    simp only [tableSize] at hi
    simp only [fieldWidth]
    have hm := hok.m_le
    have hM := hok.M_le
    have hKL : K ≤ (encode f).length := by
      rcases hKmax with h0 | ⟨cl, hcl, l, hl, hlK⟩
      · simp only [K]; omega
      · have := var_lt_length f cl hcl l hl; simp only [K]; omega
    have hn2L : et.n2 ≤ 2 * (encode f).length := by
      rw [hn2, targetGraph, List.length_append, incidenceGraph_length]
      have hM' : (f.map List.length).sum ≤ (encode f).length := hM
      cases cyc <;> simp [variableCycle_length] <;> simp only [K] at hKL <;> omega
    have hτ' : τ = 0 ∨ τ = 1 ∨ τ = 2 ∨ τ = 3 ∨ τ = 4 ∨ τ = 5 ∨ τ = 6 ∨ τ = 7 ∨ τ = 8 ∨
        τ = 9 ∨ τ = 10 ∨ τ = 11 ∨ τ = 12 ∨ τ = 13 ∨ τ = 14 ∨ τ = 15 ∨ τ = 16 ∨ τ = 17 ∨
        τ = 18 ∨ τ = 19 ∨ τ = 20 ∨ τ = 21 := by omega
    have hest' := hestar.2
    rcases hτ' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simp only [VCert.tab]
      dsimp only [pt, K, estar]
      repeat' split
      all_goals omega
    · show (canonTables f).kk i < _; have := canon_kk_le f i; omega
    · show (canonTables f).O i < _; have := canon_O_le f i; omega
    · show (canonTables f).P i < _; have := canon_P_le f i; omega
    · show tsel i < _
      by_cases hif : i < f.length
      · obtain ⟨ht, _⟩ := htsel i hif
        have := h3 f[i] (List.getElem_mem hif)
        omega
      · simp only [tsel, hif, dite_false]; omega
    · show (locate (f.map List.length) i).1 < _
      have := locate_fst_le (f.map List.length) i
      simp only [canonTables] at hm
      simp only [List.length_map] at this; omega
    · show (locate (f.map List.length) i).2 < _
      have := locate_snd_le (f.map List.length) i; omega
    · show (canonTables f).V i < _; have := canon_V_le f i; omega
    · show (canonTables f).S i < _; simp only [canonTables]; split <;> omega
    · show (canonTables f).Q i < _; have := canon_Q_le f i; omega
    · show (if a i then 1 else 0) < _; split <;> omega
    · show et.EN i < _
      by_cases hd : i < 2 * et.n2
      · obtain ⟨v, hv, hE⟩ := hends i hd
        rw [hE]
        have := targetGraph_end_bound hv
        omega
      · rw [(hzero i (by omega)).1]; omega
    · show et.N i < _
      by_cases hd : i < 2 * et.n2
      · have := (hbnd i hd).1; omega
      · rw [(hzero i (by omega)).2.1]; omega
    · show et.F i < _
      by_cases hd : i < 2 * et.n2
      · have := (hbnd i hd).2.1; omega
      · rw [(hzero i (by omega)).2.2.1]; omega
    · show et.R i < _
      by_cases hd : i < 2 * et.n2
      · have := (hbnd i hd).2.2.1; omega
      · rw [(hzero i (by omega)).2.2.2.1]; omega
    · show et.FL i < _
      by_cases hd : i < 2 * et.n2
      · have := (hbnd i hd).2.2.2.1; omega
      · rw [(hzero i (by omega)).2.2.2.2.1]; omega
    · show et.CL i < _
      by_cases hd : i < 2 * et.n2
      · have := (hbnd i hd).2.2.2.2.1; omega
      · rw [(hzero i (by omega)).2.2.2.2.2.1]; omega
    · show et.D i < _
      by_cases hd : i < 2 * et.n2
      · have := (hbnd i hd).2.2.2.2.2.1; omega
      · rw [(hzero i (by omega)).2.2.2.2.2.2.1]; omega
    · show et.SU i < _
      by_cases hd : i < 2 * et.n2
      · have := (hbnd i hd).2.2.2.2.2.2; omega
      · rw [(hzero i (by omega)).2.2.2.2.2.2.2]; omega
    · show et.cR i < _; have := (hcnt i).1; omega
    · show et.cF i < _; have := (hcnt i).2.1; omega
    · show et.cC i < _; have := (hcnt i).2.2; omega

end Complexity.Planar
