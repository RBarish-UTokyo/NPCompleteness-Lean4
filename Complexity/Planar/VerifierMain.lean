module

public import Complexity.Planar.VerifierChk
public import Complexity.Planar.VerifierTransfer
public import Complexity.Planar.EmitDecide
import Lean.Elab.Tactic.Omega

/-!
# The planar 3-SAT verifier

The verifier program reads `u = pairWords x w`.  It tries every length `L` with
`|u| = 2 L + 1 + certLen L`; for that `L` it checks the header `1^L 0` (which pins `L = |x|`),
that all certificate fields are well formed, reads the scalars and runs all checks of
`VSpec`.  It emits one empty clause for the matching `L` and one more for every failed check,
so the output is `[[]]` exactly when the certificate passes.  The canonical encoding of a
certificate from `vspec_complete` passes, which gives membership in NP of both planar
3-SAT languages.
-/

@[expose] public section

namespace Complexity.Planar.Vf

open Chk SAT StackTableauEmitter

/-! ## All checks together -/

/-- The checks of `VSpec`, in the order of its fields. -/
def checks (cyc : Bool) : List C :=
  [cMle, cMMle, cHead, cHeadEnd, cO0, cOsucc, cOlast, cP0, cLen, cLenEnd, cEmpty, cFirst, cOcc,
   cSign, cVar, cVarEnd, cNext, cLast, cPlast, cThree, cSat, cVarLt, cVarZero, cVarMax, cN2 cyc,
   cEndOcc, cEndCyc cyc, cBound, cEdgeK, cNodeEnd, cRankNext, cRankLt, cRankPrev, cRankUnique,
   cFace, cComp, cSucc, cCount 19 14 false, cCount 20 15 true, cCount 21 16 true, cFinal]

/-- The successor condition of `EmbedOK`, split by the parity of the dart. -/
theorem succ_iff (t : EmbedTables) :
    (∀ h, h < t.n2 →
      (0 < t.D (2 * h) →
        t.SU (2 * h) < 2 * t.n2 ∧ t.D (t.SU (2 * h)) + 1 = t.D (2 * h) ∧
        t.CL (t.SU (2 * h)) = t.CL (2 * h) ∧
        (t.SU (2 * h) = 2 * h + 1 ∨ t.SU (2 * h) = t.N (2 * h) ∨ t.SU (2 * h) = t.F (2 * h))) ∧
      (0 < t.D (2 * h + 1) →
        t.SU (2 * h + 1) < 2 * t.n2 ∧ t.D (t.SU (2 * h + 1)) + 1 = t.D (2 * h + 1) ∧
        t.CL (t.SU (2 * h + 1)) = t.CL (2 * h + 1) ∧
        (t.SU (2 * h + 1) = 2 * h ∨ t.SU (2 * h + 1) = t.N (2 * h + 1) ∨
          t.SU (2 * h + 1) = t.F (2 * h + 1)))) ↔
    (∀ d, d < 2 * t.n2 → 0 < t.D d →
      t.SU d < 2 * t.n2 ∧ t.D (t.SU d) + 1 = t.D d ∧ t.CL (t.SU d) = t.CL d ∧
        (t.SU d = ed d ∨ t.SU d = t.N d ∨ t.SU d = t.F d)) := by
  constructor
  · intro hh d hd hD
    obtain ⟨j, hj⟩ : ∃ j, d = 2 * j ∨ d = 2 * j + 1 := ⟨d / 2, by omega⟩
    rcases hj with rfl | rfl
    · rw [ed_even]; exact (hh j (by omega)).1 hD
    · rw [ed_odd]; exact (hh j (by omega)).2 hD
  · intro hd j hj
    refine ⟨fun hD => ?_, fun hD => ?_⟩
    · have := hd (2 * j) (by omega) hD; rw [ed_even] at this; exact this
    · have := hd (2 * j + 1) (by omega) hD; rw [ed_odd] at this; exact this

section asm

variable {u : List Bool} {L : Nat} {ρ : Sl → Nat} (hg : GlobalWF u L) (he : EnvOK u L ρ)
include hg he

/-- **All checks hold** exactly when the decoded certificate satisfies `VSpec`. -/
theorem s_checks (cyc : Bool) :
    Holds u (allOf (checks cyc)) ρ ↔ VSpec cyc L (xbits u L) (decodeCert u L) := by
  simp only [holds_allOf, checks, List.forall_mem_cons]
  rw [s_Mle hg he, s_MMle hg he, s_head hg he, s_headEnd hg he, s_O0 hg he, s_Osucc hg he,
    s_Olast hg he, s_P0 hg he, s_len hg he, s_lenEnd hg he, s_empty hg he, s_first hg he,
    s_occ hg he, s_sign hg he, s_var hg he, s_varEnd hg he, s_next hg he, s_last hg he,
    s_Plast hg he, s_three hg he, s_sat hg he, s_varLt hg he, s_varZero hg he, s_varMax hg he,
    s_n2 hg he, s_endOcc hg he, s_endCyc hg he, s_bound hg he, s_edgeK hg he, s_nodeEnd hg he,
    s_rankNext hg he, s_rankLt hg he, s_rankPrev hg he, s_rankUnique hg he, s_face hg he,
    s_comp hg he, s_succ hg he, s_count hg he, s_count hg he, s_count hg he, s_final hg he,
    succ_iff]
  constructor
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
      h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36, h37,
      h38, h39, h40, h41, -⟩
    exact ⟨⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19⟩,
      h20, h21, h22, h23, h24, h25, h26, h27,
      ⟨h28, h29, h30, h31, h32, h33, h34, h35, h36, h37, h38, h39, h40, h41⟩⟩
  · rintro ⟨⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18,
      h19⟩, h20, h21, h22, h23, h24, h25, h26, h27,
      ⟨h28, h29, h30, h31, h32, h33, h34, h35, h36, h37, h38, h39, h40, h41⟩⟩
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
      h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36, h37,
      h38, h39, h40, h41, by simp⟩

end asm

/-! ## Well-formed fields, the header and the scalars -/

/-- The offset of field `q` (in slot `tq`). -/
def fo : X := base + E tq * Bx

/-- All fields of the certificate are well formed. -/
def wfCheck : C :=
  .all tq (k 22 * Dx) (.both
    (.all tb (Bx - k 1) (.bit (fo + E tb) (.bit (fo + E tb + k 1) .ok .ok .fail)
      (.bit (fo + E tb + k 1) .ok .ok .fail) .ok))
    (.bit (fo + Bx - k 1) .ok .ok .fail))

/-- The word starts with `1^L 0`. -/
def header : C := .both (.all ti (E sL) (reqBit (E ti) true)) (reqBit (E sL) false)

/-- Read the five scalars. -/
def readScalars (body : C) : C :=
  rd 0 (k 0) sm (rd 0 (k 1) sM (rd 0 (k 2) sK (rd 0 (k 3) sE (rd 0 (k 4) sn body))))

/-- The whole verifier for a guessed length in slot `sL`. -/
def verifier (cyc : Bool) : C := .both header (.both wfCheck (readScalars (allOf (checks cyc))))

theorem holds_notOne (u : List Bool) (p : X) (ρ : Sl → Nat) :
    Holds u (.bit p .ok .ok .fail) ρ ↔ NotOne u (p.eval ρ) := by
  simp only [Holds, NotOne]
  split <;> simp_all

theorem holds_whenNotOne (u : List Bool) (p : X) (c : C) (ρ : Sl → Nat) :
    Holds u (.bit p c c .ok) ρ ↔ (NotOne u (p.eval ρ) → Holds u c ρ) := by
  simp only [Holds, NotOne]
  split <;> simp_all

theorem fieldWF_iff (u : List Bool) (o B : Nat) : FieldWF u o B ↔
    (∀ b, b < B - 1 → NotOne u (o + b) → NotOne u (o + b + 1)) ∧ NotOne u (o + B - 1) := by
  unfold FieldWF
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨fun b hb => h1 b (by omega), h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨fun b hb => h1 b (by omega), h2⟩

theorem holds_wfCheck (u : List Bool) (ρ : Sl → Nat) :
    Holds u wfCheck ρ ↔ ∀ q, q < 22 * tableSize (ρ sL) →
      FieldWF u (2 * ρ sL + 1 + q * fieldWidth (ρ sL)) (fieldWidth (ρ sL)) := by
  simp only [wfCheck, holds_all, holds_both, holds_notOne, holds_whenNotOne]
  apply forall_congr'; intro q
  simp only [fieldWF_iff, fo, base, Bx, Dx, E, k, Ex.eval, Ex.eval_add, Ex.eval_sub,
    setSlot, tableSize, fieldWidth]
  simp

theorem holds_header (u : List Bool) (ρ : Sl → Nat) :
    Holds u header ρ ↔ (∀ i, i < ρ sL → u[i]? = some true) ∧ u[ρ sL]? = some false := by
  simp [header, E, setSlot]

/-- The environment after reading the scalars. -/
def scal (u : List Bool) (L : Nat) (ρ : Sl → Nat) : Sl → Nat :=
  setSlot (setSlot (setSlot (setSlot (setSlot ρ sm (T u L 0 0)) sM (T u L 0 1)) sK (T u L 0 2))
    sE (T u L 0 3)) sn (T u L 0 4)

theorem holds_readScalars {u : List Bool} {L : Nat} {ρ : Sl → Nat} (hL : ρ sL = L)
    (hg : GlobalWF u L) (body : C) :
    Holds u (readScalars body) ρ ↔ Holds u body (scal u L ρ) := by
  simp [readScalars, holds_rd, hg, hL, setSlot, E, k, Ex.eval, off, base, Dx, Bx, scal]

theorem envOK_scal {u : List Bool} {L : Nat} {ρ : Sl → Nat} (hL : ρ sL = L) :
    EnvOK u L (scal u L ρ) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [scal, setSlot, hL]

/-! ## The verifier on paired words -/

theorem pw_length (x w : List Bool) : (pairWords x w).length = 2 * x.length + 1 + w.length := by
  simp [pairWords]; omega

theorem pw_head (x w : List Bool) {i : Nat} (hi : i < x.length) :
    (pairWords x w)[i]? = some true := by
  unfold pairWords
  rw [List.getElem?_append_left (by simp; omega)]
  simp [hi]

theorem pw_sep (x w : List Bool) : (pairWords x w)[x.length]? = some false := by
  unfold pairWords
  rw [List.getElem?_append_right (by simp)]
  simp

theorem pw_x (x w : List Bool) {p : Nat} (hp : p < x.length) :
    (pairWords x w)[x.length + 1 + p]? = x[p]? := by
  unfold pairWords
  rw [List.getElem?_append_right (by simp; omega)]
  simp only [List.length_replicate, show x.length + 1 + p - x.length = p + 1 by omega,
    List.getElem?_cons_succ]
  rw [List.getElem?_append_left hp]

theorem pw_w (x w : List Bool) (p : Nat) : (pairWords x w)[2 * x.length + 1 + p]? = w[p]? := by
  unfold pairWords
  rw [List.getElem?_append_right (by simp; omega)]
  simp only [List.length_replicate,
    show 2 * x.length + 1 + p - x.length = (x.length + p) + 1 by omega, List.getElem?_cons_succ]
  rw [List.getElem?_append_right (by omega), show x.length + p - x.length = p by omega]

theorem header_pw (x w : List Bool) (L : Nat) :
    ((∀ i, i < L → (pairWords x w)[i]? = some true) ∧ (pairWords x w)[L]? = some false) ↔
      L = x.length := by
  constructor
  · rintro ⟨h1, h2⟩
    rcases Nat.lt_trichotomy L x.length with h | h | h
    · rw [pw_head x w h] at h2; cases h2
    · exact h
    · have := h1 x.length h; rw [pw_sep] at this; cases this
  · rintro rfl; exact ⟨fun i hi => pw_head x w hi, pw_sep x w⟩

theorem xbits_pw (x w : List Bool) : xbits (pairWords x w) x.length = fun p => x[p]? := by
  funext p
  unfold xbits
  split
  · next hp => rw [pw_x x w hp]
  · next hp => rw [List.getElem?_eq_none (by omega)]

/-- The length of a certificate. -/
def certLen (L : Nat) : Nat := 22 * tableSize L * fieldWidth L

/-- The length of the paired word. -/
def totalLen (L : Nat) : Nat := 2 * L + 1 + certLen L

theorem globalWF_of (u : List Bool) (L : Nat) (hlen : u.length = totalLen L)
    (hw : ∀ q, q < 22 * tableSize L → FieldWF u (2 * L + 1 + q * fieldWidth L) (fieldWidth L)) :
    GlobalWF u L := by
  intro q
  rcases Nat.lt_or_ge q (22 * tableSize L) with hq | hq
  · exact hw q hq
  · apply fieldWF_of_ge _ (by simp [fieldWidth])
    rw [hlen]; unfold totalLen certLen
    have := Nat.mul_le_mul_right (fieldWidth L) hq
    omega

/-- **The verifier for a fixed guess** on a paired word of matching length. -/
theorem holds_verifier (cyc : Bool) (x w : List Bool) (L : Nat) (ρ : Sl → Nat) (hL : ρ sL = L)
    (hlen : (pairWords x w).length = totalLen L) :
    Holds (pairWords x w) (verifier cyc) ρ ↔ L = x.length ∧
      (∀ q, q < 22 * tableSize L →
        FieldWF (pairWords x w) (2 * L + 1 + q * fieldWidth L) (fieldWidth L)) ∧
      VSpec cyc x.length (fun p => x[p]?) (decodeCert (pairWords x w) x.length) := by
  simp only [verifier, holds_both, holds_header, holds_wfCheck, hL, header_pw]
  constructor
  · rintro ⟨rfl, hw, hb⟩
    have hg := globalWF_of _ _ hlen hw
    rw [holds_readScalars hL hg, s_checks hg (envOK_scal hL), xbits_pw] at hb
    exact ⟨rfl, hw, hb⟩
  · rintro ⟨rfl, hw, hb⟩
    have hg := globalWF_of _ _ hlen hw
    refine ⟨rfl, hw, ?_⟩
    rw [holds_readScalars hL hg, s_checks hg (envOK_scal hL), xbits_pw]
    exact hb

/-! ## The verifier as an emitter -/

/-- `totalLen` of the innermost variable. -/
def lenExpr : NumExpr 2 :=
  .add (.add (.mul (.const 2) (.var 0)) (.const 1))
    (.mul (.mul (.const 22) (.add (.mul (.const 4) (.var 0)) (.const 4)))
      (.add (.mul (.const 8) (.var 0)) (.const 8)))

theorem eval_lenExpr (env : Env 2) : lenExpr.eval env = totalLen (env 0) := by
  simp [lenExpr, NumExpr.eval, totalLen, certLen, tableSize, fieldWidth]

/-- Slot `sL` is the guessed length; the others start as the word length. -/
def σv : Sl → Fin 2 := fun t => if t = sL then 0 else 1

/-- The verifier: for the guessed length matching the word length, emit one empty clause and
run the checks. -/
def program (cyc : Bool) : ClauseProgram 1 :=
  .forDown (.var 0) (.ifLe lenExpr (.var 1)
    (.ifLe (.var 1) lenExpr (.seq (.clause []) ((verifier cyc).compile σv)) .skip) .skip)

theorem totalLen_lt {a b : Nat} (h : a < b) : totalLen a < totalLen b := by
  unfold totalLen certLen tableSize fieldWidth
  have h1 : 22 * (4 * a + 4) ≤ 22 * (4 * b + 4) := by omega
  have h2 : 8 * a + 8 ≤ 8 * b + 8 := by omega
  have := Nat.mul_le_mul h1 h2
  omega

theorem totalLen_inj {a b : Nat} (h : totalLen a = totalLen b) : a = b := by
  rcases Nat.lt_trichotomy a b with hab | hab | hab
  · have := totalLen_lt hab; omega
  · exact hab
  · have := totalLen_lt hab; omega

theorem lt_totalLen (a : Nat) : a < totalLen a := by unfold totalLen; omega

theorem flatMap_single {α β : Type} (g : α → List β) (a0 : α) :
    ∀ l : List α, a0 ∈ l → l.Nodup → (∀ a ∈ l, a ≠ a0 → g a = []) → l.flatMap g = g a0 := by
  intro l
  induction l with
  | nil => intro h; simp at h
  | cons a l ih =>
    intro hmem hnd hz
    rw [List.flatMap_cons]
    rcases List.nodup_cons.mp hnd with ⟨hna, hnd'⟩
    by_cases ha : a = a0
    · subst ha
      have : l.flatMap g = [] := by
        rw [flatMap_eq_nil_iff]
        intro b hb
        exact hz b (List.mem_cons_of_mem _ hb) (fun h => hna (h ▸ hb))
      rw [this, List.append_nil]
    · have hm : a0 ∈ l := by
        rcases List.mem_cons.mp hmem with h | h
        · exact absurd h.symm ha
        · exact h
      rw [hz a (by simp) ha, List.nil_append]
      exact ih hm hnd' (fun b hb hne => hz b (List.mem_cons_of_mem _ hb) hne)

/-- **The emitter**: it emits `[[]]` exactly when some guessed length matches the word length
and the verifier holds for it. -/
theorem program_emit (cyc : Bool) (u : List Bool) :
    (program cyc).emit u (fun _ => u.length) = [[]] ↔
      ∃ L, totalLen L = u.length ∧
        Holds u (verifier cyc) (fun t => if t = sL then L else u.length) := by
  let E := fun L => ((verifier cyc).compile σv).emit u (extend L (fun _ => u.length))
  let G := fun L => if totalLen L = u.length then [] :: E L else []
  have hstep : ∀ L, (ClauseProgram.ifLe lenExpr (.var 1)
      (.ifLe (.var 1) lenExpr (.seq (.clause []) ((verifier cyc).compile σv)) .skip)
      .skip).emit u (extend L (fun _ => u.length)) = G L := by
    intro L
    have h1 : (NumExpr.var 1 : NumExpr 2).eval (extend L (fun _ => u.length)) = u.length := rfl
    simp only [ClauseProgram.emit, eval_lenExpr, h1, extend_zero, G]
    by_cases hL : totalLen L = u.length
    · simp [hL, E]
    · by_cases h2 : totalLen L ≤ u.length
      · simp [hL, h2, show ¬ u.length ≤ totalLen L by omega]
      · simp [hL, h2]
  have hE : ∀ L, E L = [] ↔ Holds u (verifier cyc) (fun t => if t = sL then L else u.length) := by
    intro L
    apply compile_holds
    intro t
    by_cases ht : t = sL
    · subst ht; rfl
    · simp only [σv, ht, ite_false]; rfl
  simp only [program, ClauseProgram.emit_forDown, hstep]
  have hb : (NumExpr.var 0 : NumExpr 1).eval (fun _ => u.length) = u.length := rfl
  rw [hb]
  by_cases hex : ∃ L, totalLen L = u.length
  · obtain ⟨L0, hL0⟩ := hex
    have hlt : L0 < u.length := hL0 ▸ lt_totalLen L0
    rw [flatMap_single G L0 _ (by simp [hlt])
      (List.pairwise_reverse.mpr (List.nodup_range.imp fun h => Ne.symm h))
      (by
        intro a _ hne
        simp only [G]
        have : totalLen a ≠ u.length := fun h => hne (totalLen_inj (h.trans hL0.symm))
        simp [this])]
    simp only [G, hL0, ite_true, List.cons.injEq, true_and]
    constructor
    · intro h; exact ⟨L0, hL0, (hE L0).mp h⟩
    · rintro ⟨L, hL, hh⟩
      have := totalLen_inj (hL.trans hL0.symm)
      subst this
      exact (hE L).mpr hh
  · have hz : (List.range u.length).reverse.flatMap G = [] := by
      rw [flatMap_eq_nil_iff]
      intro a _
      have : totalLen a ≠ u.length := fun h => hex ⟨a, h⟩
      simp [G, this]
    rw [hz]
    constructor
    · intro h; cases h
    · rintro ⟨L, hL, _⟩; exact absurd ⟨L, hL⟩ hex

/-- **Acceptance** on a paired word. -/
theorem accepts_iff (cyc : Bool) (x w : List Bool) :
    (program cyc).emit (pairWords x w) (fun _ => (pairWords x w).length) = [[]] ↔
      w.length = certLen x.length ∧
      (∀ q, q < 22 * tableSize x.length →
        FieldWF (pairWords x w) (2 * x.length + 1 + q * fieldWidth x.length)
          (fieldWidth x.length)) ∧
      VSpec cyc x.length (fun p => x[p]?) (decodeCert (pairWords x w) x.length) := by
  rw [program_emit]
  constructor
  · rintro ⟨L, hL, hh⟩
    rw [holds_verifier cyc x w L _ (by simp) hL.symm] at hh
    obtain ⟨rfl, hw, hv⟩ := hh
    refine ⟨?_, hw, hv⟩
    rw [pw_length] at hL; unfold totalLen at hL; omega
  · rintro ⟨hlen, hw, hv⟩
    have hL : totalLen x.length = (pairWords x w).length := by
      rw [pw_length, hlen]; rfl
    refine ⟨x.length, hL, ?_⟩
    rw [holds_verifier cyc x w x.length _ (by simp) hL.symm]
    exact ⟨rfl, hw, hv⟩

/-! ## Encoding a certificate -/

/-- The fields of `c`, table after table, each entry `v` written `1^v 0^(B - v)`. -/
def encodeCert (L : Nat) (c : VCert) : List Bool :=
  (List.range (certLen L)).map fun p =>
    decide (p % fieldWidth L <
      c.tab (p / fieldWidth L / tableSize L) (p / fieldWidth L % tableSize L))

theorem encodeCert_length (L : Nat) (c : VCert) : (encodeCert L c).length = certLen L := by
  simp [encodeCert]

theorem divmod_aux {q B j : Nat} (hj : j < B) : (q * B + j) / B = q ∧ (q * B + j) % B = j := by
  have hB : 0 < B := by omega
  constructor
  · rw [Nat.add_comm, Nat.add_mul_div_right j q hB, Nat.div_eq_of_lt hj, Nat.zero_add]
  · rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj]

theorem encodeCert_getElem (L : Nat) (c : VCert) {q j : Nat} (hq : q < 22 * tableSize L)
    (hj : j < fieldWidth L) :
    (encodeCert L c)[q * fieldWidth L + j]? =
      some (decide (j < c.tab (q / tableSize L) (q % tableSize L))) := by
  have hlt : q * fieldWidth L + j < certLen L := by
    unfold certLen
    have := Nat.mul_le_mul_right (fieldWidth L) (show q + 1 ≤ 22 * tableSize L by omega)
    rw [Nat.add_mul, Nat.one_mul] at this
    omega
  obtain ⟨h1, h2⟩ := divmod_aux (q := q) hj
  simp [encodeCert, hlt, h1, h2]

/-- A thermometer field with value `v < B` reads `v` and is well formed. -/
theorem field_of_bits {u : List Bool} {o B v : Nat} (hv : v < B)
    (hb : ∀ j, j < B → u[o + j]? = some (decide (j < v))) : tval u o B = v ∧ FieldWF u o B := by
  constructor
  · apply leadOnes_eq u o B v (by omega)
    · intro i hi; rw [hb i (by omega)]; simp [hi]
    · intro _; unfold NotOne; rw [hb v hv]; simp
  · constructor
    · intro b hb1 hno
      unfold NotOne at hno ⊢
      rw [hb b (by omega)] at hno
      rw [show o + b + 1 = o + (b + 1) by omega, hb (b + 1) hb1]
      simp at hno ⊢; omega
    · unfold NotOne
      rw [show o + B - 1 = o + (B - 1) by omega, hb (B - 1) (by omega)]
      simp; omega

theorem pw_field (x : List Bool) (c : VCert) (hb : VCert.Bounded x.length c) {q : Nat}
    (hq : q < 22 * tableSize x.length) :
    tval (pairWords x (encodeCert x.length c)) (2 * x.length + 1 + q * fieldWidth x.length)
        (fieldWidth x.length) = c.tab (q / tableSize x.length) (q % tableSize x.length) ∧
      FieldWF (pairWords x (encodeCert x.length c)) (2 * x.length + 1 + q * fieldWidth x.length)
        (fieldWidth x.length) := by
  have hD : 0 < tableSize x.length := by simp [tableSize]
  apply field_of_bits
  · apply hb
    · show q / tableSize x.length < 22
      exact (Nat.div_lt_iff_lt_mul hD).mpr hq
    · exact Nat.mod_lt _ hD
  · intro j hj
    rw [show 2 * x.length + 1 + q * fieldWidth x.length + j =
      2 * x.length + 1 + (q * fieldWidth x.length + j) by omega, pw_w,
      encodeCert_getElem _ _ hq hj]

theorem decodeCert_tab (u : List Bool) (L τ i : Nat) (h1 : 1 ≤ τ) (h2 : τ < 22) :
    (decodeCert u L).tab τ i = T u L τ i := by
  match τ, h1, h2 with
  | 0, h, _ => exact absurd h (by decide)
  | 1, _, _ => rfl
  | 2, _, _ => rfl
  | 3, _, _ => rfl
  | 4, _, _ => rfl
  | 5, _, _ => rfl
  | 6, _, _ => rfl
  | 7, _, _ => rfl
  | 8, _, _ => rfl
  | 9, _, _ => rfl
  | 10, _, _ => rfl
  | 11, _, _ => rfl
  | 12, _, _ => rfl
  | 13, _, _ => rfl
  | 14, _, _ => rfl
  | 15, _, _ => rfl
  | 16, _, _ => rfl
  | 17, _, _ => rfl
  | 18, _, _ => rfl
  | 19, _, _ => rfl
  | 20, _, _ => rfl
  | 21, _, _ => rfl
  | n + 22, _, h => exact absurd h (by omega)

/-- The decoded certificate agrees with the encoded one on all inspected entries. -/
theorem decode_encode (x : List Bool) (c : VCert) (hb : VCert.Bounded x.length c) {τ i : Nat}
    (hτ : τ < 22) (hi : i < tableSize x.length) :
    (decodeCert (pairWords x (encodeCert x.length c)) x.length).tab τ i = c.tab τ i := by
  have hT : ∀ τ', τ' < 22 → ∀ i', i' < tableSize x.length →
      T (pairWords x (encodeCert x.length c)) x.length τ' i' = c.tab τ' i' := by
    intro τ' hτ' i' hi'
    have hq : τ' * tableSize x.length + i' < 22 * tableSize x.length := by
      have := Nat.mul_le_mul_right (tableSize x.length) (show τ' + 1 ≤ 22 by omega)
      rw [Nat.add_mul, Nat.one_mul] at this
      omega
    obtain ⟨d1, d2⟩ := divmod_aux (q := τ') hi'
    have := (pw_field x c hb hq).1
    rw [d1, d2] at this
    exact this
  rcases Nat.eq_zero_or_pos τ with rfl | hpos
  · have e : ∀ j, (decodeCert (pairWords x (encodeCert x.length c)) x.length).tab 0 j =
        if j = 0 then T (pairWords x (encodeCert x.length c)) x.length 0 0
        else if j = 1 then T (pairWords x (encodeCert x.length c)) x.length 0 1
        else if j = 2 then T (pairWords x (encodeCert x.length c)) x.length 0 2
        else if j = 3 then T (pairWords x (encodeCert x.length c)) x.length 0 3
        else if j = 4 then T (pairWords x (encodeCert x.length c)) x.length 0 4 else 0 :=
      fun _ => rfl
    rw [e]
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ 5 ≤ i by omega) with
      rfl | rfl | rfl | rfl | rfl | h5
    · simpa using hT 0 hτ 0 hi
    · simpa using hT 0 hτ 1 hi
    · simpa using hT 0 hτ 2 hi
    · simpa using hT 0 hτ 3 hi
    · simpa using hT 0 hτ 4 hi
    · simp [VCert.tab, show i ≠ 0 by omega, show i ≠ 1 by omega, show i ≠ 2 by omega,
        show i ≠ 3 by omega, show i ≠ 4 by omega]
  · rw [decodeCert_tab _ _ _ _ hpos hτ]
    exact hT τ hτ i hi

/-! ## Soundness and completeness of the verifier -/

theorem verifier_sound (cyc : Bool) (x w : List Bool)
    (h : (program cyc).emit (pairWords x w) (fun _ => (pairWords x w).length) = [[]]) :
    ∃ f, encode f = x ∧ IsThreeCNF f ∧ Satisfiable f ∧ PlanarGraph (targetGraph cyc f) :=
  VSpec.sound ((accepts_iff cyc x w).mp h).2.2

theorem verifier_complete (cyc : Bool) {f : CNF} (h3 : IsThreeCNF f) (hs : Satisfiable f)
    (hp : PlanarGraph (targetGraph cyc f)) :
    ∃ w, w.length = certLen (encode f).length ∧
      (program cyc).emit (pairWords (encode f) w)
        (fun _ => (pairWords (encode f) w).length) = [[]] := by
  obtain ⟨c, hv, hb⟩ := vspec_complete h3 hs hp
  generalize encode f = x at hv hb ⊢
  refine ⟨encodeCert x.length c, encodeCert_length _ _, ?_⟩
  rw [accepts_iff]
  refine ⟨encodeCert_length _ _, fun q hq => (pw_field x c hb hq).2, ?_⟩
  apply hv.transfer (fun p hp => List.getElem?_eq_none hp)
  intro τ hτ i hi
  exact decode_encode x c hb hτ hi

theorem certLen_le (L : Nat) : certLen L ≤ powerBound 704 2 L := by
  rw [powerBound_eq, Nat.pow_two]
  unfold certLen tableSize fieldWidth
  rw [show 4 * L + 4 = 4 * (L + 1) by omega, show 8 * L + 8 = 8 * (L + 1) by omega]
  apply Nat.le_of_eq
  generalize L + 1 = a
  rw [show (704 : Nat) = 22 * 4 * 8 from rfl]
  ac_rfl

/-- **Membership in NP** of the language of codes of satisfiable 3-CNFs whose target graph is
planar. -/
theorem inNP_target (cyc : Bool) :
    InNP (fun x => ∃ f, encode f = x ∧ IsThreeCNF f ∧ Satisfiable f ∧
      PlanarGraph (targetGraph cyc f)) := by
  apply inNP_of_emitter (program cyc) 704 2
  intro x
  constructor
  · rintro ⟨f, rfl, h3, hs, hp⟩
    obtain ⟨w, hw, he⟩ := verifier_complete cyc h3 hs hp
    exact ⟨w, hw ▸ certLen_le _, he⟩
  · rintro ⟨w, _, he⟩
    exact verifier_sound cyc x w he

end Complexity.Planar.Vf
