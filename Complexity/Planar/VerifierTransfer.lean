module

public import Complexity.Planar.VerifierSpec
import Lean.Elab.Tactic.Omega

/-!
# Certificates agreeing on small indices

The local checks `VSpec` for a word of length `L` only inspect table entries with index below
`tableSize L`: every index they use is bounded by `L` or by `2 · n2 ≤ 4 L` (using the bounds
that the checks themselves impose).  Hence a certificate agreeing with a valid one on these
entries is valid as well (`VSpec.transfer`).
-/

@[expose] public section

namespace Complexity.Planar

theorem VSpec.transfer {cyc : Bool} {L : Nat} {xb : Nat → Option Bool} {c c' : VCert}
    (h : VSpec cyc L xb c) (hxb : ∀ p, L ≤ p → xb p = none)
    (hag : ∀ τ, τ < numTables → ∀ i, i < tableSize L → c'.tab τ i = c.tab τ i) :
    VSpec cyc L xb c' := by
  have ag : ∀ τ, τ < 22 → ∀ i, i < 4 * L + 4 → c'.tab τ i = c.tab τ i :=
    fun τ hτ i hi => hag τ hτ i hi
  have hL1 : 1 ≤ L := by
    rcases Nat.eq_zero_or_pos L with h0 | h0
    · have h1 := h.parse.headEnd
      have h2 := h.parse.m_le
      rw [hxb _ (by omega)] at h1; cases h1
    · exact h0
  have e0 : ∀ i, i < 5 → c'.tab 0 i = c.tab 0 i := fun i hi => ag 0 (by decide) i (by omega)
  have hm : c'.pt.m = c.pt.m := by simpa [VCert.tab] using e0 0 (by decide)
  have hM : c'.pt.M = c.pt.M := by simpa [VCert.tab] using e0 1 (by decide)
  have hK : c'.K = c.K := by simpa [VCert.tab] using e0 2 (by decide)
  have hE : c'.estar = c.estar := by simpa [VCert.tab] using e0 3 (by decide)
  have hn : c'.et.n2 = c.et.n2 := by simpa [VCert.tab] using e0 4 (by decide)
  have hkk : ∀ i, i < 4 * L + 4 → c'.pt.kk i = c.pt.kk i := fun i hi => ag 1 (by decide) i hi
  have hO : ∀ i, i < 4 * L + 4 → c'.pt.O i = c.pt.O i := fun i hi => ag 2 (by decide) i hi
  have hP : ∀ i, i < 4 * L + 4 → c'.pt.P i = c.pt.P i := fun i hi => ag 3 (by decide) i hi
  have hts : ∀ i, i < 4 * L + 4 → c'.tsel i = c.tsel i := fun i hi => ag 4 (by decide) i hi
  have hJ : ∀ i, i < 4 * L + 4 → c'.pt.J i = c.pt.J i := fun i hi => ag 5 (by decide) i hi
  have hT : ∀ i, i < 4 * L + 4 → c'.pt.T i = c.pt.T i := fun i hi => ag 6 (by decide) i hi
  have hV : ∀ i, i < 4 * L + 4 → c'.pt.V i = c.pt.V i := fun i hi => ag 7 (by decide) i hi
  have hS : ∀ i, i < 4 * L + 4 → c'.pt.S i = c.pt.S i := fun i hi => ag 8 (by decide) i hi
  have hQ : ∀ i, i < 4 * L + 4 → c'.pt.Q i = c.pt.Q i := fun i hi => ag 9 (by decide) i hi
  have hA : ∀ i, i < 4 * L + 4 → c'.A i = c.A i := fun i hi => ag 10 (by decide) i hi
  have hEN : ∀ i, i < 4 * L + 4 → c'.et.EN i = c.et.EN i := fun i hi => ag 11 (by decide) i hi
  have hN : ∀ i, i < 4 * L + 4 → c'.et.N i = c.et.N i := fun i hi => ag 12 (by decide) i hi
  have hF : ∀ i, i < 4 * L + 4 → c'.et.F i = c.et.F i := fun i hi => ag 13 (by decide) i hi
  have hR : ∀ i, i < 4 * L + 4 → c'.et.R i = c.et.R i := fun i hi => ag 14 (by decide) i hi
  have hFL : ∀ i, i < 4 * L + 4 → c'.et.FL i = c.et.FL i := fun i hi => ag 15 (by decide) i hi
  have hCL : ∀ i, i < 4 * L + 4 → c'.et.CL i = c.et.CL i := fun i hi => ag 16 (by decide) i hi
  have hDD : ∀ i, i < 4 * L + 4 → c'.et.D i = c.et.D i := fun i hi => ag 17 (by decide) i hi
  have hSU : ∀ i, i < 4 * L + 4 → c'.et.SU i = c.et.SU i := fun i hi => ag 18 (by decide) i hi
  have hcR : ∀ i, i < 4 * L + 4 → c'.et.cR i = c.et.cR i := fun i hi => ag 19 (by decide) i hi
  have hcF : ∀ i, i < 4 * L + 4 → c'.et.cF i = c.et.cF i := fun i hi => ag 20 (by decide) i hi
  have hcC : ∀ i, i < 4 * L + 4 → c'.et.cC i = c.et.cC i := fun i hi => ag 21 (by decide) i hi
  -- bounds implied by the checks on `c`
  have hp := h.parse
  have he := h.embed
  have hmL := hp.m_le
  have hML := hp.M_le
  have hOle : ∀ j, j ≤ c.pt.m → c.pt.O j ≤ c.pt.M := fun j hj => by
    have := hp.O_mono hj (Nat.le_refl _); rw [hp.O_last] at this; exact this
  have hVL : ∀ e, e < c.pt.M → c.pt.V e < L := by
    intro e he'
    have := hp.varEnd e he'
    rcases Nat.lt_or_ge (c.pt.Q e + 1 + c.pt.V e) L with h1 | h1
    · omega
    · rw [hxb _ h1] at this; cases this
  have hKL : c.K ≤ L := by
    rcases Nat.eq_zero_or_pos c.pt.M with h0 | h0
    · rw [h.varZero h0]; omega
    · obtain ⟨h1, h2⟩ := h.varMax h0; have := hVL _ h1; omega
  have hnL : c.et.n2 ≤ 2 * L := by rw [h.n2]; split <;> omega
  refine
    { parse := { m_le := ?_, M_le := ?_, head := ?_, headEnd := ?_, O_zero := ?_, O_succ := ?_,
                 O_last := ?_, P_zero := ?_, len := ?_, lenEnd := ?_, empty := ?_, first := ?_,
                 occ := ?_, sign := ?_, var := ?_, varEnd := ?_, next := ?_, last := ?_,
                 P_last := ?_ }
      three := ?_, sat := ?_, varLt := ?_, varZero := ?_, varMax := ?_, n2 := ?_,
      endOcc := ?_, endCyc := ?_,
      embed := { bound := ?_, edgeK := ?_, nodeEnd := ?_, rank_next := ?_, rank_lt := ?_,
                 rank_prev := ?_, rank_unique := ?_, face := ?_, comp := ?_, succ := ?_,
                 cntR := ?_, cntF := ?_, cntC := ?_, final := ?_ } }
  · rw [hm]; exact hp.m_le
  · rw [hM]; exact hp.M_le
  · rw [hm]; exact hp.head
  · rw [hm]; exact hp.headEnd
  · rw [hO 0 (by omega)]; exact hp.O_zero
  · intro j hj; rw [hm] at hj
    rw [hO (j + 1) (by omega), hO j (by omega), hkk j (by omega)]; exact hp.O_succ j hj
  · rw [hm, hO c.pt.m (by omega), hM]; exact hp.O_last
  · rw [hP 0 (by omega), hm]; exact hp.P_zero
  · intro j hj i hi; rw [hm] at hj; rw [hkk j (by omega)] at hi
    rw [hP j (by omega)]; exact hp.len j hj i hi
  · intro j hj; rw [hm] at hj
    rw [hP j (by omega), hkk j (by omega)]; exact hp.lenEnd j hj
  · intro j hj hk; rw [hm] at hj; rw [hkk j (by omega)] at hk
    rw [hP (j + 1) (by omega), hP j (by omega)]; exact hp.empty j hj hk
  · intro j hj hk; rw [hm] at hj; rw [hkk j (by omega)] at hk
    have := hOle j (by omega)
    rw [hO j (by omega), hQ (c.pt.O j) (by omega), hP j (by omega), hkk j (by omega)]
    exact hp.first j hj hk
  · intro e he'; rw [hM] at he'
    obtain ⟨h1, h2, h3⟩ := hp.occ e he'
    rw [hJ e (by omega), hm, hT e (by omega), hkk (c.pt.J e) (by omega),
      hO (c.pt.J e) (by omega)]
    exact ⟨h1, h2, h3⟩
  · intro e he'; rw [hM] at he'
    rw [hS e (by omega), hQ e (by omega)]; exact hp.sign e he'
  · intro e he' i hi; rw [hM] at he'; rw [hV e (by omega)] at hi
    rw [hQ e (by omega)]; exact hp.var e he' i hi
  · intro e he'; rw [hM] at he'
    rw [hQ e (by omega), hV e (by omega)]; exact hp.varEnd e he'
  · intro e he' ht; rw [hM] at he'
    have := (hp.occ e he').1
    rw [hT e (by omega), hJ e (by omega), hkk (c.pt.J e) (by omega)] at ht
    rw [hQ (e + 1) (by omega), hQ e (by omega), hV e (by omega)]; exact hp.next e he' ht
  · intro e he' ht; rw [hM] at he'
    have := (hp.occ e he').1
    rw [hT e (by omega), hJ e (by omega), hkk (c.pt.J e) (by omega)] at ht
    rw [hJ e (by omega), hP (c.pt.J e + 1) (by omega), hQ e (by omega), hV e (by omega)]
    exact hp.last e he' ht
  · rw [hm, hP c.pt.m (by omega)]; exact hp.P_last
  · intro j hj; rw [hm] at hj; rw [hkk j (by omega)]; exact h.three j hj
  · intro j hj; rw [hm] at hj
    obtain ⟨h1, h2⟩ := h.sat j hj
    have hlt := (hp.occ_of hj h1).1
    have hvl := hVL _ hlt
    rw [hts j (by omega), hkk j (by omega), hO j (by omega),
      hV (c.pt.O j + c.tsel j) (by omega), hA (c.pt.V (c.pt.O j + c.tsel j)) (by omega),
      hS (c.pt.O j + c.tsel j) (by omega)]
    exact ⟨h1, h2⟩
  · intro e he'; rw [hM] at he'; rw [hV e (by omega), hK]; exact h.varLt e he'
  · rw [hM, hK]; exact h.varZero
  · rw [hM, hE, hK]; intro h0
    obtain ⟨h1, h2⟩ := h.varMax h0
    rw [hV c.estar (by omega)]; exact ⟨h1, h2⟩
  · rw [hn, hM, hK]; exact h.n2
  · intro e he'; rw [hM] at he'
    rw [hEN (2 * e) (by omega), hEN (2 * e + 1) (by omega), hV e (by omega), hJ e (by omega)]
    exact h.endOcc e he'
  · intro hc i hi; rw [hK] at hi
    have hn2 := h.n2
    rw [hc] at hn2
    simp only [ite_true] at hn2
    rw [hM, hK, hEN (2 * (c.pt.M + i)) (by omega), hEN (2 * (c.pt.M + i) + 1) (by omega)]
    exact h.endCyc hc i hi
  · intro d hd; rw [hn] at hd
    rw [hN d (by omega), hF d (by omega), hn]; exact he.bound d hd
  · intro j hj; rw [hn] at hj
    have b1 := he.bound (2 * j + 1) (by omega)
    have b2 := he.bound (2 * j) (by omega)
    rw [hF (2 * j + 1) (by omega), hN (c.et.F (2 * j + 1)) (by omega), hF (2 * j) (by omega),
      hN (c.et.F (2 * j)) (by omega)]
    exact he.edgeK j hj
  · intro d hd; rw [hn] at hd
    have := (he.bound d hd).1
    rw [hN d (by omega), hEN (c.et.N d) (by omega), hEN d (by omega)]; exact he.nodeEnd d hd
  · intro d hd; rw [hn] at hd
    have := (he.bound d hd).1
    rw [hN d (by omega), hR (c.et.N d) (by omega), hR d (by omega)]; exact he.rank_next d hd
  · intro d hd; rw [hn] at hd
    rw [hR d (by omega), hn]; exact he.rank_lt d hd
  · intro j hj; rw [hn] at hj
    have b1 := (he.bound (2 * j + 1) (by omega)).2
    have b2 := (he.bound (2 * j) (by omega)).2
    rw [hR (2 * j) (by omega), hR (2 * j + 1) (by omega), hF (2 * j + 1) (by omega),
      hF (2 * j) (by omega), hR (c.et.F (2 * j + 1)) (by omega), hR (c.et.F (2 * j)) (by omega)]
    exact he.rank_prev j hj
  · intro d hd d' hd' heq hr hr'; rw [hn] at hd hd'
    rw [hEN d (by omega), hEN d' (by omega)] at heq
    rw [hR d (by omega)] at hr
    rw [hR d' (by omega)] at hr'
    exact he.rank_unique d hd d' hd' heq hr hr'
  · intro d hd; rw [hn] at hd
    have := (he.bound d hd).2
    rw [hFL d (by omega), hF d (by omega), hFL (c.et.F d) (by omega)]; exact he.face d hd
  · intro d hd; rw [hn] at hd
    rw [hCL d (by omega), hDD d (by omega)]; exact he.comp d hd
  · intro d hd hD0; rw [hn] at hd
    rw [hDD d (by omega)] at hD0
    obtain ⟨h1, h2, h3, h4⟩ := he.succ d hd hD0
    rw [hSU d (by omega), hn, hDD (c.et.SU d) (by omega), hDD d (by omega),
      hCL (c.et.SU d) (by omega), hCL d (by omega), hN d (by omega), hF d (by omega)]
    exact ⟨h1, h2, h3, h4⟩
  · refine ⟨by rw [hcR 0 (by omega)]; exact he.cntR.1, ?_⟩
    intro d hd; rw [hn] at hd
    rw [hcR (d + 1) (by omega), hcR d (by omega), hR d (by omega)]; exact he.cntR.2 d hd
  · refine ⟨by rw [hcF 0 (by omega)]; exact he.cntF.1, ?_⟩
    intro d hd; rw [hn] at hd
    rw [hcF (d + 1) (by omega), hcF d (by omega), hFL d (by omega)]; exact he.cntF.2 d hd
  · refine ⟨by rw [hcC 0 (by omega)]; exact he.cntC.1, ?_⟩
    intro d hd; rw [hn] at hd
    rw [hcC (d + 1) (by omega), hcC d (by omega), hCL d (by omega)]; exact he.cntC.2 d hd
  · rw [hn, hcC (2 * c.et.n2) (by omega), hcR (2 * c.et.n2) (by omega),
      hcF (2 * c.et.n2) (by omega)]
    exact he.final

end Complexity.Planar
