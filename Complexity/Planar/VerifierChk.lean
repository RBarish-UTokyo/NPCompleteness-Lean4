module

public import Complexity.Planar.Fields
public import Complexity.Planar.VerifierSpec
import Lean.Elab.Tactic.Omega

/-!
# The planar 3-SAT verifier as a check program

The verifier reads the word `u = pairWords x w`.  For a guessed length `L = |x|`, the
certificate `w` starts at `2 L + 1` and consists of `numTables` tables of `tableSize L` fields
of width `fieldWidth L`.  This file writes every condition of `VSpec` as a `Chk` program over
24 named slots and proves that the program holds exactly when the certificate decoded from
the fields satisfies `VSpec`.
-/

@[expose] public section

-- Section hypotheses stay in the signatures of lemmas that do not use them, so that all
-- lemmas of a section take the same arguments.
set_option linter.unusedSectionVars false

namespace Complexity.Planar.Vf

open Chk

/-- Slots. -/
abbrev Sl := Fin 24
@[simp] abbrev sN : Sl := 0
@[simp] abbrev sL : Sl := 1
@[simp] abbrev sm : Sl := 2
@[simp] abbrev sM : Sl := 3
@[simp] abbrev sK : Sl := 4
@[simp] abbrev sE : Sl := 5
@[simp] abbrev sn : Sl := 6
@[simp] abbrev ta : Sl := 7
@[simp] abbrev tb : Sl := 8
@[simp] abbrev tc : Sl := 9
@[simp] abbrev td : Sl := 10
@[simp] abbrev te : Sl := 11
@[simp] abbrev tg : Sl := 12
@[simp] abbrev th : Sl := 13
@[simp] abbrev ti : Sl := 14
@[simp] abbrev tj : Sl := 15
@[simp] abbrev tk : Sl := 16
@[simp] abbrev tp : Sl := 17
@[simp] abbrev tq : Sl := 18
@[simp] abbrev tr : Sl := 19
@[simp] abbrev ts : Sl := 20
@[simp] abbrev tt : Sl := 21
@[simp] abbrev tv : Sl := 22
@[simp] abbrev tw : Sl := 23

abbrev X := Ex 24
abbrev C := Chk 24

def E (s : Sl) : X := .slot s
def k (c : Nat) : X := .const c

/-- Entries per table, field width and certificate start, as expressions in `L`. -/
def Dx : X := .add (.mul (k 4) (E sL)) (k 4)
def Bx : X := .add (.mul (k 8) (E sL)) (k 8)
def base : X := .add (.mul (k 2) (E sL)) (k 1)

/-- The offset of entry `idx` of table `τ`. -/
def off (τ : Nat) (idx : X) : X := .add base (.mul (.add (.mul (k τ) Dx) idx) Bx)

/-- Read entry `idx` of table `τ` into slot `dst`. -/
def rd (τ : Nat) (idx : X) (dst : Sl) (body : C) : C := readField (off τ idx) Bx dst body

/-- Require the bit `p` of `x` (stored at `L + 1 + p`) to be `v`; positions `p ≥ L` are
absent. -/
def reqX (p : X) (v : Bool) : C :=
  .le (.add p (k 1)) (E sL)
    (.bit (.add (.add (E sL) (k 1)) p) .fail (if v then .fail else .ok) (if v then .ok else .fail))
    .fail

/-! ## Semantics of the building blocks -/

/-- The bits of `x` inside `u`. -/
def xbits (u : List Bool) (L p : Nat) : Option Bool := if p < L then u[L + 1 + p]? else none

/-- The stored value of entry `i` of table `τ`. -/
def T (u : List Bool) (L τ i : Nat) : Nat :=
  tval u (2 * L + 1 + (τ * tableSize L + i) * fieldWidth L) (fieldWidth L)

/-- All fields from the certificate start on are well formed. -/
def GlobalWF (u : List Bool) (L : Nat) : Prop :=
  ∀ q, FieldWF u (2 * L + 1 + q * fieldWidth L) (fieldWidth L)

theorem eval_off (τ : Nat) (idx : X) (ρ : Sl → Nat) :
    (off τ idx).eval ρ = 2 * ρ sL + 1 + (τ * tableSize (ρ sL) + idx.eval ρ) * fieldWidth (ρ sL) := by
  simp [off, base, Dx, Bx, k, E, Ex.eval, tableSize, fieldWidth]

theorem eval_Bx (ρ : Sl → Nat) : Bx.eval ρ = fieldWidth (ρ sL) := by
  simp [Bx, k, E, Ex.eval, fieldWidth]

theorem holds_rd {u : List Bool} {ρ : Sl → Nat} (hg : GlobalWF u (ρ sL))
    (τ : Nat) (idx : X) (dst : Sl) (body : C) (hf : (off τ idx).fresh dst = true) :
    Holds u (rd τ idx dst body) ρ ↔
      Holds u body (setSlot ρ dst (T u (ρ sL) τ (idx.eval ρ))) := by
  have hwf : FieldWF u ((off τ idx).eval ρ) (Bx.eval ρ) := by
    rw [eval_off, eval_Bx]
    exact hg _
  rw [rd, holds_readField u (off τ idx) Bx dst body ρ hf hwf (by rw [eval_Bx]; simp [fieldWidth]),
    eval_off, eval_Bx]
  rfl

theorem holds_reqX {u : List Bool} {ρ : Sl → Nat} (p : X) (v : Bool) :
    Holds u (reqX p v) ρ ↔ xbits u (ρ sL) (p.eval ρ) = some v := by
  simp only [reqX, Holds, Ex.eval, E, k, xbits]
  by_cases hp : p.eval ρ + 1 ≤ ρ sL
  · simp only [hp, ite_true, show p.eval ρ < ρ sL by omega]
    rcases hb : u[ρ sL + 1 + p.eval ρ]? with _ | _ | _ <;> cases v <;> simp
  · simp only [hp, ite_false, show ¬ p.eval ρ < ρ sL by omega]
    simp

@[simp] theorem Ex.fresh_hadd (a b : X) (s : Sl) : (a + b).fresh s = (a.fresh s && b.fresh s) :=
  rfl
@[simp] theorem Ex.fresh_hmul (a b : X) (s : Sl) : (a * b).fresh s = (a.fresh s && b.fresh s) :=
  rfl
@[simp] theorem Ex.fresh_hsub (a b : X) (s : Sl) : (a - b).fresh s = (a.fresh s && b.fresh s) :=
  rfl

/-! ## The decoded certificate -/

/-- The certificate stored in `u` for the guess `L`. -/
def decodeCert (u : List Bool) (L : Nat) : VCert where
  pt := { m := T u L 0 0, M := T u L 0 1, kk := T u L 1, O := T u L 2, P := T u L 3,
          J := T u L 5, T := T u L 6, V := T u L 7, S := T u L 8, Q := T u L 9 }
  K := T u L 0 2
  estar := T u L 0 3
  A := T u L 10
  tsel := T u L 4
  et := { n2 := T u L 0 4, EN := T u L 11, N := T u L 12, F := T u L 13, R := T u L 14,
          FL := T u L 15, CL := T u L 16, D := T u L 17, SU := T u L 18,
          cR := T u L 19, cF := T u L 20, cC := T u L 21 }

/-- The slot environment after the scalars have been read. -/
structure EnvOK (u : List Bool) (L : Nat) (ρ : Sl → Nat) : Prop where
  hL : ρ sL = L
  hm : ρ sm = T u L 0 0
  hM : ρ sM = T u L 0 1
  hK : ρ sK = T u L 0 2
  hE : ρ sE = T u L 0 3
  hn : ρ sn = T u L 0 4

set_option hygiene false in
/-- Unfold the semantics of a check. -/
macro "vsimp" : tactic => `(tactic| simp [holds_rd, hg, he.hL, he.hm, he.hM, he.hK, he.hE,
  he.hn, holds_reqX, setSlot, E, k, Ex.eval, off, base, Dx, Bx, decodeCert])

/-! ## Checks of the parse -/

def cMle : C := reqLe (E sm) (E sL)
def cMMle : C := reqLe (E sM) (E sL)
def cHead : C := .all ti (E sm) (reqX (E ti) true)
def cHeadEnd : C := reqX (E sm) false
def cO0 : C := rd 2 (k 0) ta (reqEq (E ta) (k 0))
def cOsucc : C :=
  .all tj (E sm) (rd 2 (E tj) ta (rd 2 (E tj + k 1) tb (rd 1 (E tj) tc
    (reqEq (E tb) (E ta + E tc)))))
def cOlast : C := rd 2 (E sm) ta (reqEq (E ta) (E sM))
def cP0 : C := rd 3 (k 0) ta (reqEq (E ta) (E sm + k 1))
def cLen : C :=
  .all tj (E sm) (rd 3 (E tj) ta (rd 1 (E tj) tc (.all ti (E tc) (reqX (E ta + E ti) true))))
def cLenEnd : C := .all tj (E sm) (rd 3 (E tj) ta (rd 1 (E tj) tc (reqX (E ta + E tc) false)))
def cEmpty : C :=
  .all tj (E sm) (rd 1 (E tj) tc (whenEq (E tc) (k 0) (rd 3 (E tj) ta (rd 3 (E tj + k 1) tb
    (reqEq (E tb) (E ta + k 1))))))
def cFirst : C :=
  .all tj (E sm) (rd 1 (E tj) tc (whenLt (k 0) (E tc) (rd 2 (E tj) ta (rd 9 (E ta) tq
    (rd 3 (E tj) tp (reqEq (E tq) (E tp + E tc + k 1)))))))
def cOcc : C :=
  .all te (E sM) (rd 5 (E te) tj (.both (reqLt (E tj) (E sm)) (rd 6 (E te) tt (rd 1 (E tj) tc
    (.both (reqLt (E tt) (E tc)) (rd 2 (E tj) ta (reqEq (E ta + E tt) (E te))))))))
def cSign : C :=
  .all te (E sM) (rd 8 (E te) ts (rd 9 (E te) tq (.both (reqLe (E ts) (k 1))
    (.both (whenEq (E ts) (k 1) (reqX (E tq) true)) (whenNe (E ts) (k 1) (reqX (E tq) false))))))
def cVar : C :=
  .all te (E sM) (rd 9 (E te) tq (rd 7 (E te) tv (.all ti (E tv)
    (reqX (E tq + k 1 + E ti) true))))
def cVarEnd : C := .all te (E sM) (rd 9 (E te) tq (rd 7 (E te) tv (reqX (E tq + k 1 + E tv) false)))
def cNext : C :=
  .all te (E sM) (rd 6 (E te) tt (rd 5 (E te) tj (rd 1 (E tj) tc (whenLt (E tt + k 1) (E tc)
    (rd 9 (E te + k 1) tp (rd 9 (E te) tq (rd 7 (E te) tv (reqEq (E tp) (E tq + E tv + k 2)))))))))
def cLast : C :=
  .all te (E sM) (rd 6 (E te) tt (rd 5 (E te) tj (rd 1 (E tj) tc (whenEq (E tt + k 1) (E tc)
    (rd 3 (E tj + k 1) tp (rd 9 (E te) tq (rd 7 (E te) tv (reqEq (E tp) (E tq + E tv + k 2)))))))))
def cPlast : C := rd 3 (E sm) ta (reqEq (E ta) (E sL))

section sem

variable {u : List Bool} {L : Nat} {ρ : Sl → Nat} (hg : GlobalWF u L) (he : EnvOK u L ρ)
include hg he

theorem s_Mle : Holds u cMle ρ ↔ (decodeCert u L).pt.m ≤ L := by simp [cMle]; vsimp
theorem s_MMle : Holds u cMMle ρ ↔ (decodeCert u L).pt.M ≤ L := by simp [cMMle]; vsimp
theorem s_head : Holds u cHead ρ ↔
    ∀ i, i < (decodeCert u L).pt.m → xbits u L i = some true := by simp [cHead]; vsimp
theorem s_headEnd : Holds u cHeadEnd ρ ↔ xbits u L (decodeCert u L).pt.m = some false := by
  simp [cHeadEnd]; vsimp
theorem s_O0 : Holds u cO0 ρ ↔ (decodeCert u L).pt.O 0 = 0 := by simp [cO0]; vsimp
theorem s_Osucc : Holds u cOsucc ρ ↔ ∀ j, j < (decodeCert u L).pt.m →
    (decodeCert u L).pt.O (j + 1) = (decodeCert u L).pt.O j + (decodeCert u L).pt.kk j := by
  simp [cOsucc]; vsimp
theorem s_Olast : Holds u cOlast ρ ↔ (decodeCert u L).pt.O (decodeCert u L).pt.m =
    (decodeCert u L).pt.M := by simp [cOlast]; vsimp
theorem s_P0 : Holds u cP0 ρ ↔ (decodeCert u L).pt.P 0 = (decodeCert u L).pt.m + 1 := by
  simp [cP0]; vsimp
theorem s_len : Holds u cLen ρ ↔ ∀ j, j < (decodeCert u L).pt.m → ∀ i, i < (decodeCert u L).pt.kk j →
    xbits u L ((decodeCert u L).pt.P j + i) = some true := by simp [cLen]; vsimp
theorem s_lenEnd : Holds u cLenEnd ρ ↔ ∀ j, j < (decodeCert u L).pt.m →
    xbits u L ((decodeCert u L).pt.P j + (decodeCert u L).pt.kk j) = some false := by
  simp [cLenEnd]; vsimp
theorem s_empty : Holds u cEmpty ρ ↔ ∀ j, j < (decodeCert u L).pt.m →
    (decodeCert u L).pt.kk j = 0 → (decodeCert u L).pt.P (j + 1) = (decodeCert u L).pt.P j + 1 := by
  simp [cEmpty]; vsimp
theorem s_first : Holds u cFirst ρ ↔ ∀ j, j < (decodeCert u L).pt.m → 0 < (decodeCert u L).pt.kk j →
    (decodeCert u L).pt.Q ((decodeCert u L).pt.O j) =
      (decodeCert u L).pt.P j + (decodeCert u L).pt.kk j + 1 := by
  simp [cFirst]; vsimp
theorem s_occ : Holds u cOcc ρ ↔ ∀ e, e < (decodeCert u L).pt.M →
    (decodeCert u L).pt.J e < (decodeCert u L).pt.m ∧
    (decodeCert u L).pt.T e < (decodeCert u L).pt.kk ((decodeCert u L).pt.J e) ∧
    (decodeCert u L).pt.O ((decodeCert u L).pt.J e) + (decodeCert u L).pt.T e = e := by
  simp [cOcc]; vsimp

end sem

/-! ## The remaining checks -/

def cSignT : C := cSign
def cThree : C := .all tj (E sm) (rd 1 (E tj) tc (reqLe (E tc) (k 3)))
def cSat : C :=
  .all tj (E sm) (rd 4 (E tj) tt (rd 1 (E tj) tc (.both (reqLt (E tt) (E tc))
    (rd 2 (E tj) ta (rd 7 (E ta + E tt) tv (rd 10 (E tv) tg (rd 8 (E ta + E tt) ts
      (.both (whenEq (E tg) (k 1) (reqEq (E ts) (k 1)))
        (whenEq (E ts) (k 1) (reqEq (E tg) (k 1)))))))))))
def cVarLt : C := .all te (E sM) (rd 7 (E te) tv (reqLt (E tv) (E sK)))
def cVarZero : C := whenEq (E sM) (k 0) (reqEq (E sK) (k 0))
def cVarMax : C :=
  whenLt (k 0) (E sM) (.both (reqLt (E sE) (E sM)) (rd 7 (E sE) tv (reqEq (E tv + k 1) (E sK))))
def cN2 (cyc : Bool) : C := if cyc then reqEq (E sn) (E sM + E sK) else reqEq (E sn) (E sM)
def cEndOcc : C :=
  .all te (E sM) (rd 7 (E te) tv (rd 5 (E te) tj (rd 11 (k 2 * E te) ta
    (rd 11 (k 2 * E te + k 1) tb (.both (reqEq (E ta) (k 2 * E tv))
      (reqEq (E tb) (k 2 * E tj + k 1)))))))
def cEndCyc (cyc : Bool) : C :=
  if cyc then
    .all ti (E sK) (rd 11 (k 2 * (E sM + E ti)) ta (rd 11 (k 2 * (E sM + E ti) + k 1) tb
      (.both (reqEq (E ta) (k 2 * E ti)) (.both (whenEq (E ti + k 1) (E sK) (reqEq (E tb) (k 0)))
        (whenNe (E ti + k 1) (E sK) (reqEq (E tb) (k 2 * (E ti + k 1))))))))
  else .ok
def cBound : C :=
  .all td (k 2 * E sn) (rd 12 (E td) ta (rd 13 (E td) tb
    (.both (reqLt (E ta) (k 2 * E sn)) (reqLt (E tb) (k 2 * E sn)))))
def cEdgeK : C :=
  .all th (E sn) (rd 13 (k 2 * E th + k 1) ta (rd 12 (E ta) tb (rd 13 (k 2 * E th) tc
    (rd 12 (E tc) tg (.both (reqEq (E tb) (k 2 * E th)) (reqEq (E tg) (k 2 * E th + k 1)))))))
def cNodeEnd : C :=
  .all td (k 2 * E sn) (rd 12 (E td) ta (rd 11 (E ta) tb (rd 11 (E td) tc (reqEq (E tb) (E tc)))))
def cRankNext : C :=
  .all td (k 2 * E sn) (rd 12 (E td) ta (rd 14 (E ta) tb (rd 14 (E td) tc
    (whenNe (E tb) (k 0) (reqEq (E tb) (E tc + k 1))))))
def cRankLt : C := .all td (k 2 * E sn) (rd 14 (E td) ta (reqLt (E ta) (k 2 * E sn)))
def cRankPrev : C :=
  .all th (E sn) (.both
    (rd 14 (k 2 * E th) ta (whenLt (k 0) (E ta) (rd 13 (k 2 * E th + k 1) tb (rd 14 (E tb) tc
      (reqEq (E tc + k 1) (E ta))))))
    (rd 14 (k 2 * E th + k 1) ta (whenLt (k 0) (E ta) (rd 13 (k 2 * E th) tb (rd 14 (E tb) tc
      (reqEq (E tc + k 1) (E ta)))))))
def cRankUnique : C :=
  .all td (k 2 * E sn) (.all tp (k 2 * E sn) (rd 11 (E td) ta (rd 11 (E tp) tb (rd 14 (E td) tc
    (rd 14 (E tp) tg (whenEq (E ta) (E tb) (whenEq (E tc) (k 0) (whenEq (E tg) (k 0)
      (reqEq (E td) (E tp))))))))))
def cFace : C :=
  .all td (k 2 * E sn) (rd 15 (E td) ta (rd 13 (E td) tb (rd 15 (E tb) tc
    (.both (reqLe (E ta) (E td)) (reqEq (E tc) (E ta))))))
def cComp : C :=
  .all td (k 2 * E sn) (rd 16 (E td) ta (rd 17 (E td) tb (.both (reqLe (E ta) (E td))
    (.both (whenEq (E tb) (k 0) (reqEq (E ta) (E td))) (whenEq (E ta) (E td) (reqEq (E tb) (k 0)))))))
/-- The successor check at dart `dE`, whose edge partner is `eE`. -/
def succAt (dE eE : X) : C :=
  rd 17 dE ta (whenLt (k 0) (E ta) (rd 18 dE tb (.both (reqLt (E tb) (k 2 * E sn))
    (rd 17 (E tb) tc (rd 16 (E tb) tg (rd 16 dE tk (rd 12 dE tp (rd 13 dE tq
      (.both (reqEq (E tc + k 1) (E ta)) (.both (reqEq (E tg) (E tk))
        (whenNe (E tb) eE (whenNe (E tb) (E tp) (reqEq (E tb) (E tq))))))))))))))
def cSucc : C :=
  .all th (E sn) (.both (succAt (k 2 * E th) (k 2 * E th + k 1))
    (succAt (k 2 * E th + k 1) (k 2 * E th)))
/-- A running count in table `τ` of the darts whose entry in table `σ` is `0` (when `self` is
false) or the dart itself (when `self` is true). -/
def cCount (τ σ : Nat) (self : Bool) : C :=
  .both (rd τ (k 0) ta (reqEq (E ta) (k 0)))
    (.all td (k 2 * E sn) (rd τ (E td) ta (rd τ (E td + k 1) tb (rd σ (E td) tc
      (.both (whenEq (E tc) (if self then E td else k 0) (reqEq (E tb) (E ta + k 1)))
        (whenNe (E tc) (if self then E td else k 0) (reqEq (E tb) (E ta))))))))
def cFinal : C :=
  rd 19 (k 2 * E sn) ta (rd 20 (k 2 * E sn) tb (rd 21 (k 2 * E sn) tc
    (reqLe (k 2 * E tc + E sn) (E ta + E tb + k 1))))

theorem not_imp_not_imp {a b c : Prop} : (¬a → ¬b → c) ↔ (a ∨ b ∨ c) := by
  constructor
  · intro h
    by_cases ha : a
    · exact Or.inl ha
    · by_cases hb : b
      · exact Or.inr (Or.inl hb)
      · exact Or.inr (Or.inr (h ha hb))
  · rintro (h | h | h) ha hb
    · exact absurd h ha
    · exact absurd h hb
    · exact h

section sem2

variable {u : List Bool} {L : Nat} {ρ : Sl → Nat} (hg : GlobalWF u L) (he : EnvOK u L ρ)
include hg he

theorem s_sign : Holds u cSign ρ ↔ ∀ e, e < (decodeCert u L).pt.M →
    (decodeCert u L).pt.S e ≤ 1 ∧
      xbits u L ((decodeCert u L).pt.Q e) = some ((decodeCert u L).pt.S e == 1) := by
  simp only [cSign]; vsimp
  apply forall_congr'; intro e; apply imp_congr_right; intro _
  by_cases h1 : T u L 8 e = 1
  · simp [h1]
  · have hb : (T u L 8 e == 1) = false := by simpa using h1
    simp [h1, hb]
theorem s_var : Holds u cVar ρ ↔ ∀ e, e < (decodeCert u L).pt.M → ∀ i, i < (decodeCert u L).pt.V e →
    xbits u L ((decodeCert u L).pt.Q e + 1 + i) = some true := by simp [cVar]; vsimp
theorem s_varEnd : Holds u cVarEnd ρ ↔ ∀ e, e < (decodeCert u L).pt.M →
    xbits u L ((decodeCert u L).pt.Q e + 1 + (decodeCert u L).pt.V e) = some false := by
  simp [cVarEnd]; vsimp
theorem s_next : Holds u cNext ρ ↔ ∀ e, e < (decodeCert u L).pt.M →
    (decodeCert u L).pt.T e + 1 < (decodeCert u L).pt.kk ((decodeCert u L).pt.J e) →
    (decodeCert u L).pt.Q (e + 1) = (decodeCert u L).pt.Q e + (decodeCert u L).pt.V e + 2 := by
  simp [cNext]; vsimp
theorem s_last : Holds u cLast ρ ↔ ∀ e, e < (decodeCert u L).pt.M →
    (decodeCert u L).pt.T e + 1 = (decodeCert u L).pt.kk ((decodeCert u L).pt.J e) →
    (decodeCert u L).pt.P ((decodeCert u L).pt.J e + 1) =
      (decodeCert u L).pt.Q e + (decodeCert u L).pt.V e + 2 := by
  simp [cLast]; vsimp
theorem s_Plast : Holds u cPlast ρ ↔ (decodeCert u L).pt.P (decodeCert u L).pt.m = L := by
  simp [cPlast]; vsimp
theorem s_three : Holds u cThree ρ ↔ ∀ j, j < (decodeCert u L).pt.m →
    (decodeCert u L).pt.kk j ≤ 3 := by simp [cThree]; vsimp
theorem s_sat : Holds u cSat ρ ↔ ∀ j, j < (decodeCert u L).pt.m →
    (decodeCert u L).tsel j < (decodeCert u L).pt.kk j ∧
    ((decodeCert u L).A ((decodeCert u L).pt.V ((decodeCert u L).pt.O j + (decodeCert u L).tsel j)) = 1 ↔
      (decodeCert u L).pt.S ((decodeCert u L).pt.O j + (decodeCert u L).tsel j) = 1) := by
  simp [cSat]; vsimp
  apply forall_congr'; intro j; apply imp_congr_right; intro _
  apply and_congr_right; intro _
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, h2⟩
theorem s_varLt : Holds u cVarLt ρ ↔ ∀ e, e < (decodeCert u L).pt.M →
    (decodeCert u L).pt.V e < (decodeCert u L).K := by simp [cVarLt]; vsimp
theorem s_varZero : Holds u cVarZero ρ ↔ ((decodeCert u L).pt.M = 0 → (decodeCert u L).K = 0) := by
  simp [cVarZero]; vsimp
theorem s_varMax : Holds u cVarMax ρ ↔ (0 < (decodeCert u L).pt.M →
    (decodeCert u L).estar < (decodeCert u L).pt.M ∧
      (decodeCert u L).pt.V (decodeCert u L).estar + 1 = (decodeCert u L).K) := by
  simp [cVarMax]; vsimp
theorem s_n2 (cyc : Bool) : Holds u (cN2 cyc) ρ ↔
    (decodeCert u L).et.n2 = (decodeCert u L).pt.M + (if cyc then (decodeCert u L).K else 0) := by
  cases cyc <;> simp [cN2] <;> vsimp
theorem s_endOcc : Holds u cEndOcc ρ ↔ ∀ e, e < (decodeCert u L).pt.M →
    (decodeCert u L).et.EN (2 * e) = 2 * (decodeCert u L).pt.V e ∧
      (decodeCert u L).et.EN (2 * e + 1) = 2 * (decodeCert u L).pt.J e + 1 := by
  simp [cEndOcc]; vsimp
theorem s_endCyc (cyc : Bool) : Holds u (cEndCyc cyc) ρ ↔ (cyc = true → ∀ i, i < (decodeCert u L).K →
    (decodeCert u L).et.EN (2 * ((decodeCert u L).pt.M + i)) = 2 * i ∧
    (decodeCert u L).et.EN (2 * ((decodeCert u L).pt.M + i) + 1) =
      (if i + 1 = (decodeCert u L).K then 0 else 2 * (i + 1))) := by
  cases cyc
  · simp [cEndCyc]
  · simp only [cEndCyc]; vsimp
    apply forall_congr'; intro i; apply imp_congr_right; intro _
    apply and_congr_right; intro _
    by_cases h1 : i + 1 = T u L 0 2 <;> simp [h1]
theorem s_bound : Holds u cBound ρ ↔ ∀ d, d < 2 * (decodeCert u L).et.n2 →
    (decodeCert u L).et.N d < 2 * (decodeCert u L).et.n2 ∧
      (decodeCert u L).et.F d < 2 * (decodeCert u L).et.n2 := by simp [cBound]; vsimp
theorem s_edgeK : Holds u cEdgeK ρ ↔ ∀ h, h < (decodeCert u L).et.n2 →
    (decodeCert u L).et.N ((decodeCert u L).et.F (2 * h + 1)) = 2 * h ∧
      (decodeCert u L).et.N ((decodeCert u L).et.F (2 * h)) = 2 * h + 1 := by
  simp [cEdgeK]; vsimp
theorem s_nodeEnd : Holds u cNodeEnd ρ ↔ ∀ d, d < 2 * (decodeCert u L).et.n2 →
    (decodeCert u L).et.EN ((decodeCert u L).et.N d) = (decodeCert u L).et.EN d := by
  simp [cNodeEnd]; vsimp
theorem s_rankNext : Holds u cRankNext ρ ↔ ∀ d, d < 2 * (decodeCert u L).et.n2 →
    (decodeCert u L).et.R ((decodeCert u L).et.N d) = (decodeCert u L).et.R d + 1 ∨
      (decodeCert u L).et.R ((decodeCert u L).et.N d) = 0 := by
  simp [cRankNext]; vsimp
  apply forall_congr'; intro d; apply imp_congr_right; intro _
  by_cases h0 : T u L 14 (T u L 12 d) = 0 <;> simp [h0]
theorem s_rankLt : Holds u cRankLt ρ ↔ ∀ d, d < 2 * (decodeCert u L).et.n2 →
    (decodeCert u L).et.R d < 2 * (decodeCert u L).et.n2 := by simp [cRankLt]; vsimp
theorem s_rankPrev : Holds u cRankPrev ρ ↔ ∀ h, h < (decodeCert u L).et.n2 →
    (0 < (decodeCert u L).et.R (2 * h) →
      (decodeCert u L).et.R ((decodeCert u L).et.F (2 * h + 1)) + 1 = (decodeCert u L).et.R (2 * h)) ∧
    (0 < (decodeCert u L).et.R (2 * h + 1) →
      (decodeCert u L).et.R ((decodeCert u L).et.F (2 * h)) + 1 =
        (decodeCert u L).et.R (2 * h + 1)) := by
  simp [cRankPrev]; vsimp
theorem s_rankUnique : Holds u cRankUnique ρ ↔ ∀ d, d < 2 * (decodeCert u L).et.n2 →
    ∀ d', d' < 2 * (decodeCert u L).et.n2 →
    (decodeCert u L).et.EN d = (decodeCert u L).et.EN d' → (decodeCert u L).et.R d = 0 →
      (decodeCert u L).et.R d' = 0 → d = d' := by
  simp [cRankUnique]; vsimp
theorem s_face : Holds u cFace ρ ↔ ∀ d, d < 2 * (decodeCert u L).et.n2 →
    (decodeCert u L).et.FL d ≤ d ∧
      (decodeCert u L).et.FL ((decodeCert u L).et.F d) = (decodeCert u L).et.FL d := by
  simp [cFace]; vsimp
theorem s_comp : Holds u cComp ρ ↔ ∀ d, d < 2 * (decodeCert u L).et.n2 →
    (decodeCert u L).et.CL d ≤ d ∧
      ((decodeCert u L).et.D d = 0 ↔ (decodeCert u L).et.CL d = d) := by
  simp [cComp]; vsimp
  apply forall_congr'; intro d; apply imp_congr_right; intro _
  apply and_congr_right; intro _
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, h2⟩
theorem s_succ : Holds u cSucc ρ ↔ ∀ h, h < (decodeCert u L).et.n2 →
    (0 < (decodeCert u L).et.D (2 * h) →
      (decodeCert u L).et.SU (2 * h) < 2 * (decodeCert u L).et.n2 ∧
      (decodeCert u L).et.D ((decodeCert u L).et.SU (2 * h)) + 1 = (decodeCert u L).et.D (2 * h) ∧
      (decodeCert u L).et.CL ((decodeCert u L).et.SU (2 * h)) = (decodeCert u L).et.CL (2 * h) ∧
      ((decodeCert u L).et.SU (2 * h) = 2 * h + 1 ∨
        (decodeCert u L).et.SU (2 * h) = (decodeCert u L).et.N (2 * h) ∨
        (decodeCert u L).et.SU (2 * h) = (decodeCert u L).et.F (2 * h))) ∧
    (0 < (decodeCert u L).et.D (2 * h + 1) →
      (decodeCert u L).et.SU (2 * h + 1) < 2 * (decodeCert u L).et.n2 ∧
      (decodeCert u L).et.D ((decodeCert u L).et.SU (2 * h + 1)) + 1 =
        (decodeCert u L).et.D (2 * h + 1) ∧
      (decodeCert u L).et.CL ((decodeCert u L).et.SU (2 * h + 1)) =
        (decodeCert u L).et.CL (2 * h + 1) ∧
      ((decodeCert u L).et.SU (2 * h + 1) = 2 * h ∨
        (decodeCert u L).et.SU (2 * h + 1) = (decodeCert u L).et.N (2 * h + 1) ∨
        (decodeCert u L).et.SU (2 * h + 1) = (decodeCert u L).et.F (2 * h + 1))) := by
  simp only [cSucc, succAt]; vsimp
  simp only [not_imp_not_imp]
theorem s_count (τ σ : Nat) (self : Bool) : Holds u (cCount τ σ self) ρ ↔
    T u L τ 0 = 0 ∧ ∀ d, d < 2 * (decodeCert u L).et.n2 →
      T u L τ (d + 1) = T u L τ d + (if T u L σ d = (if self then d else 0) then 1 else 0) := by
  cases self
  · simp only [cCount]; vsimp
    intro _
    apply forall_congr'; intro d; apply imp_congr_right; intro _
    by_cases h0 : T u L σ d = 0 <;> simp [h0]
  · simp only [cCount]; vsimp
    intro _
    apply forall_congr'; intro d; apply imp_congr_right; intro _
    by_cases h0 : T u L σ d = d <;> simp [h0]
theorem s_final : Holds u cFinal ρ ↔ 2 * (decodeCert u L).et.cC (2 * (decodeCert u L).et.n2) +
    (decodeCert u L).et.n2 ≤ (decodeCert u L).et.cR (2 * (decodeCert u L).et.n2) +
      (decodeCert u L).et.cF (2 * (decodeCert u L).et.n2) + 1 := by
  simp [cFinal]; vsimp

end sem2

end Complexity.Planar.Vf
