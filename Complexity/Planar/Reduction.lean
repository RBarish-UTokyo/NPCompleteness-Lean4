module

public import Complexity.Planar.EmitGrid
public import Complexity.CookLevinEmitter
public import Complexity.StackTableauMachineBounds
public import Complexity.Composition
import Lean.Elab.Tactic.Omega

/-!
# Reducing NP to planar 3-SAT

For a language in NP, Cook–Levin provides a formula emitter `P` with `x ∈ L` iff the formula
`φ = P.emit x` is satisfiable.  The reduction is the composition of two emitters, each running
in polynomial time:

1. `stage1 P` writes the occurrence table of `φ` (`Complexity.Planar.EmitTable`), padded by
   `A n` empty clauses;
2. `stage2 P G` reads that word `w`, recovers the input length `n` and the number `M` of clauses
   of `φ` from `|w| = 2 A n + 1 + 5 M R n` by trying all candidates (the padding `A n =
   (n + 1) B n` with `B n > 5 M n R n` makes them unique), and emits with `G` the grid formula
   of the table (`gridProg`, for Lichtenstein's version) or the grid formula with the
   subdivided variable cycle (`plainProg`).

The grid formula is satisfiable iff `φ` is, and it is a (cycle-)planar 3-CNF formula.
-/

@[expose] public section

namespace Complexity.Planar.Emit

open StackTableauEmitter SAT Grid

/-! ## The second stage -/

section stage2

variable (P : ClauseProgram 1)

/-- A bound in the candidate length `var 1` at depth three. -/
def at1 (e : NumExpr 1) : NumExpr 3 := e.rename (fun _ => 1)

/-- The length of the first-stage word for the candidates `var 1` and `var 0`. -/
def lenE : NumExpr 3 :=
  .add (.add (.mul (.const 2) (at1 (Ax P))) (.const 1)) (.mul (.const 5) (.mul (.var 0) (at1 (Rx P))))

/-- The second stage: the emitter `G` runs for the unique fitting candidates. -/
def stage2 (G : ClauseProgram 3) : ClauseProgram 1 :=
  .forDown (.var 0) (.forDown (.var 1)
    (.ifLe (lenE P) (.var 2) (.ifLe (.var 2) (lenE P) (.ifLe (.var 0) (at1 (Mx P)) G .skip)
      .skip) .skip))

/-- The grid emitter at depth three. -/
def cycG : ClauseProgram 3 := gridProg (at1 (Ax P)) (.var 0) (at1 (Rx P)) (at1 (Wx P))

/-- The plain emitter at depth three. -/
def plainG : ClauseProgram 3 := plainProg (at1 (Ax P)) (.var 0) (at1 (Rx P)) (at1 (Wx P))

/-- Values of the bounds. -/
def vA (n : Nat) : Nat := (Ax P).eval (fun _ => n)
def vB (n : Nat) : Nat := (Bx P).eval (fun _ => n)
def vM (n : Nat) : Nat := (Mx P).eval (fun _ => n)
def vW (n : Nat) : Nat := (Wx P).eval (fun _ => n)
def vR (n : Nat) : Nat := (Rx P).eval (fun _ => n)

theorem vA_eq (n : Nat) : vA P n = (n + 1) * vB P n := rfl
theorem vB_eq (n : Nat) : vB P n = 5 * vM P n * vR P n + 1 := rfl
theorem vR_eq (n : Nat) : vR P n = 2 * vW P n := rfl
theorem vW_pos (n : Nat) : 1 ≤ vW P n := by
  show 1 ≤ (Wx P).eval (fun _ => n)
  simp only [Wx, NumExpr.eval]
  omega

theorem at1_eval (e : NumExpr 1) (m n L : Nat) :
    (at1 e).eval (extend m (extend n (fun _ => L))) = e.eval (fun _ => n) := by
  simp [at1]

theorem lenE_eval (m n L : Nat) :
    (lenE P).eval (extend m (extend n (fun _ => L))) = 2 * vA P n + 1 + 5 * (m * vR P n) := by
  simp only [lenE, NumExpr.eval, at1_eval, extend_zero]
  rfl

/-- **The candidates are unique.** -/
theorem unique_dims {n M n' m' : Nat} (hM : M ≤ vM P n) (hm' : m' ≤ vM P n')
    (h : 2 * vA P n' + 1 + 5 * (m' * vR P n') = 2 * vA P n + 1 + 5 * (M * vR P n)) :
    n' = n ∧ m' = M := by
  have key : ∀ x m, m ≤ vM P x → 5 * (m * vR P x) + 1 ≤ vB P x := by
    intro x m hm
    rw [vB_eq]
    have := Nat.mul_le_mul_right (vR P x) hm
    rw [Nat.mul_assoc]
    omega
  have k1 := key n M hM
  have k2 := key n' m' hm'
  have eA : ∀ x, vA P x = x * vB P x + vB P x := by
    intro x; rw [vA_eq, Nat.succ_mul]
  rw [eA, eA] at h
  rcases Nat.lt_trichotomy n' n with hlt | heq | hgt
  · exfalso
    have hb : vB P n' ≤ vB P n := mono_Bx P n' n (by omega)
    have p1 : n' * vB P n' ≤ n' * vB P n := Nat.mul_le_mul_left _ hb
    have p2 : (n' + 1) * vB P n ≤ n * vB P n := Nat.mul_le_mul_right _ hlt
    rw [Nat.succ_mul] at p2
    omega
  · subst heq
    refine ⟨rfl, ?_⟩
    have hR : 0 < vR P n' := by rw [vR_eq]; have := vW_pos P n'; omega
    have : m' * vR P n' = M * vR P n' := by omega
    exact Nat.eq_of_mul_eq_mul_right hR this
  · exfalso
    have hb : vB P n ≤ vB P n' := mono_Bx P n n' (by omega)
    have p1 : n * vB P n ≤ n * vB P n' := Nat.mul_le_mul_left _ hb
    have p2 : (n + 1) * vB P n' ≤ n' * vB P n' := Nat.mul_le_mul_right _ hgt
    rw [Nat.succ_mul] at p2
    omega

theorem flatMap_single {α : Type} {N i0 : Nat} (hi0 : i0 < N) (F : Nat → List α)
    (h : ∀ i, i < N → i ≠ i0 → F i = []) : (List.range N).reverse.flatMap F = F i0 := by
  induction N with
  | zero => omega
  | succ N ih =>
    rw [range_reverse_succ_flatMap]
    rcases Nat.lt_or_ge i0 N with hlt | hge
    · rw [h N (by omega) (by omega), ih hlt (fun i hi hne => h i (by omega) hne), List.nil_append]
    · have : i0 = N := by omega
      subst this
      have : (List.range i0).reverse.flatMap F = [] := by
        rw [List.flatMap_eq_nil_iff]
        intro i hi
        simp only [List.mem_reverse, List.mem_range] at hi
        exact h i (by omega) (by omega)
      rw [this, List.append_nil]

/-- **The second stage runs `G` once, for the true candidates.** -/
theorem stage2_emit (G : ClauseProgram 3) (w : Word) {n M : Nat} (hM : M ≤ vM P n)
    (hw : w.length = 2 * vA P n + 1 + 5 * (M * vR P n)) :
    (stage2 P G).emit w (fun _ => w.length) =
      G.emit w (extend M (extend n (fun _ => w.length))) := by
  have hB : 1 ≤ vB P n := by rw [vB_eq]; omega
  have hnA : n < vA P n := by
    rw [vA_eq, Nat.succ_mul]
    have := Nat.mul_le_mul_left n hB
    omega
  have hR : 1 ≤ vR P n := by rw [vR_eq]; have := vW_pos P n; omega
  have hMR : M ≤ M * vR P n := by
    have := Nat.mul_le_mul_left M hR; omega
  have body : ∀ n' m', (ClauseProgram.ifLe (lenE P) (.var 2)
      (.ifLe (.var 2) (lenE P) (.ifLe (.var 0) (at1 (Mx P)) G .skip) .skip) .skip).emit w
        (extend m' (extend n' (fun _ => w.length))) =
      if 2 * vA P n' + 1 + 5 * (m' * vR P n') = w.length ∧ m' ≤ vM P n' then
        G.emit w (extend m' (extend n' (fun _ => w.length))) else [] := by
    intro n' m'
    have e0 : (NumExpr.var 0 : NumExpr 3).eval (extend m' (extend n' (fun _ => w.length))) = m' :=
      rfl
    have e2 : (NumExpr.var 2 : NumExpr 3).eval (extend m' (extend n' (fun _ => w.length))) =
        w.length := rfl
    have eM : (at1 (Mx P)).eval (extend m' (extend n' (fun _ => w.length))) = vM P n' :=
      at1_eval _ _ _ _
    show (if (lenE P).eval (extend m' (extend n' (fun _ => w.length))) ≤
        (NumExpr.var 2 : NumExpr 3).eval (extend m' (extend n' (fun _ => w.length))) then
        (if (NumExpr.var 2 : NumExpr 3).eval (extend m' (extend n' (fun _ => w.length))) ≤
          (lenE P).eval (extend m' (extend n' (fun _ => w.length))) then
          (if (NumExpr.var 0 : NumExpr 3).eval (extend m' (extend n' (fun _ => w.length))) ≤
            (at1 (Mx P)).eval (extend m' (extend n' (fun _ => w.length))) then
            G.emit w (extend m' (extend n' (fun _ => w.length))) else []) else []) else []) = _
    rw [lenE_eval, e0, e2, eM]
    by_cases hc : 2 * vA P n' + 1 + 5 * (m' * vR P n') = w.length ∧ m' ≤ vM P n'
    · rw [ite_eq_left hc]
      have c1 : 2 * vA P n' + 1 + 5 * (m' * vR P n') ≤ w.length := by omega
      have c2 : w.length ≤ 2 * vA P n' + 1 + 5 * (m' * vR P n') := by omega
      simp only [c1, c2, hc.2, ↓reduceIte]
    · rw [ite_eq_right hc]
      by_cases c1 : 2 * vA P n' + 1 + 5 * (m' * vR P n') ≤ w.length <;>
        by_cases c2 : w.length ≤ 2 * vA P n' + 1 + 5 * (m' * vR P n') <;>
        by_cases c3 : m' ≤ vM P n' <;>
        simp only [c1, c2, c3, ↓reduceIte] <;>
        exact absurd ⟨by omega, c3⟩ hc
  unfold stage2
  simp only [ClauseProgram.emit_forDown]
  have e0 : (NumExpr.var 0 : NumExpr 1).eval (fun _ => w.length) = w.length := rfl
  have e1 : ∀ n', (NumExpr.var 1 : NumExpr 2).eval (extend n' (fun _ => w.length)) =
      w.length := fun _ => rfl
  rw [e0]
  simp only [e1, body]
  rw [flatMap_single (i0 := n) (by omega)]
  · rw [flatMap_single (i0 := M) (by omega)]
    · rw [ite_eq_left ⟨hw.symm, hM⟩]
    · intro m' _ hne
      rw [ite_eq_right]
      intro ⟨h1, h2⟩
      exact hne (unique_dims P hM h2 (h1.trans hw)).2
  · intro n' _ hne
    rw [List.flatMap_eq_nil_iff]
    intro m' _
    rw [ite_eq_right]
    intro ⟨h1, h2⟩
    exact hne (unique_dims P hM h2 (h1.trans hw)).1

end stage2

/-! ## Correctness -/

theorem sat_iff_bits (φ : CNF) (W : Nat) (hW : ∀ c ∈ φ, ∀ l ∈ c, l.var < W)
    (bits : Nat → Nat → Bool × Bool)
    (hb : ∀ j (hj : j < φ.length), ∀ v, v < W → bits j v = (bitB φ[j] v 1, bitB φ[j] v 0)) :
    (∃ a : Assignment, ∀ j, j < φ.length → ∃ v, v < W ∧
      litSat (bits j v).1 (bits j v).2 (a v) = true) ↔ Satisfiable φ := by
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨a, ?_⟩
    unfold evalCNF
    rw [List.all_eq_true]
    intro c hc
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hc
    obtain ⟨v, hv, hs⟩ := ha j hj
    rw [hb j hj v hv] at hs
    unfold evalClause
    rw [List.any_eq_true]
    unfold litSat bitB at hs
    simp only [Bool.or_eq_true, Bool.and_eq_true, List.any_eq_true, beq_iff_eq] at hs
    rcases hs with ⟨⟨l, hl, hlv, hlp⟩, hav⟩ | ⟨⟨l, hl, hlv, hlp⟩, hav⟩
    · refine ⟨l, hl, ?_⟩
      unfold evalLiteral
      simp only [show (1 == 1) = true from rfl] at hlp
      rw [show l.positive = true by simpa using hlp, hlv]
      exact hav
    · refine ⟨l, hl, ?_⟩
      unfold evalLiteral
      have : l.positive = false := by simpa using hlp
      rw [this, hlv]
      simpa using hav
  · rintro ⟨a, ha⟩
    refine ⟨a, fun j hj => ?_⟩
    unfold evalCNF at ha
    rw [List.all_eq_true] at ha
    have hc := ha φ[j] (List.getElem_mem hj)
    unfold evalClause at hc
    rw [List.any_eq_true] at hc
    obtain ⟨l, hl, hev⟩ := hc
    refine ⟨l.var, hW _ (List.getElem_mem hj) l hl, ?_⟩
    rw [hb j hj l.var (hW _ (List.getElem_mem hj) l hl)]
    unfold litSat bitB
    unfold evalLiteral at hev
    cases hp : l.positive
    · rw [hp] at hev
      have hneg : (φ[j].any fun l' => l'.var == l.var && l'.positive == ((0 : Nat) == 1)) = true :=
        List.any_eq_true.mpr ⟨l, hl, by simp [hp]⟩
      rw [hneg]
      simp at hev
      simp [hev]
    · rw [hp] at hev
      have hpos : (φ[j].any fun l' => l'.var == l.var && l'.positive == ((1 : Nat) == 1)) = true :=
        List.any_eq_true.mpr ⟨l, hl, by simp [hp]⟩
      rw [hpos]
      simp at hev
      simp [hev]

section correct

variable (P : ClauseProgram 1) (x : Word)

/-- The first-stage word. -/
def word1 : Word := encode ((stage1 P).emit x (fun _ => x.length))

theorem word1_eq : word1 P x = encode (List.replicate (vA P x.length) [] ++
    ((P.emit x (fun _ => x.length)).flatMap (rowBits (vW P x.length))).map unitOf) := by
  unfold word1
  rw [stage1_emit]
  rfl

theorem word1_length : (word1 P x).length =
    2 * vA P x.length + 1 + 5 * ((P.emit x (fun _ => x.length)).length * vR P x.length) := by
  rw [word1_eq, table_length]
  rfl

theorem bits_word1 : ∀ j (hj : j < (P.emit x (fun _ => x.length)).length), ∀ v, v < vW P x.length →
    bitsW (word1 P x) (vA P x.length) (P.emit x (fun _ => x.length)).length (vR P x.length)
      (vW P x.length) j v =
      (bitB (P.emit x (fun _ => x.length))[j] v 1, bitB (P.emit x (fun _ => x.length))[j] v 0) := by
  intro j hj v hv
  unfold bitsW
  rw [vR_eq, word1_eq, table_bit _ _ _ hj hv (by omega), table_bit _ _ _ hj hv (by omega)]
  rfl

/-- The emitted grid formula. -/
def gridOut : CNF := (stage2 P (cycG P)).emit (word1 P x) (fun _ => (word1 P x).length)

/-- The emitted plain formula. -/
def plainOut : CNF := (stage2 P (plainG P)).emit (word1 P x) (fun _ => (word1 P x).length)

theorem gridOut_eq : gridOut P x = gridCNF (vW P x.length) (P.emit x (fun _ => x.length)).length
    (bitsW (word1 P x) (vA P x.length) (P.emit x (fun _ => x.length)).length (vR P x.length)
      (vW P x.length)) := by
  unfold gridOut
  rw [stage2_emit P _ _ (emit_length_le P x) (word1_length P x), cycG, gridProg_emit]
  simp only [at1_eval]
  rfl

theorem plainOut_eq : plainOut P x = plainCNF (vW P x.length) (P.emit x (fun _ => x.length)).length
    (bitsW (word1 P x) (vA P x.length) (P.emit x (fun _ => x.length)).length (vR P x.length)
      (vW P x.length)) := by
  unfold plainOut
  rw [stage2_emit P _ _ (emit_length_le P x) (word1_length P x), plainG, plainProg_emit]
  simp only [at1_eval]
  rfl

theorem gridOut_sat : Satisfiable (gridOut P x) ↔ Satisfiable (P.emit x (fun _ => x.length)) := by
  rw [gridOut_eq, grid_satisfiable_iff]
  exact sat_iff_bits _ _ (emit_var_lt P x) _ (bits_word1 P x)

theorem plainOut_sat : Satisfiable (plainOut P x) ↔ Satisfiable (P.emit x (fun _ => x.length)) := by
  rw [plainOut_eq, plain_satisfiable_iff, grid_satisfiable_iff]
  exact sat_iff_bits _ _ (emit_var_lt P x) _ (bits_word1 P x)

theorem gridOut_planar : IsCyclePlanarThreeCNF (gridOut P x) := by
  rw [gridOut_eq]; exact grid_isCyclePlanar _ _ _

theorem plainOut_planar : IsPlanarThreeCNF (plainOut P x) := by
  rw [plainOut_eq]; exact plain_isPlanar _ _ _

end correct

/-! ## Hardness -/

theorem cyclePlanar_encode_iff (f : CNF) :
    CyclePlanarThreeSAT (encode f) ↔ IsCyclePlanarThreeCNF f ∧ Satisfiable f := by
  constructor
  · rintro ⟨g, hg, hc, hs⟩
    rw [encode_injective g f hg] at hc hs
    exact ⟨hc, hs⟩
  · rintro ⟨hc, hs⟩
    exact ⟨f, rfl, hc, hs⟩

theorem planar_encode_iff (f : CNF) :
    PlanarThreeSAT (encode f) ↔ IsPlanarThreeCNF f ∧ Satisfiable f := by
  constructor
  · rintro ⟨g, hg, hc, hs⟩
    rw [encode_injective g f hg] at hc hs
    exact ⟨hc, hs⟩
  · rintro ⟨hc, hs⟩
    exact ⟨f, rfl, hc, hs⟩

theorem polyTime_two_stages (P G : ClauseProgram 1) :
    PolyTime (fun x => encode (G.emit (encode (P.emit x (fun _ => x.length)))
      (fun _ => (encode (P.emit x (fun _ => x.length))).length))) :=
  polyTime_comp (f := fun x => encode (P.emit x (fun _ => x.length)))
    (g := fun w => encode (G.emit w (fun _ => w.length)))
    (polyTime_emitter G) (polyTime_emitter P)

theorem cyclePlanarThreeSAT_npHard : NPHard CyclePlanarThreeSAT := by
  intro L hL
  obtain ⟨P, hP⟩ := CookLevinEmitter.inNP_emitter hL
  refine ⟨fun x => encode (gridOut P x), polyTime_two_stages (stage1 P) (stage2 P (cycG P)), ?_⟩
  intro x
  rw [hP x, SAT_encode_iff, cyclePlanar_encode_iff, gridOut_sat]
  exact ⟨fun h => ⟨gridOut_planar P x, h⟩, fun h => h.2⟩

theorem planarThreeSAT_npHard : NPHard PlanarThreeSAT := by
  intro L hL
  obtain ⟨P, hP⟩ := CookLevinEmitter.inNP_emitter hL
  refine ⟨fun x => encode (plainOut P x), polyTime_two_stages (stage1 P) (stage2 P (plainG P)), ?_⟩
  intro x
  rw [hP x, SAT_encode_iff, planar_encode_iff, plainOut_sat]
  exact ⟨fun h => ⟨plainOut_planar P x, h⟩, fun h => h.2⟩

end Complexity.Planar.Emit
