module

public import Complexity.NTM.Guess
public import Complexity.NTM.Checker
public import Complexity.NTM.ClockProgram
public import Complexity.NTM.CompileTape
import Lean.Elab.Tactic.Omega

/-!
# From verifiers to nondeterministic machines

For a verifier `V` with certificate bound `p = powerBound c k`, the nondeterministic
machine `guesser V c k` runs three phases on the tape, each entered from the accepting halt
of the previous one:

1. the compiled clock program writes `1^(2 p(|x|))` into register 0 and `x` into
   register 1 of the tape encoding of ten stack registers;
2. `guessMachine` overwrites the clock with `2 p(|x|)` guessed bits `g`, one choice each,
   and returns to the start of the register encoding;
3. the compiled controller of `checkerMachine V` (started directly on the register
   encoding) decodes the certificate `decodeW g`, which ranges over all words of length at
   most `p(|x|)`, and simulates `V` on `pairWords x (decodeW g)`.

The first and third phases are deterministic and the second takes `2 * 2 p(|x|) + 2`
instructions whatever the choices, so every computation path halts within a polynomial
bound.
-/

@[expose] public section

namespace Complexity.NTM

open StackMachine (Registers set)
open StackSimulation (compiledController instructionBudget)

/-- The clock as a single-tape machine. -/
def clockTape (c k : Nat) : Machine := StackCompile.compile (clockMachine c k)

/-- The checker's finite controller, started on encoded registers. -/
def checkerTape (V : Machine) : Machine := compiledController (checkerMachine V)

/-- The nondeterministic machine: clock, guess, check. -/
def guesser (V : Machine) (c k : Nat) : NMachine :=
  seq (lift (clockTape c k)) (seq guessMachine (lift (checkerTape V)))

/-! ## Bounds -/

def guesserCheckBound (c k cV kV n : Nat) : Nat :=
  checkTime (clockLength c k n) n (powerBound cV kV (2 * n + 1 + clockLength c k n))

def guesserCapacity (c k cV kV n : Nat) : Nat :=
  clockLength c k n + n + guesserCheckBound c k cV kV n

def guesserTail (V : Machine) (c k cV kV n : Nat) : Nat :=
  guesserCheckBound c k cV kV n *
    instructionBudget (checkerMachine V) (guesserCapacity c k cV kV n)

def guesserBound (V : Machine) (c k cV kV n : Nat) : Nat :=
  StackCompile.budget (clockMachine c k) n (clockTime c k n) + (2 * clockLength c k n + 2) +
    guesserTail V c k cV kV n

theorem polynomialBound_guesserCheckBound (c k cV kV : Nat) :
    PolynomialBound (guesserCheckBound c k cV kV) := by
  have hL := polynomialBound_clockLength c k
  have hin := ((PolynomialBound.constant 2).mul PolynomialBound.identity).add
    (PolynomialBound.constant 1) |>.add hL
  have hV := (PolynomialBound.power cV kV).comp hin
  have h := ((((PolynomialBound.constant 10).mul hL).add
    ((PolynomialBound.constant 15).mul PolynomialBound.identity)).add
      (PolynomialBound.constant 30)).add ((PolynomialBound.constant 5).mul hV)
  exact h.weaken (fun n => Nat.le_refl _)

theorem polynomialBound_guesserBound (V : Machine) (c k cV kV : Nat) :
    PolynomialBound (guesserBound V c k cV kV) := by
  have hL := polynomialBound_clockLength c k
  have hC := polynomialBound_guesserCheckBound c k cV kV
  have hcap : PolynomialBound (guesserCapacity c k cV kV) :=
    ((hL.add PolynomialBound.identity).add hC).weaken (fun n => Nat.le_refl _)
  have hib : PolynomialBound
      (fun n => instructionBudget (checkerMachine V) (guesserCapacity c k cV kV n)) :=
    (((PolynomialBound.constant 4).mul
      (((PolynomialBound.constant ((checkerMachine V).stacks + 1)).mul
        (hcap.add (PolynomialBound.constant 1))).add (PolynomialBound.constant 1))).add
          (PolynomialBound.constant 13)).weaken (fun n => Nat.le_refl _)
  have hbudget := StackCompile.polynomialBound_budget (clockMachine c k) (clockTime c k)
    (polynomialBound_clockTime c k)
  exact ((hbudget.add (((PolynomialBound.constant 2).mul hL).add
    (PolynomialBound.constant 2))).add (hC.mul hib)).weaken (fun n => Nat.le_refl _)

/-! ## The register encoding around register 0 -/

theorem homeTape_register_zero {stacks : Nat} (r : Registers stacks) :
    ∃ rest : List Symbol,
      StackEncoding.homeTape r = ⟨[.blank], .sep :: ((r 0).map Symbol.bit ++ .sep :: rest)⟩ ∧
      ∀ g : List Bool, StackEncoding.homeTape (set r 0 g) =
        ⟨[.blank], .sep :: (g.map Symbol.bit ++ .sep :: rest)⟩ := by
  obtain ⟨rest, ht⟩ := StackEncoding.tail_eq_cons r 0
  have hb : StackEncoding.before r 0 = [] := by simp [StackEncoding.before]
  refine ⟨rest, ?_, ?_⟩
  · simp only [StackEncoding.homeTape]
    rw [StackEncoding.encodeRegisters_split r 0, hb]
    simp [StackEncoding.suffix, ht, StackCompiler.stackPrefix]
  · intro g
    simp only [StackEncoding.homeTape]
    rw [StackEncoding.encodeRegisters_set r 0 g, hb]
    simp [ht, StackCompiler.stackPrefix]

/-! ## The first two phases -/

theorem guesser_phases (V : Machine) (c k : Nat) (x : Word) :
    ∃ off : Nat,
      off ≤ StackCompile.budget (clockMachine c k) x.length (clockTime c k x.length) ∧
      ∃ R : Registers 9, ClockResult c k x R ∧
      ∀ cs : List Bool, cs.length = off + (2 * clockLength c k x.length + 2) →
        ∃ q' t', Steps (guesser V c k) (guesser V c k).start (Tape.ofInput x) cs q' t' ∧
          (q' = seqRight (lift (clockTape c k)) (seq guessMachine (lift (checkerTape V)))
            (seqRight guessMachine (lift (checkerTape V)) (lift (checkerTape V)).start) ∧
          (StackEncoding.homeTape
            (set R 0 ((cs.drop off).take (clockLength c k x.length)))).Equivalent t') := by
  obtain ⟨T₁, R₁, hT₁, hrun₁, hR₁⟩ := clock_runs c k x
  obtain ⟨time₁, t₁, htime₁, hD1, heq₁⟩ :=
    compile_simulate_tape (clockMachine c k) T₁ x (true, R₁) hrun₁
  obtain ⟨n₁, q₁, hn₁, hsteps₁, hhalt₁⟩ :=
    halt_steps (clockTape c k) time₁ (clockTape c k).start (Tape.ofInput x) true t₁ hD1
  have hbudget := StackCompile.budget_mono (clockMachine c k) x.length hT₁
  refine ⟨n₁ + 1, by omega, R₁, hR₁, ?_⟩
  intro cs hcs
  -- split the choices
  obtain ⟨c₁, B, hB⟩ : ∃ c₁ B, cs.drop n₁ = c₁ :: B := by
    cases h : cs.drop n₁ with
    | nil => have := congrArg List.length h; simp at this; omega
    | cons c₁ B => exact ⟨c₁, B, rfl⟩
  have hBlen : B.length = 2 * clockLength c k x.length + 2 := by
    have := congrArg List.length hB; simp at this; omega
  obtain ⟨c₂, hB2⟩ : ∃ c₂, B.drop (2 * clockLength c k x.length + 1) = [c₂] := by
    cases h : B.drop (2 * clockLength c k x.length + 1) with
    | nil => have := congrArg List.length h; simp at this; omega
    | cons c₂ rest =>
      have := congrArg List.length h
      simp at this
      have hr : rest = [] := List.length_eq_zero_iff.mp (by omega)
      exact ⟨c₂, by rw [hr]⟩
  have hcsplit :
      cs = cs.take n₁ ++ ([c₁] ++ (B.take (2 * clockLength c k x.length + 1) ++ [c₂])) := by
    rw [← hB2, List.take_append_drop, List.singleton_append, ← hB, List.take_append_drop]
  have hdrop : cs.drop (n₁ + 1) = B := by
    rw [← List.drop_drop, hB]; rfl
  -- phase 1: the clock
  have hlenA : (cs.take n₁).length = n₁ := by
    have := congrArg List.length hB
    simp at this
    simp
    omega
  have hA := (hsteps₁ (cs.take n₁) hlenA).seqLeft (B := seq guessMachine (lift (checkerTape V)))
  have hcont₁ := steps_continue (lift (clockTape c k)) (seq guessMachine (lift (checkerTape V)))
    c₁ q₁ t₁ hhalt₁
  -- phase 2: guessing on the canonical tape, transferred to the actual tape
  obtain ⟨rest, hhome, hhomeSet⟩ := homeTape_register_zero R₁
  have hR0 : R₁ 0 = List.replicate (clockLength c k x.length) true := hR₁.1
  let canonical : Tape :=
    ⟨[.sep, .blank],
      (List.replicate (clockLength c k x.length) true).map Symbol.bit ++ .sep :: rest⟩
  have hcanon : canonical.Equivalent (t₁.write t₁.read) := by
    have h1 : ((StackEncoding.homeTape R₁).move .right) = canonical := by
      rw [hhome, hR0]; rfl
    rw [← h1]
    exact heq₁.trans (write_read_equivalent t₁).symm
  have hG := guess_phase (List.replicate (clockLength c k x.length) true) [.blank] rest
    (B.take (2 * clockLength c k x.length + 1)) (by simp; omega)
  simp only [List.length_replicate] at hG
  obtain ⟨u', hGu, hequ⟩ := hG.equivalent (t₁.write t₁.read) hcanon
  have hu'read : u'.read = .sep := by rw [← hequ.read]; rfl
  have hcont₂ := steps_continue guessMachine (lift (checkerTape V)) c₂ 1 u'
    (guess_halt c₂ u' hu'read)
  have hBsteps := (hGu.seqLeft (B := lift (checkerTape V))).trans hcont₂
  have hall := hA.trans (hcont₁.trans (hBsteps.seqRight (A := lift (clockTape c k))))
  refine ⟨_, u'.write u'.read, ?_, rfl, ?_⟩
  · rw [hcsplit]
    exact hall
  · rw [hdrop, hhomeSet]
    have htake : (B.take (2 * clockLength c k x.length + 1)).take (clockLength c k x.length) =
        B.take (clockLength c k x.length) := by
      rw [List.take_take]; congr 1; omega
    rw [← htake]
    exact hequ.trans (write_read_equivalent u').symm

/-! ## The third phase -/

theorem checker_phase (V : Machine) (c k cV kV : Nat)
    (hV : ∀ u : Word, ∃ time decision tape, time ≤ powerBound cV kV u.length ∧
      runInput V time u = some (decision, tape))
    (x g : Word) (R : Registers 9) (hR : ClockResult c k x R)
    (hg : g.length = clockLength c k x.length) (t : Tape)
    (ht : (StackEncoding.homeTape (set R 0 g)).Equivalent t) :
    ∃ time res, time ≤ guesserTail V c k cV kV x.length ∧
      Complexity.run (checkerTape V) time ⟨(checkerTape V).start, t⟩ = some res ∧
      (res.1 = true ↔ Accepts V (pairWords x (decodeW g))) := by
  let u := pairWords x (decodeW g)
  obtain ⟨T, d, tape, hT, hVu⟩ := hV u
  have hdec := decodeW_length g
  have hu : u.length ≤ 2 * x.length + 1 + clockLength c k x.length := by
    simp only [u, pairWords_length]; omega
  have hTV : T ≤ powerBound cV kV (2 * x.length + 1 + clockLength c k x.length) :=
    Nat.le_trans hT (powerBound_mono cV kV hu)
  obtain ⟨T₂, r', hT₂, hS2⟩ := checker_runs V g x (set R 0 g) (by simp) (by simp [hR.2.1])
    (by
      intro j hj
      have hj0 : j ≠ 0 := fun h => by subst h; simp at hj
      simp [StackMachine.set, hj0, hR.2.2 j hj])
    T d tape hVu
  have hT₂' : T₂ ≤ guesserCheckBound c k cV kV x.length := by
    unfold guesserCheckBound checkTime at *
    rw [hg] at hT₂
    omega
  have hroom : StackSimulation.Room (set R 0 g) T₂ (guesserCapacity c k cV kV x.length) := by
    intro j
    unfold guesserCapacity
    by_cases hj0 : j = 0
    · subst j; simp [hg]; omega
    by_cases hj1 : j = 1
    · subst j; simp [hR.2.1]; omega
    have hj : 2 ≤ j.val := by
      have h0 : j.val ≠ 0 := fun h => hj0 (Fin.ext h)
      have h1 : j.val ≠ 1 := fun h => hj1 (Fin.ext h)
      omega
    simp [StackMachine.set, hj0, hR.2.2 j hj]
    omega
  obtain ⟨time, res, htime, hrun, hpost⟩ := StackSimulation.controller_simulates
    (checkerMachine V) T₂ ⟨(checkerMachine V).start, set R 0 g⟩ (d, r') hS2
    (guesserCapacity c k cV kV x.length) hroom t ht
  refine ⟨time, res, ?_, hrun, ?_⟩
  · refine Nat.le_trans htime ?_
    exact Nat.mul_le_mul_right _ hT₂'
  · rw [hpost.1]
    constructor
    · intro hd
      subst hd
      exact ⟨T, tape, hVu⟩
    · rintro ⟨T', tape', hacc⟩
      exact (Prod.mk.inj (run_deterministic V (initial V u) hVu hacc)).1

/-! ## Assembly -/

theorem guesser_run_checker (V : Machine) (c k : Nat) (cs : List Bool) (t : Tape) :
    (guesser V c k).run cs
      (seqRight (lift (clockTape c k)) (seq guessMachine (lift (checkerTape V)))
        (seqRight guessMachine (lift (checkerTape V)) (lift (checkerTape V)).start)) t =
      Complexity.run (checkerTape V) cs.length ⟨(checkerTape V).start, t⟩ :=
  (run_seqRight _ _ _ _ _).trans ((run_seqRight _ _ _ _ _).trans (lift_run _ _ _ _))

theorem guesser_spec (V : Machine) (c k cV kV : Nat)
    (hV : ∀ u : Word, ∃ time decision tape, time ≤ powerBound cV kV u.length ∧
      runInput V time u = some (decision, tape))
    (x : Word) :
    (∀ cs : List Bool, guesserBound V c k cV kV x.length ≤ cs.length →
      (guesser V c k).run cs (guesser V c k).start (Tape.ofInput x) ≠ none) ∧
    ((∃ cs tape, (guesser V c k).run cs (guesser V c k).start (Tape.ofInput x) =
        some (true, tape)) ↔
      ∃ w : Word, w.length ≤ powerBound c k x.length ∧ Accepts V (pairWords x w)) := by
  obtain ⟨off, hoff, R, hR, hphase⟩ := guesser_phases V c k x
  let pre := off + (2 * clockLength c k x.length + 2)
  have hshort : ∀ cs : List Bool, cs.length ≤ pre →
      (guesser V c k).run cs (guesser V c k).start (Tape.ofInput x) = none := by
    intro cs hcs
    apply run_phase_short (n := pre) _ cs hcs
    intro cs' hcs'
    obtain ⟨q', t', hs, _⟩ := hphase cs' hcs'
    exact ⟨q', t', hs⟩
  -- every long run is a run of the checker phase
  have hlong : ∀ cs : List Bool, pre ≤ cs.length →
      ∃ time res, time ≤ guesserTail V c k cV kV x.length ∧
        (res.1 = true ↔
          Accepts V (pairWords x (decodeW ((cs.drop off).take (clockLength c k x.length))))) ∧
        ∃ t', Complexity.run (checkerTape V) time ⟨(checkerTape V).start, t'⟩ = some res ∧
          (guesser V c k).run cs (guesser V c k).start (Tape.ofInput x) =
            Complexity.run (checkerTape V) (cs.length - pre) ⟨(checkerTape V).start, t'⟩ := by
    intro cs hcs
    obtain ⟨q', t', ⟨hq', heq⟩, hrun⟩ := run_phase_long (n := pre)
      (P := fun (cs : List Bool) (q' : Fin ((guesser V c k).states + 1)) (t' : Tape) =>
        q' = seqRight (lift (clockTape c k))
          (seq guessMachine (lift (checkerTape V)))
            (seqRight guessMachine (lift (checkerTape V)) (lift (checkerTape V)).start) ∧
          (StackEncoding.homeTape
            (set R 0 ((cs.drop off).take (clockLength c k x.length)))).Equivalent t')
      (fun cs' hcs' => by
        obtain ⟨q', t', hs, hq, he⟩ := hphase cs' hcs'
        exact ⟨q', t', hs, hq, he⟩) cs hcs
    have hgtake : ((cs.take pre).drop off).take (clockLength c k x.length) =
        (cs.drop off).take (clockLength c k x.length) := by
      rw [List.drop_take, List.take_take]; congr 1; omega
    rw [hgtake] at heq
    have hglen : ((cs.drop off).take (clockLength c k x.length)).length =
        clockLength c k x.length := by simp; omega
    obtain ⟨time, res, htime, hres, hacc⟩ :=
      checker_phase V c k cV kV hV x ((cs.drop off).take (clockLength c k x.length)) R hR hglen
        t' heq
    refine ⟨time, res, htime, hacc, t', hres, ?_⟩
    rw [hrun, hq', guesser_run_checker, List.length_drop]
  have hbound :
      pre + guesserTail V c k cV kV x.length ≤ guesserBound V c k cV kV x.length := by
    unfold guesserBound
    omega
  have hm : clockLength c k x.length = 2 * powerBound c k x.length := by
    simp only [clockLength, powerBound_eq, Nat.mul_assoc]
  refine ⟨?_, ?_⟩
  · intro cs hcs
    obtain ⟨time, res, htime, _, t', hres, hrun⟩ := hlong cs (by omega)
    rw [hrun, run_mono (checkerTape V) (by omega) _ res hres]
    simp
  · constructor
    · rintro ⟨cs, tape, hrun⟩
      by_cases hcs : pre ≤ cs.length
      · obtain ⟨time, res, htime, hacc, t', hres, hrun'⟩ := hlong cs hcs
        rw [hrun'] at hrun
        have hdet := run_deterministic (checkerTape V) _ hres hrun
        have hres1 : res.1 = true := by rw [hdet]
        refine ⟨decodeW ((cs.drop off).take (clockLength c k x.length)), ?_, hacc.mp hres1⟩
        have := decodeW_length ((cs.drop off).take (clockLength c k x.length))
        have hlen : ((cs.drop off).take (clockLength c k x.length)).length ≤
            clockLength c k x.length := List.length_take_le _ _
        omega
      · rw [hshort cs (by omega)] at hrun
        cases hrun
    · rintro ⟨w, hw, hacc⟩
      obtain ⟨g, hglen, hgw⟩ := exists_guess w (powerBound c k x.length) hw
      let cs := List.replicate off false ++
        (g ++ List.replicate (clockLength c k x.length + 2 + guesserTail V c k cV kV x.length)
          false)
      have hcslen : cs.length = pre + guesserTail V c k cV kV x.length := by
        simp [cs, pre, hglen, hm]; omega
      obtain ⟨time, res, htime, hacc', t', hres, hrun⟩ := hlong cs (by omega)
      have hg : (cs.drop off).take (clockLength c k x.length) = g := by
        simp [cs, hm, ← hglen]
      rw [hg, hgw] at hacc'
      refine ⟨cs, res.2, ?_⟩
      rw [hrun, run_mono (checkerTape V) (by omega) _ res hres]
      have h1 : res.1 = true := hacc'.mpr hacc
      rw [← h1]

/-- NP (certificate form) is contained in nondeterministic polynomial time. -/
theorem nondeterministicPolyTime_of_inNP {L : Language} (h : InNP L) :
    NondeterministicPolyTime L := by
  obtain ⟨V, c, k, ⟨cV, kV, hV⟩, hL⟩ := h
  obtain ⟨c', k', hbound⟩ := polynomialBound_guesserBound V c k cV kV
  refine ⟨guesser V c k, c', k', fun x => ⟨?_, ?_⟩⟩
  · intro choices hlen
    exact (guesser_spec V c k cV kV hV x).1 choices (by rw [hlen]; exact hbound x.length)
  · rw [hL x]
    exact (guesser_spec V c k cV kV hV x).2.symm

end Complexity.NTM
