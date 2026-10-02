module

public import Complexity.NTM.Basic
public import Complexity.TapeToStacks
import Lean.Elab.Tactic.Omega

/-!
# Simulating a nondeterministic machine on Boolean stacks

A finite stack program simulating an `NMachine` along the choices stored in a register.
As in `TapeToStacks`, the scanned symbol is kept in finite control and the two halves of
the tape are stored, two bits per symbol, in two registers. Before every simulated
instruction one choice is popped from the choice register; an empty register supplies the
choice `false`, exactly as `runD` does. The program halts with the simulated decision.

The registers are parameters, so the program can be embedded in larger programs.
-/

@[expose] public section

namespace Complexity.NTM

open StackProgram
open StackMachine (Registers set branch)
open TapeToStacks (high low pairSymbol symbols symbolEncoding readCost pairSymbol_bits)

/-! ## Expanding raw bits into symbol pairs -/

/-- Pop the bits of `src` and push their symbol encodings onto `dst`, three instructions
per bit. -/
def expand {k : Nat} (src dst : Fin (k + 1)) : Program k (Fin 6) where
  start := 0
  code q := if q = 0 then .pop src 1 2 4
    else if q = 1 then .halt true
    else if q = 2 then .push dst true 3
    else if q = 3 then .push dst false 0
    else if q = 4 then .push dst false 5
    else .push dst true 0

theorem exec_expand {k : Nat} (src dst : Fin (k + 1)) (hne : src ≠ dst) (xs : List Bool)
    (r : Registers k) (hr : r src = xs) :
    Exec (expand src dst) 0 r (3 * xs.length + 2)
      (true, set (set r src []) dst (symbols (xs.reverse.map Symbol.bit) ++ r dst)) := by
  induction xs generalizing r with
  | nil =>
    have heq : set (set r src []) dst (symbols (([] : List Bool).reverse.map Symbol.bit) ++ r dst) =
        set r src [] := by
      funext j
      by_cases hj : j = dst
      · subst j; simp [Ne.symm hne, symbols]
      · simp [StackMachine.set, hj]
    rw [heq]
    exact .next (q' := 1) (r' := set r src [])
      (by simp [StackProgram.step, expand, hr, branch])
      (.halt (by simp [StackProgram.step, expand]))
  | cons b xs ih =>
    let r' := set (set r src xs) dst (high (.bit b) :: low (.bit b) :: r dst)
    have h := ih r' (by simp [r', hne])
    have hpop : StackProgram.step (expand src dst) 0 r =
        .inr ((if b then 4 else 2), set r src xs) := by
      cases b <;> simp [StackProgram.step, expand, hr, branch]
    have hlow : StackProgram.step (expand src dst) (if b then 4 else 2) (set r src xs) =
        .inr ((if b then 5 else 3), set (set r src xs) dst (low (.bit b) :: r dst)) := by
      cases b <;> simp [StackProgram.step, expand, low, Ne.symm hne]
    have hhigh : StackProgram.step (expand src dst) (if b then 5 else 3)
        (set (set r src xs) dst (low (.bit b) :: r dst)) = .inr (0, r') := by
      cases b <;> simp [StackProgram.step, expand, high, r', StackWords.set_overwrite]
    have hh := Exec.next hpop (Exec.next hlow (Exec.next hhigh h))
    have hout : set (set r' src []) dst (symbols (xs.reverse.map Symbol.bit) ++ r' dst) =
        set (set r src []) dst (symbols ((b :: xs).reverse.map Symbol.bit) ++ r dst) := by
      funext j
      by_cases hj : j = dst
      · subst j
        simp [r', symbols, List.reverse_cons, List.map_append, TapeToStacks.symbols_append]
      · by_cases hs : j = src
        · subst j; simp [hj]
        · simp [r', StackMachine.set, hj, hs]
    rw [hout] at hh
    have htime : 3 * xs.length + 2 + 1 + 1 + 1 = 3 * (b :: xs).length + 2 := by
      simp only [List.length_cons]; omega
    rw [htime] at hh
    exact hh

/-! ## The simulation program -/

inductive Label (M : NMachine) where
  | read (q : Fin (M.states + 1)) (fromLeft : Bool)
  | readLow (q : Fin (M.states + 1)) (fromLeft first : Bool)
  | choose (q : Fin (M.states + 1)) (head : Symbol)
  | exec (c : Bool) (q : Fin (M.states + 1)) (head : Symbol)
  | writeHigh (q : Fin (M.states + 1)) (goLeft first : Bool)

abbrev LabelSum (M : NMachine) :=
  Sum (Fin (M.states + 1) × Bool)
    (Sum (Fin (M.states + 1) × (Bool × Bool))
      (Sum (Fin (M.states + 1) × Symbol)
        (Sum (Bool × (Fin (M.states + 1) × Symbol))
          (Fin (M.states + 1) × (Bool × Bool)))))

def Label.toSum {M : NMachine} : Label M → LabelSum M
  | .read q b => .inl (q, b)
  | .readLow q b c => .inr (.inl (q, b, c))
  | .choose q a => .inr (.inr (.inl (q, a)))
  | .exec c q a => .inr (.inr (.inr (.inl (c, q, a))))
  | .writeHigh q b c => .inr (.inr (.inr (.inr (q, b, c))))

def Label.ofSum {M : NMachine} : LabelSum M → Label M
  | .inl (q, b) => .read q b
  | .inr (.inl (q, b, c)) => .readLow q b c
  | .inr (.inr (.inl (q, a))) => .choose q a
  | .inr (.inr (.inr (.inl (c, q, a)))) => .exec c q a
  | .inr (.inr (.inr (.inr (q, b, c)))) => .writeHigh q b c

@[simp] theorem Label.ofSum_toSum {M : NMachine} (q : Label M) :
    Label.ofSum q.toSum = q := by cases q <;> rfl

def labelSumEncoding (M : NMachine) : Encoding (LabelSum M) :=
  let q := Encoding.fin M.states
  let bb := Encoding.bool.prod Encoding.bool
  (q.prod Encoding.bool).sum ((q.prod bb).sum ((q.prod symbolEncoding).sum
    ((Encoding.bool.prod (q.prod symbolEncoding)).sum (q.prod bb))))

def labelEncoding (M : NMachine) : Encoding (Label M) where
  states := (labelSumEncoding M).states
  encode q := (labelSumEncoding M).encode q.toSum
  decode q := Label.ofSum ((labelSumEncoding M).decode q)
  decode_encode q := by simp [(labelSumEncoding M).decode_encode]

/-- The register holding the tape half on the given side (`true` is the left half). -/
def sideRegister {k : Nat} (lt rt : Fin (k + 1)) (side : Bool) : Fin (k + 1) :=
  if side then lt else rt

/-- Simulate `M` with the choices in register `ch`, the left half of the tape in `lt` and
the right half (after the scanned cell) in `rt`. -/
def core (M : NMachine) {k : Nat} (ch lt rt : Fin (k + 1)) : Program k (Label M) where
  start := .read M.start false
  code label := match label with
    | .read q side =>
      .pop (sideRegister lt rt side) (.choose q .blank)
        (.readLow q side false) (.readLow q side true)
    | .readLow q side first =>
      .pop (sideRegister lt rt side) (.choose q (pairSymbol first false))
        (.choose q (pairSymbol first false)) (.choose q (pairSymbol first true))
    | .choose q a => .pop ch (.exec false q a) (.exec false q a) (.exec true q a)
    | .exec c q a => match M.code c q a with
      | .halt b => .halt b
      | .step a' .stay q' => .goto (.choose q' a')
      | .step a' .left q' => .push rt (low a') (.writeHigh q' true (high a'))
      | .step a' .right q' => .push lt (low a') (.writeHigh q' false (high a'))
    | .writeHigh q side first => .push (sideRegister lt rt (!side)) first (.read q side)

theorem exec_read (M : NMachine) {k : Nat} (ch lt rt : Fin (k + 1))
    (q : Fin (M.states + 1)) (side : Bool) (xs : List Symbol) (r : Registers k)
    (hr : r (sideRegister lt rt side) = symbols xs) (time : Nat) (result : Bool × Registers k)
    (h : Exec (core M ch lt rt) (.choose q (xs.headD .blank))
      (set r (sideRegister lt rt side) (symbols (xs.drop 1))) time result) :
    Exec (core M ch lt rt) (.read q side) r (time + readCost xs) result := by
  cases xs with
  | nil =>
    exact .next (by simp [StackProgram.step, core, hr, branch, symbols]) h
  | cons a rest =>
    have hs : StackProgram.step (core M ch lt rt) (.read q side) r =
        .inr (.readLow q side (high a),
          set r (sideRegister lt rt side) (low a :: symbols rest)) := by
      cases hhigh : high a <;> simp [StackProgram.step, core, symbols, branch, hr, hhigh]
    have ht : StackProgram.step (core M ch lt rt) (.readLow q side (high a))
        (set r (sideRegister lt rt side) (low a :: symbols rest)) =
        .inr (.choose q a, set r (sideRegister lt rt side) (symbols rest)) := by
      have hp := pairSymbol_bits a
      cases hlow : low a <;> simp_all [StackProgram.step, core, branch]
    exact .next hs (.next ht (by simpa [readCost] using h))

theorem branch_headD {α : Type} (cs : List Bool) (f : Bool → α) :
    branch cs (f false) (f false) (f true) = f (cs.headD false) := by
  cases cs with
  | nil => rfl
  | cons c cs => cases c <;> rfl

/-- Each simulated instruction costs at most five stack instructions. -/
theorem core_simulates (M : NMachine) {k : Nat} (ch lt rt : Fin (k + 1))
    (hcl : ch ≠ lt) (hcr : ch ≠ rt) (hlr : lt ≠ rt)
    (fuel : Nat) (cs : List Bool) (q : Fin (M.states + 1)) (t : Tape) (b : Bool) (out : Tape)
    (hrun : runD M fuel cs q t = some (b, out)) (r : Registers k)
    (hch : r ch = cs) (hlt : r lt = symbols t.left) (hrt : r rt = symbols (t.right.drop 1)) :
    ∃ time r', time ≤ 5 * fuel ∧
      Exec (core M ch lt rt) (.choose q t.read) r time (b, r') := by
  induction fuel generalizing cs q t r with
  | zero => simp [runD] at hrun
  | succ fuel ih =>
    obtain ⟨c, hcd⟩ : ∃ c, cs.headD false = c := ⟨_, rfl⟩
    have hrun' : (match M.code c q t.read with
        | .halt b => some (b, t)
        | .step a d q' => runD M fuel cs.tail q' ((t.write a).move d)) = some (b, out) := by
      rw [← hcd]; exact hrun
    let r₁ := set r ch cs.tail
    have hchoose : StackProgram.step (core M ch lt rt) (.choose q t.read) r =
        .inr (.exec c q t.read, r₁) := by
      simp only [StackProgram.step, core, hch, r₁]
      rw [branch_headD cs (fun c => Label.exec c q t.read), hcd]
    have hlt₁ : r₁ lt = symbols t.left := by simp [r₁, Ne.symm hcl, hlt]
    have hrt₁ : r₁ rt = symbols (t.right.drop 1) := by simp [r₁, Ne.symm hcr, hrt]
    have hch₁ : r₁ ch = cs.tail := by simp [r₁]
    cases hc : M.code c q t.read with
    | halt b' =>
      have heq : (b', t) = (b, out) := by simpa [hc] using hrun'
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
      refine ⟨2, r₁, by omega, .next hchoose (.halt ?_)⟩
      simp [StackProgram.step, core, hc]
    | step a d q' =>
      have hnext : runD M fuel cs.tail q' ((t.write a).move d) = some (b, out) := by
        simpa [hc] using hrun'
      cases d with
      | stay =>
        obtain ⟨time, r', ht, he⟩ := ih cs.tail q' ((t.write a).move .stay) hnext r₁ hch₁
          (by simpa [Tape.move, Tape.write] using hlt₁)
          (by simpa [Tape.move, Tape.write] using hrt₁)
        have he' : Exec (core M ch lt rt) (.choose q' a) r₁ time (b, r') := by
          simpa [Tape.move, Tape.write, Tape.read] using he
        refine ⟨time + 1 + 1, r', by omega, .next hchoose (.next ?_ he')⟩
        simp [StackProgram.step, core, hc]
      | right =>
        let r₂ := set r₁ lt (low a :: r₁ lt)
        let r₃ := set r₂ lt (high a :: r₂ lt)
        have hlt₃ : r₃ lt = symbols (a :: t.left) := by simp [r₃, r₂, hlt₁, symbols]
        have hrt₃ : r₃ (sideRegister lt rt false) = symbols (t.right.drop 1) := by
          simp [r₃, r₂, sideRegister, Ne.symm hlr, hrt₁]
        have htape : (t.write a).move .right = ⟨a :: t.left, t.right.drop 1⟩ := by
          rw [Tape.move_right_eq]; simp [Tape.write]
        rw [htape] at hnext
        obtain ⟨time, r', ht, he⟩ := ih cs.tail q' ⟨a :: t.left, t.right.drop 1⟩ hnext
          (set r₃ (sideRegister lt rt false) (symbols ((t.right.drop 1).drop 1)))
          (by simp [r₃, r₂, sideRegister, hcl, hcr, hch₁])
          (by simp [sideRegister, hlr, hlt₃])
          (by simp [sideRegister])
        have hread := exec_read M ch lt rt q' false (t.right.drop 1) r₃ hrt₃ time (b, r')
          (by simpa [Tape.read] using he)
        have hcost := TapeToStacks.readCost_le (t.right.drop 1)
        refine ⟨time + readCost (t.right.drop 1) + 1 + 1 + 1, r', by omega,
          .next hchoose (.next (q' := .writeHigh q' false (high a)) (r' := r₂) ?_
            (.next (q' := .read q' false) (r' := r₃) ?_ hread))⟩
        · simp [StackProgram.step, core, hc, r₂]
        · simp [StackProgram.step, core, sideRegister, r₃, r₂]
      | left =>
        let r₂ := set r₁ rt (low a :: r₁ rt)
        let r₃ := set r₂ rt (high a :: r₂ rt)
        have hrt₃ : r₃ rt = symbols (a :: t.right.drop 1) := by
          simp [r₃, r₂, hrt₁, symbols]
        have hlt₃ : r₃ (sideRegister lt rt true) = symbols t.left := by
          simp [r₃, r₂, sideRegister, hlr, hlt₁]
        have htape : (t.write a).move .left =
            ⟨t.left.drop 1, t.left.headD .blank :: a :: t.right.drop 1⟩ := by
          rw [Tape.move_left_eq]; simp [Tape.write]
        rw [htape] at hnext
        obtain ⟨time, r', ht, he⟩ := ih cs.tail q'
          ⟨t.left.drop 1, t.left.headD .blank :: a :: t.right.drop 1⟩ hnext
          (set r₃ (sideRegister lt rt true) (symbols (t.left.drop 1)))
          (by simp [r₃, r₂, sideRegister, hcl, hcr, hch₁])
          (by simp [sideRegister])
          (by simp [sideRegister, Ne.symm hlr, hrt₃])
        have hread := exec_read M ch lt rt q' true t.left r₃ hlt₃ time (b, r')
          (by simpa [Tape.read] using he)
        have hcost := TapeToStacks.readCost_le t.left
        refine ⟨time + readCost t.left + 1 + 1 + 1, r', by omega,
          .next hchoose (.next (q' := .writeHigh q' true (high a)) (r' := r₂) ?_
            (.next (q' := .read q' true) (r' := r₃) ?_ hread))⟩
        · simp [StackProgram.step, core, hc, r₂]
        · simp [StackProgram.step, core, sideRegister, r₃, r₂]

/-- The simulation from the start of the program on an input tape. -/
theorem core_runs (M : NMachine) {k : Nat} (ch lt rt : Fin (k + 1))
    (hcl : ch ≠ lt) (hcr : ch ≠ rt) (hlr : lt ≠ rt)
    (fuel : Nat) (cs : List Bool) (input : List Bool) (b : Bool) (out : Tape)
    (hrun : runD M fuel cs M.start (Tape.ofInput input) = some (b, out)) (r : Registers k)
    (hch : r ch = cs) (hlt : r lt = []) (hrt : r rt = symbols (input.map Symbol.bit)) :
    ∃ time r', time ≤ 5 * fuel + 2 ∧
      Exec (core M ch lt rt) (core M ch lt rt).start r time (b, r') := by
  obtain ⟨time, r', ht, he⟩ := core_simulates M ch lt rt hcl hcr hlr fuel cs M.start
    (Tape.ofInput input) b out hrun
    (set r (sideRegister lt rt false) (symbols ((input.map Symbol.bit).drop 1)))
    (by simp [sideRegister, hcr, hch])
    (by simp [sideRegister, hlr, hlt, Tape.ofInput, symbols])
    (by simp [sideRegister, Tape.ofInput])
  have hread := exec_read M ch lt rt M.start false (input.map Symbol.bit) r
    (by simpa [sideRegister] using hrt) time (b, r')
    (by simpa [Tape.ofInput, Tape.read] using he)
  have hcost := TapeToStacks.readCost_le (input.map Symbol.bit)
  exact ⟨time + readCost (input.map Symbol.bit), r', by omega, hread⟩

end Complexity.NTM
