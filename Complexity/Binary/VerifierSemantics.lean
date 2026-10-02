module

public import Complexity.Binary.VerifierCheck
import Lean.Elab.Tactic.Omega

/-!
# Correctness of the binary SAT verifier's register semantics

* `parseStep_eq`: the first phase succeeds exactly when the input is a binary-indexed
  formula, the certificate has a bit for every occurrence, and every clause has an
  occurrence agreeing with its sign; it then leaves the entries of all occurrences.
* `check_isSome`: the second phase succeeds exactly when the entries are consistent.
-/

@[expose] public section

namespace Complexity.Binary.Verify

open Complexity.StackMachine (Registers set)
open Complexity.SAT
open Complexity.Binary

/-- An occurrence whose certificate bit agrees with its sign. -/
def agrees (p : BinaryLiteral × Bool) : Bool := p.2 == p.1.positive

theorem countP_agrees_eq_zero (lc : List (BinaryLiteral × Bool)) :
    lc.countP agrees = 0 ↔ clauseOK lc = false := by
  simp [clauseOK, agrees]

/-! ## Literals -/

def litsOut (r : Registers 17) (lc : List (BinaryLiteral × Bool)) (rest w : Word) :
    Registers 17 :=
  set (set (set (set (set (set r inner []) input rest) cert w) entries
    (writeEntries ((lc.map entry).reverse) ++ r entries)) count
    (List.replicate lc.length true ++ r count)) flag
    (List.replicate (lc.countP agrees) true ++ r flag)

theorem literals_success (m : Nat) (r : Registers 17) (c : List BinaryLiteral) (rest : Word)
    (lc : List (BinaryLiteral × Bool)) (w : Word) (hr : r inner = List.replicate m true)
    (hp : readMany readBinaryLiteral m (r input) = some (c, rest))
    (hl : labelClause c (r cert) = some (lc, w)) :
    iterStep inner litStep m r = some (litsOut r lc rest w) := by
  induction m generalizing r c rest lc w with
  | zero =>
    have hc : c = [] ∧ rest = r input := by
      simpa [readMany, Prod.mk.injEq, eq_comm] using hp
    obtain ⟨rfl, rfl⟩ := hc
    have hlw : lc = [] ∧ w = r cert := by
      simpa [labelClause, Prod.mk.injEq, eq_comm] using hl
    obtain ⟨rfl, rfl⟩ := hlw
    have hz : r inner = [] := by simpa using hr
    simp only [iterStep_zero, Option.some.injEq]
    apply regs_ext <;> simp [litsOut, hz, writeEntries]
  | succ m ih =>
    cases hb : readBinaryLiteral (r input) with
    | none => simp [readMany, hb] at hp
    | some pair =>
      obtain ⟨l, tail⟩ := pair
      cases hm : readMany readBinaryLiteral m tail with
      | none => simp [readMany, hb, hm] at hp
      | some result =>
        obtain ⟨cs, final⟩ := result
        have hc : c = l :: cs ∧ rest = final := by
          simpa [readMany, hb, hm, Prod.mk.injEq, eq_comm] using hp
        obtain ⟨rfl, rfl⟩ := hc
        cases hw : r cert with
        | nil => simp [labelClause, hw] at hl
        | cons b w₀ =>
          cases hlc : labelClause cs w₀ with
          | none => simp [labelClause, hw, hlc] at hl
          | some pair =>
            obtain ⟨lc', w'⟩ := pair
            have hlw : lc = (l, b) :: lc' ∧ w = w' := by
              simpa [labelClause, hw, hlc, Prod.mk.injEq, eq_comm] using hl
            obtain ⟨rfl, rfl⟩ := hlw
            let r' := litFinish (set r inner (List.replicate m true)) l b tail w₀
            have hstep : litStep (set r inner (List.replicate m true)) = some r' := by
              have hb' : readBinaryLiteral ((set r inner (List.replicate m true)) input) =
                  some (l, tail) := by simpa using hb
              have hw' : (set r inner (List.replicate m true)) cert = b :: w₀ := by
                simpa using hw
              simp only [litStep, hb', hw', r']
            have h' := ih r' cs rest lc' w (by simp [r', litFinish])
              (by simpa [r', litFinish] using hm) (by simpa [r', litFinish] using hlc)
            rw [iterStep_succ, hstep, Option.bind_some, h']
            congr 1
            have hflag : List.replicate (lc'.countP agrees) true ++
                (if b == l.positive then true :: r flag else r flag) =
                List.replicate (((l, b) :: lc').countP agrees) true ++ r flag := by
              rw [List.countP_cons]
              cases hbl : b == l.positive
              · simp [agrees, hbl]
              · simp [agrees, hbl, List.replicate_succ', List.append_assoc]
            apply regs_ext <;>
              simp [litsOut, r', litFinish, writeEntries_append, writeEntries, entry,
                List.replicate_succ', List.append_assoc]
            simpa [agrees] using hflag

theorem literals_failure (m : Nat) (r : Registers 17)
    (hfail : ∀ c rest, readMany readBinaryLiteral m (r input) = some (c, rest) →
      labelClause c (r cert) = none) :
    iterStep inner litStep m r = none := by
  induction m generalizing r with
  | zero =>
    have h := hfail [] (r input) (by simp [readMany])
    simp [labelClause] at h
  | succ m ih =>
    cases hb : readBinaryLiteral (r input) with
    | none =>
      have hb' : readBinaryLiteral ((set r inner (List.replicate m true)) input) = none := by
        simpa using hb
      have hstep : litStep (set r inner (List.replicate m true)) = none := by
        unfold litStep; rw [hb']
      rw [iterStep_succ, hstep]
      rfl
    | some pair =>
      obtain ⟨l, tail⟩ := pair
      cases hw : r cert with
      | nil =>
        have hb' : readBinaryLiteral ((set r inner (List.replicate m true)) input) =
            some (l, tail) := by simpa using hb
        have hw' : (set r inner (List.replicate m true)) cert = [] := by simpa using hw
        have hstep : litStep (set r inner (List.replicate m true)) = none := by
          unfold litStep; rw [hb', hw']
        rw [iterStep_succ, hstep]
        rfl
      | cons b w₀ =>
        let r' := litFinish (set r inner (List.replicate m true)) l b tail w₀
        have hstep : litStep (set r inner (List.replicate m true)) = some r' := by
          have hb' : readBinaryLiteral ((set r inner (List.replicate m true)) input) =
              some (l, tail) := by simpa using hb
          have hw' : (set r inner (List.replicate m true)) cert = b :: w₀ := by simpa using hw
          simp only [litStep, hb', hw', r']
        rw [iterStep_succ, hstep, Option.bind_some]
        apply ih r'
        intro cs rest hm
        have hm' : readMany readBinaryLiteral m tail = some (cs, rest) := by
          simpa [r', litFinish] using hm
        have h := hfail (l :: cs) rest (by simp [readMany, hb, hm'])
        have hcert : r' cert = w₀ := by simp [r', litFinish]
        rw [hcert]
        cases hlc : labelClause cs w₀ with
        | none => rfl
        | some pair => simp [labelClause, hw, hlc] at h

/-! ## Clauses -/

def clauseOut (r : Registers 17) (lc : List (BinaryLiteral × Bool)) (rest w : Word) :
    Registers 17 :=
  set (set (set (set (set r inner []) input rest) cert w) entries
    (writeEntries ((lc.map entry).reverse) ++ r entries)) count
    (List.replicate lc.length true ++ r count)

theorem clauseStep_success (r : Registers 17) (hf : r flag = []) (c : List BinaryLiteral)
    (rest : Word) (lc : List (BinaryLiteral × Bool)) (w : Word)
    (hp : readBinaryClause (r input) = some (c, rest))
    (hl : labelClause c (r cert) = some (lc, w)) (hok : clauseOK lc = true) :
    clauseStep r = some (clauseOut r lc rest w) := by
  cases hn : readNat (r input) with
  | none => simp [readBinaryClause, readList, hn] at hp
  | some pair =>
    obtain ⟨m, t⟩ := pair
    have hm : readMany readBinaryLiteral m t = some (c, rest) := by
      simpa [readBinaryClause, readList, hn] using hp
    have h := literals_success m (set (set r input t) inner (List.replicate m true)) c rest lc w
      (by simp) (by simpa using hm) (by simpa using hl)
    have hne : (lc.countP agrees) ≠ 0 := by
      intro h0
      rw [countP_agrees_eq_zero] at h0
      simp [h0] at hok
    have hflag : ((litsOut (set (set r input t) inner (List.replicate m true)) lc rest w)
        flag).isEmpty = false := by
      cases hcnt : lc.countP agrees with
      | zero => exact absurd hcnt hne
      | succ k => simp [litsOut, hcnt, List.replicate_succ]
    simp only [clauseStep, hn, h, hflag, Bool.false_eq_true, ite_false, Option.some.injEq]
    apply regs_ext <;> simp [litsOut, clauseOut, hf]

theorem clauseStep_failure (r : Registers 17) (hf : r flag = [])
    (hfail : ∀ c rest, readBinaryClause (r input) = some (c, rest) →
      ∀ lc w, labelClause c (r cert) = some (lc, w) → clauseOK lc = false) :
    clauseStep r = none := by
  cases hn : readNat (r input) with
  | none => simp [clauseStep, hn]
  | some pair =>
    obtain ⟨m, t⟩ := pair
    let r₁ := set (set r input t) inner (List.replicate m true)
    have hiter : iterStep inner litStep m r₁ = none ∨
        ∃ q, iterStep inner litStep m r₁ = some q ∧ (q flag).isEmpty := by
      cases hm : readMany readBinaryLiteral m t with
      | none =>
        left
        apply literals_failure
        intro c rest h
        simp [r₁, hm] at h
      | some result =>
        obtain ⟨c, rest⟩ := result
        have hp : readBinaryClause (r input) = some (c, rest) := by
          simp [readBinaryClause, readList, hn, hm]
        cases hl : labelClause c (r cert) with
        | none =>
          left
          apply literals_failure
          intro c' rest' h
          have : c' = c := by
            simp [r₁, hm] at h
            exact h.1.symm
          subst this
          simpa [r₁] using hl
        | some pair =>
          obtain ⟨lc, w⟩ := pair
          right
          have hok := hfail c rest hp lc w hl
          have h := literals_success m r₁ c rest lc w (by simp [r₁]) (by simpa [r₁] using hm)
            (by simpa [r₁] using hl)
          refine ⟨_, h, ?_⟩
          have h0 := (countP_agrees_eq_zero lc).mpr hok
          simp [litsOut, h0, r₁, hf]
    have hiter' : iterStep inner litStep m (set (set r input t) inner
        (List.replicate m true)) = iterStep inner litStep m r₁ := rfl
    rcases hiter with h | ⟨q, h, he⟩
    · simp [clauseStep, hn, hiter', h]
    · simp [clauseStep, hn, hiter', h, he]

/-! ## The formula -/

def clausesOut (r : Registers 17) (g : List (List (BinaryLiteral × Bool))) (rest w : Word) :
    Registers 17 :=
  set (set (set (set (set r outer []) input rest) cert w) entries
    (writeEntries ((g.flatten.map entry).reverse) ++ r entries)) count
    (List.replicate g.flatten.length true ++ r count)

theorem clauses_success (n : Nat) (r : Registers 17) (hf : r flag = []) (hi : r inner = [])
    (f : List (List BinaryLiteral)) (rest : Word) (g : List (List (BinaryLiteral × Bool)))
    (w : Word) (hr : r outer = List.replicate n true)
    (hp : readMany readBinaryClause n (r input) = some (f, rest))
    (hl : labelCNF f (r cert) = some (g, w)) (hok : g.all clauseOK = true) :
    iterStep outer clauseStep n r = some (clausesOut r g rest w) := by
  induction n generalizing r f rest g w with
  | zero =>
    have hc : f = [] ∧ rest = r input := by
      simpa [readMany, Prod.mk.injEq, eq_comm] using hp
    obtain ⟨rfl, rfl⟩ := hc
    have hgw : g = [] ∧ w = r cert := by
      simpa [labelCNF, Prod.mk.injEq, eq_comm] using hl
    obtain ⟨rfl, rfl⟩ := hgw
    have hz : r outer = [] := by simpa using hr
    simp only [iterStep_zero, Option.some.injEq]
    apply regs_ext <;> simp [clausesOut, hz, writeEntries]
  | succ n ih =>
    cases hc : readBinaryClause (r input) with
    | none => simp [readMany, hc] at hp
    | some pair =>
      obtain ⟨c, tail⟩ := pair
      cases hm : readMany readBinaryClause n tail with
      | none => simp [readMany, hc, hm] at hp
      | some result =>
        obtain ⟨fs, final⟩ := result
        have heq : f = c :: fs ∧ rest = final := by
          simpa [readMany, hc, hm, Prod.mk.injEq, eq_comm] using hp
        obtain ⟨rfl, rfl⟩ := heq
        cases hlc : labelClause c (r cert) with
        | none => simp [labelCNF, hlc] at hl
        | some pair =>
          obtain ⟨lc, w₁⟩ := pair
          cases hlf : labelCNF fs w₁ with
          | none => simp [labelCNF, hlc, hlf] at hl
          | some pair =>
            obtain ⟨gs, w'⟩ := pair
            have hgw : g = lc :: gs ∧ w = w' := by
              simpa [labelCNF, hlc, hlf, Prod.mk.injEq, eq_comm] using hl
            obtain ⟨rfl, rfl⟩ := hgw
            have hok' : clauseOK lc = true ∧ gs.all clauseOK = true := by
              simpa using hok
            let r₀ := set r outer (List.replicate n true)
            have hstep : clauseStep r₀ = some (clauseOut r₀ lc tail w₁) :=
              clauseStep_success r₀ (by simpa [r₀] using hf) c tail lc w₁
                (by simpa [r₀] using hc) (by simpa [r₀] using hlc) hok'.1
            let r' := clauseOut r₀ lc tail w₁
            have h' := ih r' (by simpa [r', clauseOut, r₀] using hf) (by simp [r', clauseOut])
              fs rest gs w (by simp [r', clauseOut, r₀]) (by simpa [r', clauseOut] using hm)
              (by simpa [r', clauseOut] using hlf) hok'.2
            rw [iterStep_succ, hstep, Option.bind_some, h']
            congr 1
            have hcount : List.replicate gs.flatten.length true ++
                (List.replicate lc.length true ++ r count) =
                List.replicate (lc :: gs).flatten.length true ++ r count := by
              rw [← List.append_assoc, List.replicate_append_replicate]
              simp [Nat.add_comm]
            apply regs_ext <;>
              simp [clausesOut, r', clauseOut, r₀, hi, writeEntries_append, List.append_assoc]
            · simpa [List.append_assoc] using hcount

theorem clauses_failure (n : Nat) (r : Registers 17) (hf : r flag = []) (hi : r inner = [])
    (hfail : ∀ f rest, readMany readBinaryClause n (r input) = some (f, rest) →
      ∀ g w, labelCNF f (r cert) = some (g, w) → g.all clauseOK = false) :
    iterStep outer clauseStep n r = none := by
  induction n generalizing r with
  | zero =>
    have h := hfail [] (r input) (by simp [readMany]) [] (r cert) (by simp [labelCNF])
    simp at h
  | succ n ih =>
    let r₀ := set r outer (List.replicate n true)
    have hf₀ : r₀ flag = [] := by simpa [r₀] using hf
    cases hc : readBinaryClause (r input) with
    | none =>
      have h := clauseStep_failure r₀ hf₀ (by intro c rest h; simp [r₀, hc] at h)
      rw [iterStep_succ]
      change (clauseStep r₀).bind _ = none
      rw [h]
      rfl
    | some pair =>
      obtain ⟨c, tail⟩ := pair
      cases hlc : labelClause c (r cert) with
      | none =>
        have h := clauseStep_failure r₀ hf₀ (by
          intro c' rest' h lc w hl
          have : c' = c := by simp [r₀, hc] at h; exact h.1.symm
          subst this
          simp [r₀, hlc] at hl)
        rw [iterStep_succ]
        change (clauseStep r₀).bind _ = none
        rw [h]
        rfl
      | some pair =>
        obtain ⟨lc, w₁⟩ := pair
        cases hok : clauseOK lc with
        | false =>
          have h := clauseStep_failure r₀ hf₀ (by
            intro c' rest' h lc' w hl
            have : c' = c := by simp [r₀, hc] at h; exact h.1.symm
            subst this
            have : lc' = lc := by simp [r₀, hlc] at hl; exact hl.1.symm
            subst this
            exact hok)
          rw [iterStep_succ]
          change (clauseStep r₀).bind _ = none
          rw [h]
          rfl
        | true =>
          have hstep : clauseStep r₀ = some (clauseOut r₀ lc tail w₁) :=
            clauseStep_success r₀ hf₀ c tail lc w₁ (by simpa [r₀] using hc)
              (by simpa [r₀] using hlc) hok
          rw [iterStep_succ]
          change (clauseStep r₀).bind _ = none
          rw [hstep, Option.bind_some]
          apply ih _ (by simpa [clauseOut, r₀] using hf) (by simp [clauseOut])
          intro fs rest hm gs w hl
          have hm' : readMany readBinaryClause n tail = some (fs, rest) := by
            simpa [clauseOut] using hm
          have hl' : labelCNF fs w₁ = some (gs, w) := by simpa [clauseOut] using hl
          have h := hfail (c :: fs) rest (by simp [readMany, hc, hm']) (lc :: gs) w
            (by simp [labelCNF, hlc, hl'])
          simpa [hok] using h

/-- The first phase, in terms of the decoded formula and the labelled occurrences. -/
theorem parseStep_eq (r : Registers 17) (hf : r flag = []) (hi : r inner = []) :
    parseStep r = match decodeBinary (r input) with
      | none => none
      | some f =>
        match labelCNF f (r cert) with
        | none => none
        | some (g, w) => if g.all clauseOK then some (clausesOut r g [] w) else none := by
  cases hn : readNat (r input) with
  | none =>
    have hd : decodeBinary (r input) = none := by
      simp [decodeBinary, readBinaryCNF, readList, hn]
    simp [parseStep, hn, hd]
  | some pair =>
    obtain ⟨n, t⟩ := pair
    let r₁ := set (set r input t) outer (List.replicate n true)
    have hiter : iterStep outer clauseStep n (set (set r input t) outer
        (List.replicate n true)) = iterStep outer clauseStep n r₁ := rfl
    have hf₁ : r₁ flag = [] := by simpa [r₁] using hf
    have hi₁ : r₁ inner = [] := by simpa [r₁] using hi
    cases hm : readMany readBinaryClause n t with
    | none =>
      have hd : decodeBinary (r input) = none := by
        simp [decodeBinary, readBinaryCNF, readList, hn, hm]
      have h := clauses_failure n r₁ hf₁ hi₁ (by intro f rest h; simp [r₁, hm] at h)
      simp [parseStep, hn, hiter, h, hd]
    | some result =>
      obtain ⟨f, rest⟩ := result
      have hd : decodeBinary (r input) = if rest = [] then some f else none := by
        cases rest <;> simp [decodeBinary, readBinaryCNF, readList, hn, hm]
      have hfailCase : (∀ g w, labelCNF f (r cert) = some (g, w) → g.all clauseOK = false) →
          parseStep r = none := by
        intro hall
        have h := clauses_failure n r₁ hf₁ hi₁ (by
          intro f' rest' h g w hl
          have : f' = f := by simp [r₁, hm] at h; exact h.1.symm
          subst this
          exact hall g w (by simpa [r₁] using hl))
        simp [parseStep, hn, hiter, h]
      cases hl : labelCNF f (r cert) with
      | none =>
        have h := hfailCase (by intro g w h; simp [hl] at h)
        rw [h, hd]
        cases rest <;> simp [hl]
      | some pair =>
        obtain ⟨g, w⟩ := pair
        cases hok : g.all clauseOK with
        | false =>
          have h := hfailCase (by
            intro g' w' h
            have : g' = g := by simp [hl] at h; exact h.1.symm
            subst this
            exact hok)
          rw [h, hd]
          cases rest <;> simp [hl, hok]
        | true =>
          have h := clauses_success n r₁ hf₁ hi₁ f rest g w (by simp [r₁])
            (by simpa [r₁] using hm) (by simpa [r₁] using hl) hok
          rw [hd]
          cases rest with
          | nil =>
            simp only [parseStep, hn, hiter, h, ite_true, hl, hok]
            simp only [clausesOut, StackMachine.set_other _ (by decide : input ≠ entries),
              StackMachine.set_other _ (by decide : input ≠ count),
              StackMachine.set_other _ (by decide : input ≠ cert), StackMachine.set_same,
              List.isEmpty_nil, ite_true, Option.some.injEq]
            apply regs_ext <;> simp [r₁]
          | cons b rest =>
            simp [parseStep, hn, hiter, h, clausesOut]

/-! ## The second phase -/

theorem inner_spec (c : Bool) (ds : List Bool) :
    ∀ (es : List (Bool × List Bool)) (junk : Word) (r : Registers 17),
      r list₂ = writeEntries es ++ junk → r bit = [c] → r digits = ds →
      r count₂ = List.replicate es.length true → r digitsCmp = [] →
      iterStep count₂ innerStep es.length r =
        if es.all (compatible (c, ds)) then some (set (set r list₂ junk) count₂ []) else none
  | [], junk, r, hl, _, _, hn, _ => by
    have hn' : r count₂ = [] := by simpa using hn
    have hl' : r list₂ = junk := by simpa [writeEntries] using hl
    simp only [List.length_nil, iterStep_zero, List.all_nil, ite_true, Option.some.injEq]
    apply regs_ext <;> simp [hn', hl']
  | e :: es, junk, r, hl, hb, hd, hn, hc => by
    let r' := set r count₂ (List.replicate es.length true)
    have hspec : cmpSpec (r' bit) (r' list₂) (r' digits) =
        if e.2 = ds ∧ c ≠ e.1 then none else some (writeEntries es ++ junk) := by
      have h₁ : r' bit = [c] := by simpa [r'] using hb
      have h₂ : r' list₂ = entryCode e ++ (writeEntries es ++ junk) := by
        simpa [r', writeEntries, List.append_assoc] using hl
      have h₃ : r' digits = ds := by simpa [r'] using hd
      rw [h₁, h₂, h₃]
      exact cmpSpec_entry c [] e.1 e.2 _ ds
    rw [List.length_cons, iterStep_succ]
    by_cases hbad : e.2 = ds ∧ c ≠ e.1
    · have hnone : innerStep r' = none := by
        unfold innerStep; rw [hspec]; simp [hbad]
      have hcomp : compatible (c, ds) e = false := by
        simp [compatible, hbad.1, hbad.2]
      rw [hnone, Option.bind_none]
      simp [hcomp]
    · let r'' := set (set r' list₂ (writeEntries es ++ junk)) digitsCmp []
      have hsome : innerStep r' = some r'' := by
        unfold innerStep; rw [hspec]; simp [hbad, r'']
      have hcomp : compatible (c, ds) e = true := by
        unfold compatible
        by_cases h2 : ds = e.2
        · have h3 : c = e.1 := by
            cases hce : decide (c = e.1) with
            | true => simpa using hce
            | false => exact absurd ⟨h2.symm, by simpa using hce⟩ hbad
          simp [h2, h3]
        · simp [h2]
      rw [hsome, Option.bind_some]
      rw [inner_spec c ds es junk r'' (by simp [r'']) (by simpa [r'', r'] using hb)
        (by simpa [r'', r'] using hd) (by simp [r'', r']) (by simp [r''])]
      simp only [List.all_cons, hcomp, Bool.true_and]
      split
      · congr 1
        apply regs_ext <;> simp [r'', r', hc]
      · rfl

theorem outer_spec (es : List (Bool × List Bool)) :
    ∀ (fs : List (Bool × List Bool)) (r : Registers 17),
      r list₁ = writeEntries fs → r count₁ = List.replicate fs.length true →
      r entries = writeEntries es → r count = List.replicate es.length true →
      r digitsRev = [] → r digits = [] → r bit = [] → r digitsCmp = [] → r count₂ = [] →
      (iterStep count₁ outerStep fs.length r).isSome = fs.all (fun e₁ => es.all (compatible e₁))
  | [], r, _, _, _, _, _, _, _, _, _ => by simp [iterStep_zero]
  | (c, ds) :: fs, r, hl₁, hn₁, he, hc, hrev, hd, hb, hcmp, hn₂ => by
    let r' := set r count₁ (List.replicate fs.length true)
    have hread : readEntry (r' list₁) = some ((c, ds), writeEntries fs) := by
      have : r' list₁ = entryCode (c, ds) ++ writeEntries fs := by
        simpa [r', writeEntries] using hl₁
      rw [this, readEntry_entryCode]
    have hcount : (r' count).length = es.length := by simp [r', hc]
    have hinner := inner_spec c ds es [] (outerLoad r' c ds (writeEntries fs))
      (by simp [outerLoad, r', he]) (by simp [outerLoad]) (by simp [outerLoad])
      (by simp [outerLoad, r', hc]) (by simp [outerLoad, r', hcmp])
    rw [List.length_cons, iterStep_succ]
    have hstep : outerStep r' = (iterStep count₂ innerStep es.length
        (outerLoad r' c ds (writeEntries fs))).map (fun q => set (set q digits []) bit []) := by
      simp only [outerStep, hread, hcount]
    rw [hstep, hinner]
    by_cases hall : es.all (compatible (c, ds)) = true
    · simp only [hall, ite_true, Option.map_some, Option.bind_some, List.all_cons,
        Bool.true_and]
      apply outer_spec es fs
      · simp [outerLoad]
      · simp [outerLoad, r']
      · simp [outerLoad, r', he]
      · simp [outerLoad, r', hc]
      · simp [outerLoad, r', hrev]
      · simp
      · simp
      · simp [outerLoad, r', hcmp]
      · simp
    · have hf : es.all (compatible (c, ds)) = false := by
        cases h : es.all (compatible (c, ds)) with
        | false => rfl
        | true => exact absurd h hall
      simp [hf]

/-- The second phase accepts exactly the consistent lists of entries. -/
theorem check_isSome (r : Registers 17) (es : List (Bool × List Bool))
    (he : r entries = writeEntries es) (hc : r count = List.replicate es.length true)
    (hrev : r digitsRev = []) (hd : r digits = []) (hb : r bit = []) (hcmp : r digitsCmp = [])
    (hn₂ : r count₂ = []) :
    (iterStep count₁ outerStep (r count).length (checkLoad r)).isSome = consistent es := by
  have hlen : (r count).length = es.length := by simp [hc]
  rw [hlen]
  exact outer_spec es es (checkLoad r) (by simp [checkLoad, he]) (by simp [checkLoad, hc])
    (by simp [checkLoad, he]) (by simp [checkLoad, hc]) (by simp [checkLoad, hrev])
    (by simp [checkLoad, hd]) (by simp [checkLoad, hb]) (by simp [checkLoad, hcmp])
    (by simp [checkLoad, hn₂])

end Complexity.Binary.Verify
