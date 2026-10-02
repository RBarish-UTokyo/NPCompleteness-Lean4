module

public import Complexity.NTM.Core
public import Complexity.Clock
import Lean.Elab.Tactic.Omega

/-!
# Checking a guessed certificate on Boolean stacks

The nondeterministic machine for a language in NP guesses a word `g` in register 0 (and
keeps the instance `x` in register 1). The certificate is the word `decodeW g`: the bit
pairs `true v` of `g` before the first pair starting with `false`, each giving the bit `v`.
Every certificate of length at most `|g| / 2` arises in this way.

The stack program `checkerProgram V` decodes the certificate `w`, builds the tape contents
`pairWords x w` and simulates the deterministic verifier `V` on it, halting with the
verifier's decision.
-/

@[expose] public section

namespace Complexity.NTM

open StackProgram
open StackMachine (Registers set branch)
open TapeToStacks (symbols)

/-! ## Certificates encoded by bit pairs -/

/-- The certificate encoded by a guessed word. -/
def decodeW : List Bool → List Bool
  | true :: v :: rest => v :: decodeW rest
  | _ => []

/-- The canonical encoding of a certificate. -/
def encodeW : List Bool → List Bool
  | [] => []
  | v :: w => true :: v :: encodeW w

@[simp] theorem encodeW_length (w : List Bool) : (encodeW w).length = 2 * w.length := by
  induction w with
  | nil => rfl
  | cons v w ih => simp [encodeW, ih]; omega

theorem decodeW_replicate_false (n : Nat) : decodeW (List.replicate n false) = [] := by
  cases n <;> rfl

theorem decodeW_encodeW (w : List Bool) (n : Nat) :
    decodeW (encodeW w ++ List.replicate n false) = w := by
  induction w with
  | nil => simpa [encodeW] using decodeW_replicate_false n
  | cons v w ih => simp [encodeW, decodeW, ih]

theorem decodeW_length (g : List Bool) : 2 * (decodeW g).length ≤ g.length := by
  match g with
  | [] => simp [decodeW]
  | [b] => cases b <;> simp [decodeW]
  | false :: _ :: rest => simp [decodeW]
  | true :: v :: rest =>
    have := decodeW_length rest
    simp only [decodeW, List.length_cons]
    omega

/-- A guessed word of length `2 * p` for every certificate of length at most `p`. -/
theorem exists_guess (w : List Bool) (p : Nat) (hw : w.length ≤ p) :
    ∃ g : List Bool, g.length = 2 * p ∧ decodeW g = w :=
  ⟨encodeW w ++ List.replicate (2 * p - 2 * w.length) false,
    by simp; omega, decodeW_encodeW w _⟩

/-! ## Decoding on stacks -/

def decode {k : Nat} (src dst : Fin (k + 1)) : Program k (Fin 5) where
  start := 0
  code q := if q = 0 then .pop src 1 1 2
    else if q = 1 then .halt true
    else if q = 2 then .pop src 1 3 4
    else if q = 3 then .push dst false 0
    else .push dst true 0

theorem set_set_same_value {k : Nat} (r : Registers k) (src dst : Fin (k + 1)) (hne : src ≠ dst)
    (xs : List Bool) : set (set r src xs) dst (r dst) = set r src xs := by
  have h : (set r src xs) dst = r dst := by simp [Ne.symm hne]
  rw [← h, StackWords.set_unchanged]

theorem exec_decode {k : Nat} (src dst : Fin (k + 1)) (hne : src ≠ dst) :
    ∀ (g : List Bool) (r : Registers k), r src = g →
      ∃ rest time, time ≤ 2 * g.length + 3 ∧
        Exec (decode src dst) 0 r time
          (true, set (set r src rest) dst ((decodeW g).reverse ++ r dst))
  | [], r, hr => by
    refine ⟨[], 2, by omega, ?_⟩
    simp only [decodeW, List.reverse_nil, List.nil_append, set_set_same_value r src dst hne]
    exact .next (q' := 1) (r' := set r src [])
      (by simp [StackProgram.step, decode, hr, branch])
      (.halt (by simp [StackProgram.step, decode]))
  | false :: rest, r, hr => by
    refine ⟨rest, 2, by omega, ?_⟩
    simp only [decodeW, List.reverse_nil, List.nil_append, set_set_same_value r src dst hne]
    exact .next (q' := 1) (r' := set r src rest)
      (by simp [StackProgram.step, decode, hr, branch])
      (.halt (by simp [StackProgram.step, decode]))
  | [true], r, hr => by
    refine ⟨[], 3, by simp, ?_⟩
    simp only [decodeW, List.reverse_nil, List.nil_append, set_set_same_value r src dst hne]
    refine .next (q' := 2) (r' := set r src []) (by simp [StackProgram.step, decode, hr, branch]) ?_
    refine .next (q' := 1) (r' := set r src []) ?_ (.halt (by simp [StackProgram.step, decode]))
    simp [StackProgram.step, decode, branch, StackWords.set_overwrite]
  | true :: v :: rest, r, hr => by
    let r' := set (set r src rest) dst (v :: r dst)
    obtain ⟨rest', time, ht, he⟩ := exec_decode src dst hne rest r' (by simp [r', hne])
    refine ⟨rest', time + 1 + 1 + 1, by simp; omega, ?_⟩
    have hout : set (set r' src rest') dst ((decodeW rest).reverse ++ r' dst) =
        set (set r src rest') dst ((decodeW (true :: v :: rest)).reverse ++ r dst) := by
      funext j
      by_cases hj : j = dst
      · subst j; simp [r', decodeW]
      · by_cases hs : j = src
        · subst j; simp [hj]
        · simp [r', StackMachine.set, hj, hs]
    rw [← hout]
    refine .next (q' := 2) (r' := set r src (v :: rest))
      (by simp [StackProgram.step, decode, hr, branch]) ?_
    refine .next (q' := if v then 4 else 3) (r' := set r src rest) ?_ ?_
    · cases v <;> simp [StackProgram.step, decode, branch, StackWords.set_overwrite]
    refine .next (q' := 0) (r' := r') ?_ he
    cases v <;> simp [StackProgram.step, decode, r', Ne.symm hne]

/-! ## The checker -/

/-- Decode the certificate (register 3), build `(pairWords x w).reverse` in register 6,
expand it into the right tape half (register 7) and simulate `V` (choices in register 8,
left tape half in register 9). -/
def checkerProgram (V : Machine) :=
  StackProgram.seq (decode (k := 9) 0 2)
  (StackProgram.seq (StackWords.transfer (k := 9) 2 3)
  (StackProgram.seq (StackWords.length (k := 9) 1 6 5)
  (StackProgram.seq (StackProgram.push (k := 9) 6 false)
  (StackProgram.seq (StackWords.transfer (k := 9) 1 6)
  (StackProgram.seq (StackWords.transfer (k := 9) 3 6)
  (StackProgram.seq (expand (k := 9) 6 7)
  (core (lift V) (k := 9) 8 9 7)))))))

def checkerEncoding (V : Machine) :=
  (Encoding.fin 4).sum ((Encoding.fin 3).sum (StackWords.copyMapEncoding.sum
    (Encoding.bool.sum ((Encoding.fin 3).sum ((Encoding.fin 3).sum ((Encoding.fin 5).sum
      (labelEncoding (lift V))))))))

def checkerMachine (V : Machine) : StackMachine.Machine :=
  compile (checkerProgram V) (checkerEncoding V)

/-- A bound on the checker's instruction count. -/
def checkTime (guessLength inputLength verifierTime : Nat) : Nat :=
  10 * guessLength + 15 * inputLength + 30 + 5 * verifierTime

theorem pairWords_reverse (x w : List Bool) :
    (w.reverse ++ (x.reverse ++ false :: List.replicate x.length true)).reverse =
      pairWords x w := by
  simp [pairWords, List.reverse_append, List.reverse_replicate, List.append_assoc]

theorem checker_exec (V : Machine) (g x : List Bool) (r : Registers 9)
    (h0 : r 0 = g) (h1 : r 1 = x) (hj : ∀ j : Fin 10, 2 ≤ j.val → r j = [])
    (T : Nat) (d : Bool) (tape : Tape)
    (hV : runInput V T (pairWords x (decodeW g)) = some (d, tape)) :
    ∃ time r', time ≤ checkTime g.length x.length T ∧
      Exec (checkerProgram V) (checkerProgram V).start r time (d, r') := by
  have h2 : r 2 = [] := hj 2 (by decide)
  have h3 : r 3 = [] := hj 3 (by decide)
  have h5 : r 5 = [] := hj 5 (by decide)
  have h6 : r 6 = [] := hj 6 (by decide)
  have h7 : r 7 = [] := hj 7 (by decide)
  have h8 : r 8 = [] := hj 8 (by decide)
  have h9 : r 9 = [] := hj 9 (by decide)
  let w := decodeW g
  have hw : 2 * w.length ≤ g.length := decodeW_length g
  obtain ⟨rest, tdec, htdec, hdec⟩ := exec_decode (k := 9) 0 2 (by decide) g r h0
  let rA := set (set r 0 rest) 2 (w.reverse ++ r 2)
  have hA2 : rA 2 = w.reverse := by simp [rA, h2, w]
  have htr1 := StackWords.exec_transfer (k := 9) 2 3 (by decide) rA
  let rB := set (set rA 2 []) 3 ((rA 2).reverse ++ rA 3)
  have hB1 : rB 1 = x := by simp [rB, rA, h1]
  have hB5 : rB 5 = [] := by simp [rB, rA, h5]
  have hB3 : rB 3 = w := by simp [rB, rA, h2, h3, w]
  have hlen := StackWords.exec_length (k := 9) 1 6 5 (by decide) (by decide) (by decide) rB hB5
  let rC := set rB 6 (List.replicate (rB 1).length true)
  have hpush := StackProgram.exec_push (k := 9) 6 false rC
  let rD := set rC 6 (false :: rC 6)
  have htr2 := StackWords.exec_transfer (k := 9) 1 6 (by decide) rD
  let rE := set (set rD 1 []) 6 ((rD 1).reverse ++ rD 6)
  have htr3 := StackWords.exec_transfer (k := 9) 3 6 (by decide) rE
  let rF := set (set rE 3 []) 6 ((rE 3).reverse ++ rE 6)
  have hF6 : rF 6 = w.reverse ++ (x.reverse ++ false :: List.replicate x.length true) := by
    simp [rF, rE, rD, rC, hB1, hB3]
  have hex := exec_expand (k := 9) 6 7 (by decide) (rF 6) rF rfl
  let rG := set (set rF 6 []) 7 (symbols ((rF 6).reverse.map Symbol.bit) ++ rF 7)
  have hG7 : rG 7 = symbols ((pairWords x w).map Symbol.bit) := by
    have h7' : rF 7 = [] := by simp [rF, rE, rD, rC, rB, rA, h7]
    simp only [rG, StackMachine.set_same, h7', List.append_nil]
    rw [hF6, pairWords_reverse]
  have hG8 : rG 8 = [] := by simp [rG, rF, rE, rD, rC, rB, rA, h8]
  have hG9 : rG 9 = [] := by simp [rG, rF, rE, rD, rC, rB, rA, h9]
  have hrun : runD (lift V) T [] (lift V).start (Tape.ofInput (pairWords x w)) =
      some (d, tape) := by
    exact (runD_lift V T [] V.start _).trans hV
  obtain ⟨tcore, r', htcore, hcore⟩ := core_runs (lift V) (k := 9) 8 9 7 (by decide)
    (by decide) (by decide) T [] (pairWords x w) d tape hrun rG hG8 hG9 hG7
  have hall := exec_seq _ _ hdec (exec_seq _ _ htr1 (exec_seq _ _ hlen (exec_seq _ _ hpush
    (exec_seq _ _ htr2 (exec_seq _ _ htr3 (exec_seq _ _ hex hcore))))))
  refine ⟨_, r', ?_, hall⟩
  have e1 : (rA 2).length = w.length := by simp [hA2]
  have e2 : (rB 6).length = 0 := by simp [rB, rA, h6]
  have e3 : (rB 1).length = x.length := by simp [hB1]
  have e4 : (rD 1).length = x.length := by simp [rD, rC, hB1]
  have e5 : (rE 3).length = w.length := by simp [rE, rD, rC, hB3]
  have e6 : (rF 6).length = w.length + x.length + 1 + x.length := by simp [hF6]; omega
  rw [e1, e2, e3, e4, e5, e6]
  unfold checkTime
  omega

/-- The compiled checker runs within `checkTime` and halts with the verifier's decision. -/
theorem checker_runs (V : Machine) (g x : List Bool) (r : Registers 9)
    (h0 : r 0 = g) (h1 : r 1 = x) (hj : ∀ j : Fin 10, 2 ≤ j.val → r j = [])
    (T : Nat) (d : Bool) (tape : Tape)
    (hV : runInput V T (pairWords x (decodeW g)) = some (d, tape)) :
    ∃ time, ∃ r' : Registers 9, time ≤ checkTime g.length x.length T ∧
      StackMachine.run (checkerMachine V) time ⟨(checkerMachine V).start, r⟩ =
        some (d, r') := by
  obtain ⟨time, r', ht, he⟩ := checker_exec V g x r h0 h1 hj T d tape hV
  exact ⟨time, r', ht, compile_exec (checkerEncoding V) he⟩

end Complexity.NTM
