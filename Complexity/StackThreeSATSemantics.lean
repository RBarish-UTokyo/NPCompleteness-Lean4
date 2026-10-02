module

public import Complexity.StackThreeSAT
import Lean.Elab.Tactic.Omega

/-! The checked stack parser's exact register semantics implements the proved
implication-chain reduction, including rejection of malformed encoded inputs. -/

@[expose] public section

namespace Complexity.StackThreeSATSemantics

open Complexity.SAT Complexity.ThreeSAT
open Complexity.StackThreeSAT
open Complexity.StackMachine (Registers set)

theorem writeValues_append {α : Type} (enc : α → Word) (xs ys : List α) :
    writeValues enc (xs ++ ys) = writeValues enc xs ++ writeValues enc ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [writeValues, ih, List.append_assoc]

def implications (n : Nat) : Clause → CNF
  | [] => []
  | l :: rest => implications (n + 1) rest ++ [ChainThreeSAT.implicationClause n l]

theorem chainEnd_eq (n : Nat) (c : Clause) :
    ChainThreeSAT.chainEnd n c = [[neg (n + c.length)]] ++ implications n c := by
  induction c generalizing n with
  | nil => simp [ChainThreeSAT.chainEnd, implications]
  | cons l c ih =>
    simp [ChainThreeSAT.chainEnd, implications, ih, Nat.add_left_comm, Nat.add_comm]

theorem literalsStep_failure (n : Nat) (r : Registers 7)
    (hp : readMany readLiteral n (r input) = none) : literalsStep n r = none := by
  induction n generalizing r with
  | zero => simp [readMany] at hp
  | succ n ih =>
    cases hl : readLiteral (r input) with
    | none => simp [literalsStep, literalStep, input, inner, hl] at *
    | some pair =>
      obtain ⟨l, tail⟩ := pair
      let r' := chainLiteralFinish (set r inner (List.replicate n true)) l tail
      have hin : r' input = tail := by simp [r']
      have ht : readMany readLiteral n tail = none := by
        cases hm : readMany readLiteral n tail with
        | none => rfl
        | some result => obtain ⟨c, rest⟩ := result; simp [readMany, hl, hm] at hp
      have hi := ih r' (by simpa [hin] using ht)
      simpa [literalsStep, literalStep, r', StackMachine.set_other _ (by decide : input ≠ inner), hl] using hi

theorem literalsStep_success (n : Nat) (r : Registers 7) (c : Clause) (rest : Word)
    (hp : readMany readLiteral n (r input) = some (c, rest)) :
    ∃ out, literalsStep n r = some out ∧ out input = rest ∧
      (out fresh).length = (r fresh).length + c.length ∧
      (out count).length = (r count).length + c.length ∧
      out output = writeValues encodeClause (implications (r fresh).length c) ++ r output := by
  induction n generalizing r c rest with
  | zero =>
    have hc : c = [] ∧ rest = r input := by
      simpa [readMany, Prod.mk.injEq, eq_comm] using hp
    obtain ⟨rfl, rfl⟩ := hc
    exact ⟨r, rfl, rfl, by simp, by simp, by simp [implications, writeValues]⟩
  | succ n ih =>
    cases hl : readLiteral (r input) with
    | none => simp [readMany, hl] at hp
    | some pair =>
      obtain ⟨l, tail⟩ := pair
      cases hm : readMany readLiteral n tail with
      | none => simp [readMany, hl, hm] at hp
      | some result =>
        obtain ⟨cs, final⟩ := result
        have hc : c = l :: cs ∧ rest = final := by
          simpa [readMany, hl, hm, Prod.mk.injEq, eq_comm] using hp
        obtain ⟨rfl, rfl⟩ := hc
        let r' := chainLiteralFinish (set r inner (List.replicate n true)) l tail
        have hin : r' input = tail := by simp [r']
        obtain ⟨out, he, hi, hf, hk, ho⟩ := ih r' cs _ (by simpa [hin] using hm)
        refine ⟨out, ?_, hi, ?_, ?_, ?_⟩
        · simpa [literalsStep, literalStep, r', StackMachine.set_other _ (by decide : input ≠ inner), hl] using he
        · simp only [r', chainFinish_fresh, StackMachine.set_other _ (by decide : fresh ≠ inner), List.length_cons] at hf
          simp only [List.length_cons]
          omega
        · simp only [r', chainFinish_count, StackMachine.set_other _ (by decide : count ≠ inner), List.length_cons] at hk
          simp only [List.length_cons]
          omega
        · simp only [r', chainFinish_output, chainFinish_fresh,
            StackMachine.set_other _ (by decide : fresh ≠ inner),
            StackMachine.set_other _ (by decide : output ≠ inner), List.length_cons] at ho
          simpa [implications, writeValues_append, writeValues, implicationClause, List.append_assoc] using ho

theorem clauseStep_failure (r : Registers 7) (hp : readClause (r input) = none) :
    clauseStep r = none := by
  cases hn : readNat (r input) with
  | none => simp [clauseStep, hn]
  | some pair =>
    obtain ⟨n, tail⟩ := pair
    have hm : readMany readLiteral n tail = none := by simpa [readClause, readList, hn] using hp
    let q := unitFinish (set (set r input tail) inner (List.replicate n true)) true
    have hq : q input = tail := by
      simp only [q, unitFinish_input, StackMachine.set_other _ (by decide : input ≠ inner), StackMachine.set_same]
    have he := literalsStep_failure n q (by simpa [hq] using hm)
    simp only [clauseStep, hn, Option.bind_eq_bind, Option.bind_some]
    change (literalsStep n q).bind _ = none
    rw [he]
    rfl

theorem clauseStep_success (r : Registers 7) (c : Clause) (rest : Word)
    (hp : readClause (r input) = some (c, rest)) :
    ∃ out, clauseStep r = some out ∧ out input = rest ∧
      (out fresh).length = (r fresh).length + c.length + 1 ∧
      (out count).length = (r count).length + c.length + 2 ∧
      out output = writeValues encodeClause (ChainThreeSAT.chainClause (r fresh).length c) ++ r output := by
  cases hn : readNat (r input) with
  | none => simp [readClause, readList, hn] at hp
  | some pair =>
    obtain ⟨n, tail⟩ := pair
    have hm : readMany readLiteral n tail = some (c, rest) := by simpa [readClause, readList, hn] using hp
    let q := unitFinish (set (set r input tail) inner (List.replicate n true)) true
    have hq : q input = tail := by
      simp only [q, unitFinish_input, StackMachine.set_other _ (by decide : input ≠ inner), StackMachine.set_same]
    obtain ⟨mid, he, hi, hf, hk, ho⟩ := literalsStep_success n q c rest (by simpa [hq] using hm)
    let out := set (unitFinish mid false) fresh (true :: mid fresh)
    have hqFresh : q fresh = r fresh := by
      simp only [q, unitFinish_fresh, StackMachine.set_other _ (by decide : fresh ≠ inner),
        StackMachine.set_other _ (by decide : fresh ≠ input)]
    have hqCount : q count = true :: r count := by
      simp only [q, unitFinish_count, StackMachine.set_other _ (by decide : count ≠ inner),
        StackMachine.set_other _ (by decide : count ≠ input)]
    have hqOutput : q output = encodeClause [pos (r fresh).length] ++ r output := by
      simp only [q, unitFinish_output, StackMachine.set_other _ (by decide : fresh ≠ inner),
        StackMachine.set_other _ (by decide : fresh ≠ input), StackMachine.set_other _ (by decide : output ≠ inner),
        StackMachine.set_other _ (by decide : output ≠ input), pos]
    refine ⟨out, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [clauseStep, hn, Option.bind_eq_bind, Option.bind_some]
      change (literalsStep n q).bind _ = some out
      rw [he]
      rfl
    · simpa only [out, StackMachine.set_other _ (by decide : input ≠ fresh), unitFinish_input] using hi
    · simp only [out, StackMachine.set_same, List.length_cons]
      rw [hf, hqFresh]
    · simp only [out, StackMachine.set_other _ (by decide : count ≠ fresh), unitFinish_count, List.length_cons]
      rw [hk, hqCount]
      simp only [List.length_cons]
      omega
    · simp only [out, StackMachine.set_other _ (by decide : output ≠ fresh), unitFinish_output]
      rw [ho, hf, hqFresh, hqOutput]
      simp [ChainThreeSAT.chainClause, chainEnd_eq, writeValues_append, writeValues,
        pos, neg, List.append_assoc]

theorem clausesStep_failure (n : Nat) (r : Registers 7)
    (hp : readMany readClause n (r input) = none) : clausesStep n r = none := by
  induction n generalizing r with
  | zero => simp [readMany] at hp
  | succ n ih =>
    let r₀ := set r outer (List.replicate n true)
    have hin : r₀ input = r input := by simp [r₀, input, outer]
    cases hc : readClause (r input) with
    | none =>
      have he := clauseStep_failure r₀ (by simpa [hin] using hc)
      simp only [clausesStep]
      change (clauseStep r₀).bind _ = none
      rw [he]
      rfl
    | some pair =>
      obtain ⟨c, tail⟩ := pair
      have ht : readMany readClause n tail = none := by
        cases hm : readMany readClause n tail with
        | none => rfl
        | some result => obtain ⟨f, rest⟩ := result; simp [readMany, hc, hm] at hp
      obtain ⟨mid, hm, hi, _, _, _⟩ := clauseStep_success r₀ c tail (by simpa [hin] using hc)
      have hr := ih mid (by simpa [hi] using ht)
      simp only [clausesStep]
      change (clauseStep r₀).bind _ = none
      rw [hm]
      exact hr

theorem clausesStep_success (n : Nat) (r : Registers 7) (f : CNF) (rest : Word)
    (hp : readMany readClause n (r input) = some (f, rest)) :
    ∃ out, clausesStep n r = some out ∧ out input = rest ∧
      (out fresh).length = (r fresh).length + formulaSize f ∧
      (out count).length = (r count).length + (formulaSize f + f.length) ∧
      out output = writeValues encodeClause (ChainThreeSAT.chainCNF (r fresh).length f) ++ r output := by
  induction n generalizing r f rest with
  | zero =>
    have hc : f = [] ∧ rest = r input := by
      simpa [readMany, Prod.mk.injEq, eq_comm] using hp
    obtain ⟨rfl, rfl⟩ := hc
    exact ⟨r, rfl, rfl, by simp [formulaSize], by simp [formulaSize],
      by simp [ChainThreeSAT.chainCNF, writeValues]⟩
  | succ n ih =>
    let r₀ := set r outer (List.replicate n true)
    have hin : r₀ input = r input := by simp [r₀, input, outer]
    have hfresh : r₀ fresh = r fresh := by simp [r₀, fresh, outer]
    have hcount : r₀ count = r count := by simp [r₀, count, outer]
    have hout : r₀ output = r output := by simp [r₀, output, outer]
    cases hc : readClause (r input) with
    | none => simp [readMany, hc] at hp
    | some pair =>
      obtain ⟨c, tail⟩ := pair
      cases hm : readMany readClause n tail with
      | none => simp [readMany, hc, hm] at hp
      | some result =>
        obtain ⟨fs, final⟩ := result
        have heq : f = c :: fs ∧ rest = final := by
          simpa [readMany, hc, hm, Prod.mk.injEq, eq_comm] using hp
        obtain ⟨rfl, rfl⟩ := heq
        obtain ⟨mid, hms, hmi, hmf, hmk, hmo⟩ := clauseStep_success r₀ c tail (by simpa [hin] using hc)
        rw [hfresh] at hmf hmo
        rw [hcount] at hmk
        rw [hout] at hmo
        obtain ⟨out, he, hi, hf, hk, ho⟩ := ih mid fs _ (by simpa [hmi] using hm)
        refine ⟨out, ?_, hi, ?_, ?_, ?_⟩
        · simp only [clausesStep]
          change (clauseStep r₀).bind _ = some out
          rw [hms]
          exact he
        · rw [hf, hmf]
          simp [formulaSize, Nat.add_assoc]
        · rw [hk, hmk]
          simp only [formulaSize, List.length_cons]
          omega
        · rw [ho, hmf, hmo]
          simp [ChainThreeSAT.chainCNF, writeValues_append, List.append_assoc]

theorem parseCNFStep_failure (r : Registers 7) (hp : decode (r input) = none) :
    parseCNFStep r = none := by
  cases hn : readNat (r input) with
  | none => simp [parseCNFStep, hn]
  | some pair =>
    obtain ⟨n, tail⟩ := pair
    let r₀ := set (set r input tail) outer (List.replicate n true)
    have hin : r₀ input = tail := by simp [r₀, input, outer]
    cases hm : readMany readClause n tail with
    | none =>
      have he := clausesStep_failure n r₀ (by simpa [hin] using hm)
      simp only [parseCNFStep, hn, Option.bind_eq_bind, Option.bind_some]
      change (clausesStep n r₀).bind _ = none
      rw [he]
      rfl
    | some result =>
      obtain ⟨f, rest⟩ := result
      obtain ⟨out, he, hi, _, _, _⟩ := clausesStep_success n r₀ f rest (by simpa [hin] using hm)
      cases rest with
      | nil => simp [decode, readCNF, readList, hn, hm] at hp
      | cons b rest =>
        simp only [parseCNFStep, hn, Option.bind_eq_bind, Option.bind_some]
        change (clausesStep n r₀).bind _ = none
        rw [he]
        simp [hi]

theorem parseCNFStep_success (r : Registers 7) (f : CNF) (hp : decode (r input) = some f) :
    ∃ out, parseCNFStep r = some out ∧ out input = [] ∧
      (out fresh).length = (r fresh).length + formulaSize f ∧
      (out count).length = (r count).length + (formulaSize f + f.length) ∧
      out output = writeValues encodeClause (ChainThreeSAT.chainCNF (r fresh).length f) ++ r output := by
  cases hn : readNat (r input) with
  | none => simp [decode, readCNF, readList, hn] at hp
  | some pair =>
    obtain ⟨n, tail⟩ := pair
    let r₀ := set (set r input tail) outer (List.replicate n true)
    have hin : r₀ input = tail := by simp [r₀, input, outer]
    cases hm : readMany readClause n tail with
    | none => simp [decode, readCNF, readList, hn, hm] at hp
    | some result =>
      obtain ⟨g, rest⟩ := result
      cases rest with
      | cons b rest => simp [decode, readCNF, readList, hn, hm] at hp
      | nil =>
        have hg : g = f := by simpa [decode, readCNF, readList, hn, hm] using hp
        subst g
        obtain ⟨out, he, hi, hf, hk, ho⟩ := clausesStep_success n r₀ f [] (by simpa [hin] using hm)
        refine ⟨out, ?_, hi, ?_, ?_, ?_⟩
        · simp only [parseCNFStep, hn, Option.bind_eq_bind, Option.bind_some]
          change (clausesStep n r₀).bind _ = some out
          rw [he]
          simp [hi]
        · simpa [r₀, fresh, input, outer] using hf
        · simpa [r₀, count, input, outer] using hk
        · have hr : r₀ fresh = r fresh := by simp [r₀, fresh, input, outer]
          have ho₀ : r₀ output = r output := by simp [r₀, output, input, outer]
          simpa [hr, ho₀] using ho

theorem parseCNFStep_formatted (r : Registers 7) (f : CNF)
    (hp : decode (r input) = some f) (hcount : r count = []) (houtput : r output = []) :
    ∃ out, parseCNFStep r = some out ∧
      writeNat (out count).length ++ out output = encode (ChainThreeSAT.chainCNF (r fresh).length f) := by
  obtain ⟨out, he, _, _, hc, ho⟩ := parseCNFStep_success r f hp
  refine ⟨out, he, ?_⟩
  rw [hc, ho, hcount, houtput]
  simp [encode, writeList, ChainThreeSAT.chainCNF_length]

/-- Final formatting used by the runtime wrapper, including its malformed-input result. -/
def formattedResult (r : Registers 7) : Word :=
  match parseCNFStep r with
  | none => encode [[]]
  | some out => writeNat (out count).length ++ out output

theorem formattedResult_eq_reduceWord (r : Registers 7)
    (hfresh : (r fresh).length = (r input).length)
    (hcount : r count = []) (houtput : r output = []) :
    formattedResult r = ChainThreeSAT.reduceWord (r input) := by
  cases hp : decode (r input) with
  | none => simp [formattedResult, parseCNFStep_failure r hp, ChainThreeSAT.reduceWord, hp]
  | some f =>
    obtain ⟨out, he, ho⟩ := parseCNFStep_formatted r f hp hcount houtput
    simp [formattedResult, he, ho, hfresh, ChainThreeSAT.reduceWord, hp]

theorem formattedResult_correct (r : Registers 7)
    (hfresh : (r fresh).length = (r input).length)
    (hcount : r count = []) (houtput : r output = []) :
    SAT (r input) ↔ SAT.ThreeSAT (formattedResult r) := by
  rw [formattedResult_eq_reduceWord r hfresh hcount houtput]
  exact ChainThreeSAT.reduceWord_correct (r input)

theorem reduceWord_eq (word : Word) :
    StackThreeSAT.reduceWord word = ChainThreeSAT.reduceWord word := by
  have hin : preparedRegisters word input = word := by
    simp [preparedRegisters, initialRegisters, input, fresh]
  have hf : (preparedRegisters word fresh).length = (preparedRegisters word input).length := by
    rw [hin]
    simp [preparedRegisters]
  have hc : preparedRegisters word count = [] := by
    simp [preparedRegisters, initialRegisters, count, fresh, input]
  have ho : preparedRegisters word output = [] := by
    simp [preparedRegisters, initialRegisters, output, fresh, input]
  change formattedResult (preparedRegisters word) = ChainThreeSAT.reduceWord word
  simpa only [hin] using formattedResult_eq_reduceWord (preparedRegisters word) hf hc ho

theorem reduceWord_correct (word : Word) :
    SAT word ↔ SAT.ThreeSAT (StackThreeSAT.reduceWord word) := by
  rw [reduceWord_eq]
  exact ChainThreeSAT.reduceWord_correct word

end Complexity.StackThreeSATSemantics
