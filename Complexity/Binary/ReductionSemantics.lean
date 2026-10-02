module

public import Complexity.Binary.ReductionLoops
public import Complexity.StackCompile
import Lean.Elab.Tactic.Omega

/-!
# Correctness of the SAT to binary SAT transducer

The register semantics of the transducer (`Reduce.transformedWord`) is the pure reduction
`Binary.reduceWord`, on every word. With the instruction bound of `ReductionLoops`, this
gives a polynomial-time Karp reduction from SAT to binary SAT.
-/

@[expose] public section

namespace Complexity.Binary.Reduce

open Complexity.StackMachine (Registers set)
open Complexity.SAT
open Complexity.Binary

theorem writeValues_append {α : Type} (enc : α → Word) (xs ys : List α) :
    writeValues enc (xs ++ ys) = writeValues enc xs ++ writeValues enc ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [writeValues, ih, List.append_assoc]

theorem binaryClause_cons (l : Literal) (c : Clause) :
    binaryClause (l :: c) = binaryClause c ++ [toBinary l] := by
  simp [binaryClause]

theorem literals_success (m : Nat) (r : Registers 10) (c : Clause) (rest : Word)
    (hr : r inner = List.replicate m true)
    (hp : readMany readLiteral m (r input) = some (c, rest)) :
    iterStep inner litStep m r = some (set (set (set (set r inner []) input rest) output
      (writeValues encodeBinaryLiteral (binaryClause c) ++ r output)) litCount
      (List.replicate m true ++ r litCount)) := by
  induction m generalizing r c rest with
  | zero =>
    have hc : c = [] ∧ rest = r input := by
      simpa [readMany, Prod.mk.injEq, eq_comm] using hp
    obtain ⟨rfl, rfl⟩ := hc
    have hz : r inner = [] := by simpa using hr
    simp only [iterStep_zero, Option.some.injEq]
    apply regs_ext <;> simp [hz, binaryClause, writeValues]
  | succ m ih =>
    cases hl : readLiteral (r input) with
    | none => simp [readMany, hl] at hp
    | some pair =>
      obtain ⟨l, tail⟩ := pair
      cases hm : readMany readLiteral m tail with
      | none => simp [readMany, hl, hm] at hp
      | some result =>
        obtain ⟨cs, final⟩ := result
        have hc : c = l :: cs ∧ rest = final := by
          simpa [readMany, hl, hm, Prod.mk.injEq, eq_comm] using hp
        obtain ⟨rfl, rfl⟩ := hc
        let r' := litFinish (set r inner (List.replicate m true)) l tail
        have hstep : litStep (set r inner (List.replicate m true)) = some r' := by
          have hl' : readLiteral ((set r inner (List.replicate m true)) input) =
              some (l, tail) := by simpa using hl
          simp only [litStep, StackMachine.set_other _ (by decide : input ≠ inner), hl, r']
        have h' := ih r' cs rest (by simp [r', litFinish]) (by simpa [r', litFinish] using hm)
        rw [iterStep_succ, hstep, Option.bind_some, h']
        congr 1
        apply regs_ext <;>
          simp [r', litFinish, binaryClause_cons, writeValues_append, writeValues,
            List.append_assoc, List.replicate_succ']

theorem literals_failure (m : Nat) (r : Registers 10)
    (hp : readMany readLiteral m (r input) = none) : iterStep inner litStep m r = none := by
  induction m generalizing r with
  | zero => simp [readMany] at hp
  | succ m ih =>
    cases hl : readLiteral (r input) with
    | none =>
      have hl' : readLiteral ((set r inner (List.replicate m true)) input) = none := by
        simpa using hl
      simp only [iterStep_succ, litStep, StackMachine.set_other _ (by decide : input ≠ inner), hl, Option.bind_none]
    | some pair =>
      obtain ⟨l, tail⟩ := pair
      have ht : readMany readLiteral m tail = none := by
        cases hm : readMany readLiteral m tail with
        | none => rfl
        | some result => obtain ⟨c, rest⟩ := result; simp [readMany, hl, hm] at hp
      let r' := litFinish (set r inner (List.replicate m true)) l tail
      have hstep : litStep (set r inner (List.replicate m true)) = some r' := by
        have hl' : readLiteral ((set r inner (List.replicate m true)) input) =
            some (l, tail) := by simpa using hl
        simp only [litStep, StackMachine.set_other _ (by decide : input ≠ inner), hl, r']
      rw [iterStep_succ, hstep, Option.bind_some]
      exact ih r' (by simpa [r', litFinish] using ht)

theorem clauseStep_success (r : Registers 10) (c : Clause) (rest : Word)
    (hi : r inner = []) (hl : r litCount = [])
    (hp : readClause (r input) = some (c, rest)) :
    clauseStep r = some (set (set (set r input rest) output
      (encodeBinaryClause (binaryClause c) ++ r output)) clauseCount (true :: r clauseCount)) := by
  cases hn : readNat (r input) with
  | none => simp [readClause, readList, hn] at hp
  | some pair =>
    obtain ⟨m, tail⟩ := pair
    have hm : readMany readLiteral m tail = some (c, rest) := by
      simpa [readClause, readList, hn] using hp
    have hlen := (readMany_eq_some readLiteral encodeLiteral readLiteral_eq_some hm).1
    have h := literals_success m (set (set r input tail) inner (List.replicate m true)) c rest
      (by simp) (by simpa using hm)
    simp only [clauseStep, hn, h, Option.map_some, Option.some.injEq]
    apply regs_ext <;>
      simp [clauseFinish, hi, hl, encodeBinaryClause, writeList, binaryClause, hlen,
        Complexity.StackParse.writeNat_eq, List.append_assoc]

theorem clauseStep_failure (r : Registers 10) (hp : readClause (r input) = none) :
    clauseStep r = none := by
  cases hn : readNat (r input) with
  | none => simp [clauseStep, hn]
  | some pair =>
    obtain ⟨m, tail⟩ := pair
    have hm : readMany readLiteral m tail = none := by
      simpa [readClause, readList, hn] using hp
    have h := literals_failure m (set (set r input tail) inner (List.replicate m true))
      (by simpa using hm)
    simp [clauseStep, hn, h]

theorem clauses_success (n : Nat) (r : Registers 10) (f : CNF) (rest : Word)
    (hr : r outer = List.replicate n true) (hi : r inner = []) (hl : r litCount = [])
    (hp : readMany readClause n (r input) = some (f, rest)) :
    iterStep outer clauseStep n r = some (set (set (set (set r outer []) input rest) output
      (writeValues encodeBinaryClause ((f.map binaryClause).reverse) ++ r output)) clauseCount
      (List.replicate n true ++ r clauseCount)) := by
  induction n generalizing r f rest with
  | zero =>
    have hc : f = [] ∧ rest = r input := by
      simpa [readMany, Prod.mk.injEq, eq_comm] using hp
    obtain ⟨rfl, rfl⟩ := hc
    have hz : r outer = [] := by simpa using hr
    simp only [iterStep_zero, Option.some.injEq]
    apply regs_ext <;> simp [hz, writeValues]
  | succ n ih =>
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
        let r₀ := set r outer (List.replicate n true)
        let r' := set (set (set r₀ input tail) output
          (encodeBinaryClause (binaryClause c) ++ r₀ output)) clauseCount (true :: r₀ clauseCount)
        have hstep : clauseStep r₀ = some r' :=
          clauseStep_success r₀ c tail (by simpa [r₀] using hi) (by simpa [r₀] using hl)
            (by simpa [r₀] using hc)
        have h' := ih r' fs rest (by simp [r', r₀]) (by simpa [r', r₀] using hi)
          (by simpa [r', r₀] using hl) (by simpa [r', r₀] using hm)
        rw [iterStep_succ, hstep, Option.bind_some, h']
        congr 1
        apply regs_ext <;>
          simp [r', r₀, writeValues_append, writeValues, List.append_assoc,
            List.replicate_succ']

theorem clauses_failure (n : Nat) (r : Registers 10) (hi : r inner = []) (hl : r litCount = [])
    (hp : readMany readClause n (r input) = none) : iterStep outer clauseStep n r = none := by
  induction n generalizing r with
  | zero => simp [readMany] at hp
  | succ n ih =>
    let r₀ := set r outer (List.replicate n true)
    cases hc : readClause (r input) with
    | none =>
      have h := clauseStep_failure r₀ (by simpa [r₀] using hc)
      rw [iterStep_succ]
      change (clauseStep r₀).bind _ = none
      rw [h]
      rfl
    | some pair =>
      obtain ⟨c, tail⟩ := pair
      have ht : readMany readClause n tail = none := by
        cases hm : readMany readClause n tail with
        | none => rfl
        | some result => obtain ⟨f, rest⟩ := result; simp [readMany, hc, hm] at hp
      let r' := set (set (set r₀ input tail) output
        (encodeBinaryClause (binaryClause c) ++ r₀ output)) clauseCount (true :: r₀ clauseCount)
      have hstep : clauseStep r₀ = some r' :=
        clauseStep_success r₀ c tail (by simpa [r₀] using hi) (by simpa [r₀] using hl)
          (by simpa [r₀] using hc)
      rw [iterStep_succ]
      change (clauseStep r₀).bind _ = none
      rw [hstep, Option.bind_some]
      exact ih r' (by simpa [r', r₀] using hi) (by simpa [r', r₀] using hl)
        (by simpa [r', r₀] using ht)

/-- The transducer's register semantics is the pure reduction. -/
theorem transformedWord_eq (r : Registers 10) (hi : r inner = []) (hl : r litCount = [])
    (hc : r clauseCount = []) (ho : r output = []) :
    transformedWord r = reduceWord (r input) := by
  cases hn : readNat (r input) with
  | none =>
    have hd : decode (r input) = none := by simp [decode, readCNF, readList, hn]
    simp [transformedWord, parseStep, hn, reduceWord, hd]
  | some pair =>
    obtain ⟨n, tail⟩ := pair
    let r₁ := set (set r input tail) outer (List.replicate n true)
    cases hm : readMany readClause n tail with
    | none =>
      have hd : decode (r input) = none := by simp [decode, readCNF, readList, hn, hm]
      have h := clauses_failure n r₁ (by simpa [r₁] using hi) (by simpa [r₁] using hl)
        (by simpa [r₁] using hm)
      have h' : iterStep outer clauseStep n (set (set r input tail) outer
          (List.replicate n true)) = none := h
      simp [transformedWord, parseStep, hn, h', reduceWord, hd]
    | some result =>
      obtain ⟨f, rest⟩ := result
      have h := clauses_success n r₁ f rest (by simp [r₁]) (by simpa [r₁] using hi)
        (by simpa [r₁] using hl) (by simpa [r₁] using hm)
      have h' : iterStep outer clauseStep n (set (set r input tail) outer
          (List.replicate n true)) = _ := h
      have hlen := (readMany_eq_some readClause encodeClause readClause_eq_some hm).1
      cases rest with
      | cons b rest =>
        have hd : decode (r input) = none := by simp [decode, readCNF, readList, hn, hm]
        simp [transformedWord, parseStep, hn, h', reduceWord, hd]
      | nil =>
        have hd : decode (r input) = some f := by simp [decode, readCNF, readList, hn, hm]
        simp [transformedWord, parseStep, hn, h', reduceWord, hd, hc, ho, r₁, encodeBinary_eq,
          writeList, binaryCNF, hlen, Complexity.StackParse.writeNat_eq, List.append_assoc]

theorem transformedWord_initial (word : Word) :
    transformedWord (initialRegisters word) = reduceWord word := by
  have h := transformedWord_eq (initialRegisters word) rfl rfl rfl rfl
  simpa [initialRegisters] using h

end Complexity.Binary.Reduce

namespace Complexity.Binary

/-- The reduction is computed by a polynomial-time machine. -/
theorem reduceWord_polyTime : PolyTime reduceWord := by
  apply StackCompile.polyTime_of_stack Reduce.machine Reduce.transformCost
    Reduce.polynomialBound_transformCost
  intro input
  obtain ⟨out, hr, ho⟩ := Reduce.machine_runs input
  exact ⟨_, out, Nat.le_refl _, hr, ho.trans (Reduce.transformedWord_initial input)⟩

/-- SAT reduces to binary SAT. -/
theorem sat_polyRed_binarySAT : PolyRed SAT.SAT SAT.BinarySAT :=
  ⟨reduceWord, reduceWord_polyTime, reduceWord_correct⟩

end Complexity.Binary
