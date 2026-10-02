module

public import Complexity.Binary.Spec
public import Complexity.Binary.Increment
import Lean.Elab.Tactic.Omega

/-!
# A stack transducer from SAT to binary SAT

The transducer parses the unary-indexed formula clause by clause and literal by literal.
For each literal it converts the unary index into binary (`toBinaryProg`) and prepends the
binary literal to the output; after each clause it prepends the literal count, and at the
end the clause count. Because the output is built by prepending, the literal order inside
each clause and the clause order are reversed; see `Binary.reduceWord`.

This file gives the programs, their partial register semantics (`litStep`, `clauseStep`,
`parseStep`) and the instruction counts. `ReductionSemantics` relates the semantics to the
parser of `Complexity.SAT`.
-/

@[expose] public section

namespace Complexity.Binary.Reduce

open Complexity.StackMachine (Registers set)
open Complexity.StackProgram Complexity.StackWords Complexity.StackParse
open Complexity.SAT
open Complexity.Binary

abbrev Reg := Fin 11
abbrev input : Reg := 0
abbrev outer : Reg := 1
abbrev inner : Reg := 2
abbrev var : Reg := 3
abbrev digits : Reg := 4
abbrev carry : Reg := 5
abbrev temp : Reg := 6
abbrev width : Reg := 7
abbrev output : Reg := 8
abbrev litCount : Reg := 9
abbrev clauseCount : Reg := 10

attribute [simp] input outer inner var digits carry temp width output litCount clauseCount

theorem regs_ext {r s : Registers 10} (h0 : r 0 = s 0) (h1 : r 1 = s 1) (h2 : r 2 = s 2)
    (h3 : r 3 = s 3) (h4 : r 4 = s 4) (h5 : r 5 = s 5) (h6 : r 6 = s 6) (h7 : r 7 = s 7)
    (h8 : r 8 = s 8) (h9 : r 9 = s 9) (h10 : r 10 = s 10) : r = s := by
  funext a
  obtain ⟨n, hn⟩ := a
  match n, hn with
  | 0, _ => exact h0
  | 1, _ => exact h1
  | 2, _ => exact h2
  | 3, _ => exact h3
  | 4, _ => exact h4
  | 5, _ => exact h5
  | 6, _ => exact h6
  | 7, _ => exact h7
  | 8, _ => exact h8
  | 9, _ => exact h9
  | 10, _ => exact h10
  | n + 11, h => omega

/-- The work registers of the literal conversion are empty. -/
structure Clean (r : Registers 10) : Prop where
  var_eq : r 3 = []
  digits_eq : r 4 = []
  carry_eq : r 5 = []
  temp_eq : r 6 = []
  width_eq : r 7 = []

theorem Clean.set {r : Registers 10} (h : Clean r) (j : Reg) (hv : j ≠ var) (hd : j ≠ digits)
    (hc : j ≠ carry) (ht : j ≠ temp) (hw : j ≠ width) (xs : Word) :
    Clean (StackMachine.set r j xs) := by
  constructor
  · simpa [Ne.symm hv] using h.var_eq
  · simpa [Ne.symm hd] using h.digits_eq
  · simpa [Ne.symm hc] using h.carry_eq
  · simpa [Ne.symm ht] using h.temp_eq
  · simpa [Ne.symm hw] using h.width_eq

theorem writeValues_bits (bits : List Bool) : writeValues (fun b => [b]) bits = bits := by
  induction bits with
  | nil => rfl
  | cons b bits ih => simp [writeValues, ih]

/-! ## One literal -/

/-- After the sign bit: read the unary index, convert it to binary, and prepend the binary
literal (sign, digit count, digits) to the output; count the literal. -/
def emitLiteral (s : Bool) :=
  seq (readUnary input var)
  (seq (toBinaryProg var digits carry)
  (seq (transfer digits temp)
  (seq (scatter temp output width true true)
  (seq (push output false)
  (seq (transfer width output)
  (seq (push output s) (push litCount true)))))))

def emitLiteralEncoding :=
  readUnaryEncoding.sum (toBinaryEncoding.sum ((Encoding.fin 3).sum ((Encoding.fin 5).sum
    (Encoding.bool.sum ((Encoding.fin 3).sum (Encoding.bool.sum Encoding.bool))))))

def literalSign (s : Bool) := seq (pop input) (emitLiteral s)

def literalSignEncoding := Encoding.bool.sum emitLiteralEncoding

/-- Read one literal and prepend its binary form. -/
def literal := peekCase input (stop 10 false) (literalSign false) (literalSign true)

def literalEncoding :=
  Encoding.unit.sum (Encoding.unit.sum (literalSignEncoding.sum literalSignEncoding))

def litFinish (r : Registers 10) (l : Literal) (rest : Word) : Registers 10 :=
  StackMachine.set (StackMachine.set (StackMachine.set r input rest) output
    (encodeBinaryLiteral (toBinary l) ++ r output)) litCount (true :: r litCount)

/-- The partial register semantics of `literal`. -/
def litStep (r : Registers 10) : Option (Registers 10) :=
  match readLiteral (r input) with
  | none => none
  | some (l, rest) => some (litFinish r l rest)

theorem emitLiteral_success (s : Bool) (v : Nat) (rest : Word) (r : Registers 10)
    (hc : Clean r) (hi : r input = writeNat v ++ rest) :
    ∃ t, t ≤ v * (4 * v + 5) + 9 * v + 18 ∧
      Exec (emitLiteral s) (emitLiteral s).start r t (true, litFinish r ⟨v, s⟩ rest) := by
  have h₁ := exec_readUnary_encoded input var (by decide) v rest r hi
  let r₁ := StackMachine.set (StackMachine.set r input rest) var (List.replicate v true)
  obtain ⟨t₂, ht₂, h₂⟩ := exec_toBinary_nil var digits carry (by decide) (by decide) (by decide)
    v r₁ (by simp [r₁]) (by simp [r₁, hc.carry_eq, carry, var, input])
    (by simp [r₁, hc.digits_eq, digits, var, input])
  let r₂ := StackMachine.set (StackMachine.set r₁ var []) digits (binOf v)
  have h₃ := exec_transfer digits temp (by decide) r₂
  let r₃ := StackMachine.set (StackMachine.set r₂ digits []) temp ((r₂ digits).reverse ++ r₂ temp)
  have h₄ := exec_scatter temp output width (by decide) (by decide) (by decide) true true r₃
  let r₄ := StackMachine.set (StackMachine.set (StackMachine.set r₃ temp []) output
    ((r₃ temp).reverse ++ r₃ output)) width ((r₃ temp).reverse.map (mapBit true true) ++ r₃ width)
  have h₅ := exec_push output false r₄
  let r₅ := StackMachine.set r₄ output (false :: r₄ output)
  have h₆ := exec_transfer width output (by decide) r₅
  let r₆ := StackMachine.set (StackMachine.set r₅ width []) output ((r₅ width).reverse ++ r₅ output)
  have h₇ := exec_push output s r₆
  let r₇ := StackMachine.set r₆ output (s :: r₆ output)
  have h₈ := exec_push litCount true r₇
  have he := exec_seq _ _ h₁ (exec_seq _ _ h₂ (exec_seq _ _ h₃ (exec_seq _ _ h₄
    (exec_seq _ _ h₅ (exec_seq _ _ h₆ (exec_seq _ _ h₇ h₈))))))
  have hd₂ : r₂ digits = binOf v := by simp [r₂]
  have ht₂' : r₂ temp = [] := by simp [r₂, r₁, hc.temp_eq, temp, digits, var, input]
  have hw₂ : r₂ width = [] := by simp [r₂, r₁, hc.width_eq, width, digits, var, input]
  have hout : StackMachine.set r₇ litCount (true :: r₇ litCount) = litFinish r ⟨v, s⟩ rest := by
    apply regs_ext <;>
      simp [r₇, r₆, r₅, r₄, r₃, r₂, r₁, litFinish, toBinary, encodeBinaryLiteral, writeList,
        writeValues_bits, map_ones, hc.var_eq, hc.digits_eq, hc.carry_eq, hc.temp_eq,
        hc.width_eq, input, output, litCount, var, digits, temp, width,
        writeNat_eq, List.append_assoc]
  rw [hout] at he
  refine ⟨_, ?_, he⟩
  have hL := length_binOf_le v
  have e1 : (r var).length = 0 := by rw [hc.var_eq]; rfl
  have e3 : r₃ temp = (binOf v).reverse := by
    simp only [r₃, StackMachine.set_same, hd₂, ht₂', List.append_nil]
  have e4 : r₃ width = [] := by
    simp only [r₃, StackMachine.set_other _ (by decide : width ≠ temp),
      StackMachine.set_other _ (by decide : width ≠ digits), hw₂]
  have e5 : (r₅ width).length = (binOf v).length := by
    simp only [r₅, r₄, StackMachine.set_other _ (by decide : width ≠ output),
      StackMachine.set_same, e3, e4, List.append_nil, List.length_map, List.length_reverse]
  rw [e1, hd₂, e3, e5, List.length_reverse]
  omega

theorem literalSign_success (s : Bool) (v : Nat) (rest : Word) (r : Registers 10)
    (hc : Clean r) (hi : r input = s :: (writeNat v ++ rest)) :
    ∃ t, t ≤ v * (4 * v + 5) + 9 * v + 20 ∧
      Exec (literalSign s) (literalSign s).start r t (true, litFinish r ⟨v, s⟩ rest) := by
  let r₀ := StackMachine.set r input (writeNat v ++ rest)
  have hp : Exec (pop input) false r 2 (true, r₀) := by
    simpa [hi, r₀] using exec_pop input r
  have hc₀ : Clean r₀ := hc.set input (by decide) (by decide) (by decide) (by decide)
    (by decide) _
  obtain ⟨t, ht, he⟩ := emitLiteral_success s v rest r₀ hc₀ (by simp [r₀])
  have hh := exec_seq _ _ hp he
  have hout : litFinish r₀ ⟨v, s⟩ rest = litFinish r ⟨v, s⟩ rest := by
    apply regs_ext <;> simp [litFinish, r₀, input, output, litCount]
  rw [hout] at hh
  exact ⟨2 + t, by omega, hh⟩

/-- `literal` realizes `litStep`, within a quadratic bound. -/
def litCost (bound : Nat) : Nat := bound * (4 * bound + 5) + 11 * bound + 21

theorem literal_runs (bound : Nat) (r : Registers 10) (hc : Clean r)
    (hb : (r input).length ≤ bound) :
    ∃ t b out, t ≤ litCost bound ∧ Exec literal literal.start r t (b, out) ∧
      Realizes (litStep r) b out := by
  cases hr : r input with
  | nil =>
    refine ⟨2, false, r, by unfold litCost; omega, ?_, by simp [litStep, hr, readLiteral]⟩
    exact exec_peekCase_empty input (stop 10 false) (literalSign false) (literalSign true) hr
      (exec_stop 10 false r)
  | cons s rest =>
    cases hn : readNat rest with
    | none =>
      have hall := readNat_none_eq hn
      let r₀ := StackMachine.set r input rest
      have hp : Exec (pop input) false r 2 (true, r₀) := by
        simpa [hr, r₀] using exec_pop input r
      have hu := exec_readUnary_malformed input var (by decide) rest.length r₀
        (by simpa [r₀] using hall)
      have hf := exec_seq _ _ hp (exec_seq_failure _ (seq (toBinaryProg var digits carry)
        (seq (transfer digits temp) (seq (scatter temp output width true true)
        (seq (push output false) (seq (transfer width output)
        (seq (push output s) (push litCount true))))))) hu)
      have hv : (r₀ var).length = 0 := by simp [r₀, hc.var_eq, var, input]
      rw [hv] at hf
      have hlen : rest.length ≤ bound := by rw [hr] at hb; simp at hb; omega
      cases s with
      | false =>
        have hh := exec_peekCase_zero input (stop 10 false) (literalSign false)
          (literalSign true) hr hf
        refine ⟨_, false, _, ?_, hh, by simp [litStep, hr, readLiteral, hn]⟩
        unfold litCost; omega
      | true =>
        have hh := exec_peekCase_one input (stop 10 false) (literalSign false)
          (literalSign true) hr hf
        refine ⟨_, false, _, ?_, hh, by simp [litStep, hr, readLiteral, hn]⟩
        unfold litCost; omega
    | some pair =>
      obtain ⟨v, tail⟩ := pair
      have hrest := readNat_eq_some hn
      have hv : v ≤ bound := by
        rw [hr, hrest] at hb
        simp [SATBounds.writeNat_length] at hb
        omega
      have hlit : readLiteral (r input) = some (⟨v, s⟩, tail) := by
        simp [hr, readLiteral, hn]
      obtain ⟨t, ht, he⟩ := literalSign_success s v tail r hc (by rw [hr, hrest])
      have hcost : t + 1 ≤ litCost bound := by
        have hm := Nat.mul_le_mul hv (show 4 * v + 5 ≤ 4 * bound + 5 by omega)
        unfold litCost; omega
      cases s with
      | false =>
        have hh := exec_peekCase_zero input (stop 10 false) (literalSign false)
          (literalSign true) hr he
        exact ⟨_, true, _, hcost, hh, by simp [litStep, hlit]⟩
      | true =>
        have hh := exec_peekCase_one input (stop 10 false) (literalSign false)
          (literalSign true) hr he
        exact ⟨_, true, _, hcost, hh, by simp [litStep, hlit]⟩

end Complexity.Binary.Reduce
