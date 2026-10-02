module

public import Complexity.ThreeSAT
public import Complexity.SATBounds

/-!
# Finite certificates for SAT and 3-SAT

The executable verifiers below decode an input word and evaluate the resulting
formula using a finite Boolean certificate. Missing certificate positions have
value `false`. Every satisfying assignment has a finite certificate agreeing on
all occurring variables. This file proves semantic correctness and certificate
length bounds only; no machine running-time claim is made.
-/

@[expose] public section

namespace Complexity.SATVerifier

open Complexity.SAT

/-- Interpret a finite certificate as an assignment, defaulting to false. -/
def assignment (certificate : Word) : Assignment :=
  fun i => certificate[i]?.getD false

/-- Restrict an assignment to its first `n` values. -/
def certificateOf (a : Assignment) (n : Nat) : Word :=
  List.ofFn (fun i : Fin n => a i.val)

@[simp] theorem certificateOf_length (a : Assignment) (n : Nat) :
    (certificateOf a n).length = n := by
  simp [certificateOf]

theorem assignment_certificateOf (a : Assignment) {n i : Nat} (h : i < n) :
    assignment (certificateOf a n) i = a i := by
  simp [assignment, certificateOf, h]

theorem evalCNF_certificateOf (a : Assignment) (f : CNF) :
    evalCNF (assignment (certificateOf a (variableBound f))) f = evalCNF a f := by
  apply Complexity.ThreeSAT.evalCNF_agrees (Complexity.ThreeSAT.input_below_bound f)
  intro i hi
  exact assignment_certificateOf a hi

/-- Decode a word and check its clauses under the finite certificate. -/
def verify (input certificate : Word) : Bool :=
  match decode input with
  | none => false
  | some f => evalCNF (assignment certificate) f

@[simp] theorem verify_encode (f : CNF) (certificate : Word) :
    verify (encode f) certificate = evalCNF (assignment certificate) f := by
  simp [verify]

theorem verify_rejects_malformed {input : Word} (h : decode input = none)
    (certificate : Word) : verify input certificate = false := by
  simp [verify, h]

theorem verify_sound {input certificate : Word}
    (h : verify input certificate = true) : SAT input := by
  cases hd : decode input with
  | none => simp [verify, hd] at h
  | some f =>
    exact (SAT_iff_decode input).mpr
      ⟨f, hd, assignment certificate, by simpa [verify, hd] using h⟩

theorem verify_complete_encoded {f : CNF} (h : Satisfiable f) :
    ∃ certificate : Word,
      certificate.length = variableBound f ∧ verify (encode f) certificate = true := by
  obtain ⟨a, ha⟩ := h
  refine ⟨certificateOf a (variableBound f), certificateOf_length .., ?_⟩
  simpa [evalCNF_certificateOf] using ha

/-- Every SAT instance has a certificate no longer than its binary encoding. -/
theorem verify_complete {input : Word} (h : SAT input) :
    ∃ certificate : Word,
      certificate.length ≤ input.length ∧ verify input certificate = true := by
  obtain ⟨f, hf, hs⟩ := (SAT_iff_decode input).mp h
  have hinput := (Complexity.SAT.decode_eq_some_iff input f).mp hf
  obtain ⟨certificate, hlen, hc⟩ := verify_complete_encoded hs
  refine ⟨certificate, ?_, ?_⟩
  · rw [hlen, hinput]
    exact Complexity.SATBounds.variableBound_le_encode_length f
  · simpa [hinput] using hc

/-- Semantic certificate characterization; machine runtime remains separate. -/
theorem SAT_iff_exists_certificate (input : Word) :
    SAT input ↔ ∃ certificate : Word,
      certificate.length ≤ input.length ∧ verify input certificate = true := by
  constructor
  · exact verify_complete
  · rintro ⟨certificate, _, hc⟩
    exact verify_sound hc

/-- Check the clause-width condition and satisfiability certificate together. -/
def verifyThree (input certificate : Word) : Bool :=
  match decode input with
  | none => false
  | some f => f.all (fun c => decide (c.length ≤ 3)) && evalCNF (assignment certificate) f

theorem verifyThree_rejects_malformed {input : Word} (h : decode input = none)
    (certificate : Word) : verifyThree input certificate = false := by
  simp [verifyThree, h]

theorem verifyThree_sound {input certificate : Word}
    (h : verifyThree input certificate = true) : ThreeSAT input := by
  cases hd : decode input with
  | none => simp [verifyThree, hd] at h
  | some f =>
    have hh : f.all (fun c => decide (c.length ≤ 3)) = true ∧
        evalCNF (assignment certificate) f = true := by
      simpa [verifyThree, hd] using h
    refine (ThreeSAT_iff_decode input).mpr ⟨f, hd, ?_, assignment certificate, hh.2⟩
    simpa [IsThreeCNF] using hh.1

theorem verifyThree_complete_encoded {f : CNF}
    (h₃ : IsThreeCNF f) (hs : Satisfiable f) :
    ∃ certificate : Word, certificate.length = variableBound f ∧
      verifyThree (encode f) certificate = true := by
  obtain ⟨a, ha⟩ := hs
  refine ⟨certificateOf a (variableBound f), certificateOf_length .., ?_⟩
  have hall : f.all (fun c => decide (c.length ≤ 3)) = true := by
    simpa [IsThreeCNF] using h₃
  simp [verifyThree, hall, evalCNF_certificateOf, ha]

/-- Every 3-SAT instance has a certificate no longer than its binary encoding. -/
theorem verifyThree_complete {input : Word} (h : ThreeSAT input) :
    ∃ certificate : Word,
      certificate.length ≤ input.length ∧ verifyThree input certificate = true := by
  obtain ⟨f, hf, h₃, hs⟩ := (ThreeSAT_iff_decode input).mp h
  have hinput := (Complexity.SAT.decode_eq_some_iff input f).mp hf
  obtain ⟨certificate, hlen, hc⟩ := verifyThree_complete_encoded h₃ hs
  refine ⟨certificate, ?_, ?_⟩
  · rw [hlen, hinput]
    exact Complexity.SATBounds.variableBound_le_encode_length f
  · simpa [hinput] using hc

/-- Semantic certificate characterization; machine runtime remains separate. -/
theorem ThreeSAT_iff_exists_certificate (input : Word) :
    ThreeSAT input ↔ ∃ certificate : Word,
      certificate.length ≤ input.length ∧ verifyThree input certificate = true := by
  constructor
  · exact verifyThree_complete
  · rintro ⟨certificate, _, hc⟩
    exact verifyThree_sound hc

end Complexity.SATVerifier
