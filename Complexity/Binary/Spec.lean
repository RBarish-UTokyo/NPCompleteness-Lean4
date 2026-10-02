module

public import Complexity.Binary.Basic
import Lean.Elab.Tactic.Omega

/-!
# The reduction and the verifier as pure functions

* `reduceWord`: SAT to binary SAT. A malformed word goes to one empty clause; a formula goes
  to the formula with the clause order and the literal order of every clause reversed (the
  order in which a stack transducer emits them) and every variable written in binary.
* `verify`: the certificate has one bit per literal occurrence, in order. The verifier
  accepts iff the word is a formula, the certificate is long enough, every clause has an
  occurrence whose bit agrees with its sign, and occurrences naming the same variable carry
  equal bits.
-/

@[expose] public section

namespace Complexity.Binary

open Complexity.SAT

/-! ## The reduction -/

/-- Write the variable of a literal in binary. -/
def toBinary (l : Literal) : BinaryLiteral := ⟨binOf l.var, l.positive⟩

@[simp] theorem toLiteral_toBinary (l : Literal) : (toBinary l).toLiteral = l := by
  cases l
  simp [toBinary, BinaryLiteral.toLiteral]

/-- A clause, literals reversed and written in binary. -/
def binaryClause (c : Clause) : List BinaryLiteral := (c.map toBinary).reverse

/-- A formula, clauses reversed, each clause as `binaryClause`. -/
def binaryCNF (f : CNF) : List (List BinaryLiteral) := (f.map binaryClause).reverse

theorem binaryCNF_toLiteral (f : CNF) :
    (binaryCNF f).map (List.map BinaryLiteral.toLiteral) = (f.map List.reverse).reverse := by
  simp [binaryCNF, binaryClause, List.map_reverse, Function.comp_def]

theorem evalCNF_reverse_reverse (a : Assignment) (f : CNF) :
    evalCNF a ((f.map List.reverse).reverse) = evalCNF a f := by
  unfold evalCNF
  rw [List.all_reverse, List.all_map]
  congr 1
  funext c
  simp [evalClause]

/-- The reduction from SAT to binary SAT, as a function on words. -/
def reduceWord (input : Word) : Word :=
  match decode input with
  | none => encodeBinary [[]]
  | some f => encodeBinary (binaryCNF f)

theorem reduceWord_correct (input : Word) : SAT input ↔ BinarySAT (reduceWord input) := by
  cases hd : decode input with
  | none =>
    simp only [reduceWord, hd, BinarySAT_encodeBinary_iff]
    constructor
    · intro h
      exact absurd h (not_SAT_of_decode_none hd)
    · intro h
      exact absurd h (by simpa using not_satisfiable_empty_clause [])
  | some f =>
    have hin := (decode_eq_some_iff input f).mp hd
    subst hin
    simp only [reduceWord, hd, BinarySAT_encodeBinary_iff, SAT_encode_iff, binaryCNF_toLiteral]
    constructor
    · rintro ⟨a, ha⟩
      exact ⟨a, by rw [evalCNF_reverse_reverse]; exact ha⟩
    · rintro ⟨a, ha⟩
      exact ⟨a, by rw [evalCNF_reverse_reverse] at ha; exact ha⟩

/-! ## The verifier -/

/-- Give each literal of a clause the next certificate bit. -/
def labelClause : List BinaryLiteral → Word → Option (List (BinaryLiteral × Bool) × Word)
  | [], w => some ([], w)
  | _ :: _, [] => none
  | l :: c, b :: w => do
      let (lc, rest) ← labelClause c w
      pure ((l, b) :: lc, rest)

/-- Give each literal occurrence of a formula the next certificate bit. -/
def labelCNF : List (List BinaryLiteral) → Word →
    Option (List (List (BinaryLiteral × Bool)) × Word)
  | [], w => some ([], w)
  | c :: f, w => do
      let (lc, rest) ← labelClause c w
      let (lf, tail) ← labelCNF f rest
      pure (lc :: lf, tail)

/-- Some occurrence of the clause carries a bit equal to its sign. -/
def clauseOK (c : List (BinaryLiteral × Bool)) : Bool :=
  c.any (fun p => p.2 == p.1.positive)

/-- The bit of an occurrence and the normal form of its digits. -/
def entry (p : BinaryLiteral × Bool) : Bool × List Bool := (p.2, norm p.1.bits)

/-- Two entries with the same normal form carry the same bit. -/
def compatible (e₁ e₂ : Bool × List Bool) : Bool :=
  !(decide (e₁.2 = e₂.2)) || (e₁.1 == e₂.1)

/-- All pairs of entries are compatible. -/
def consistent (es : List (Bool × List Bool)) : Bool :=
  es.all (fun e₁ => es.all (compatible e₁))

/-- The certificate verifier for binary SAT, as a pure function. -/
def verify (input certificate : Word) : Bool :=
  match decodeBinary input with
  | none => false
  | some f =>
    match labelCNF f certificate with
    | none => false
    | some (g, _) => g.all clauseOK && consistent (g.flatten.map entry)

theorem labelClause_fst {c : List BinaryLiteral} {w : Word} {lc rest}
    (h : labelClause c w = some (lc, rest)) : lc.map Prod.fst = c := by
  induction c generalizing w lc rest with
  | nil =>
    simp only [labelClause, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl
  | cons l c ih =>
    cases w with
    | nil => simp [labelClause] at h
    | cons b w =>
      cases hc : labelClause c w with
      | none => simp [labelClause, hc] at h
      | some pair =>
        obtain ⟨lc', rest'⟩ := pair
        simp only [labelClause, hc, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
          Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        simp [ih hc]

theorem labelCNF_fst {f : List (List BinaryLiteral)} {w : Word} {g rest}
    (h : labelCNF f w = some (g, rest)) : g.map (List.map Prod.fst) = f := by
  induction f generalizing w g rest with
  | nil =>
    simp only [labelCNF, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl
  | cons c f ih =>
    cases hc : labelClause c w with
    | none => simp [labelCNF, hc] at h
    | some pair =>
      obtain ⟨lc, mid⟩ := pair
      cases hf : labelCNF f mid with
      | none => simp [labelCNF, hc, hf] at h
      | some pair =>
        obtain ⟨lf, tail⟩ := pair
        simp only [labelCNF, hc, hf, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
          Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        simp [labelClause_fst hc, ih hf]

theorem labelClause_map (c : List BinaryLiteral) (h : BinaryLiteral → Bool) (rest : Word) :
    labelClause c (c.map h ++ rest) = some (c.map (fun l => (l, h l)), rest) := by
  induction c with
  | nil => rfl
  | cons l c ih => simp [labelClause, ih]

theorem labelCNF_map (f : List (List BinaryLiteral)) (h : BinaryLiteral → Bool) (rest : Word) :
    labelCNF f (f.flatten.map h ++ rest) = some (f.map (List.map (fun l => (l, h l))), rest) := by
  induction f with
  | nil => rfl
  | cons c f ih =>
    rw [List.flatten_cons, List.map_append, List.append_assoc]
    simp only [labelCNF, labelClause_map, ih, List.map_cons, Option.bind_eq_bind,
      Option.bind_some, Option.pure_def]

/-- The assignment read off an accepted certificate: the bit of the first occurrence of each
variable, and `false` for variables that do not occur. -/
def assignmentOf (occurrences : List (BinaryLiteral × Bool)) : Assignment := fun v =>
  match occurrences.find? (fun p => binaryValue p.1.bits == v) with
  | some p => p.2
  | none => false

theorem assignmentOf_eq {occ : List (BinaryLiteral × Bool)}
    (hc : consistent (occ.map entry) = true) {p : BinaryLiteral × Bool} (hp : p ∈ occ) :
    assignmentOf occ (binaryValue p.1.bits) = p.2 := by
  unfold assignmentOf
  cases hf : occ.find? (fun q => binaryValue q.1.bits == binaryValue p.1.bits) with
  | none =>
    have := List.find?_eq_none.mp hf p hp
    simp at this
  | some q =>
    have hq := List.mem_of_find?_eq_some hf
    have hv : binaryValue q.1.bits = binaryValue p.1.bits := by
      simpa using List.find?_some hf
    have hn : norm q.1.bits = norm p.1.bits := (norm_eq_norm_iff _ _).mpr hv
    have hall : ∀ e₁ ∈ occ.map entry, ∀ e₂ ∈ occ.map entry, compatible e₁ e₂ = true := by
      intro e₁ h₁ e₂ h₂
      exact List.all_eq_true.mp (List.all_eq_true.mp hc e₁ h₁) e₂ h₂
    have hcomp := hall (entry q) (List.mem_map_of_mem hq) (entry p) (List.mem_map_of_mem hp)
    simp only [compatible, entry, hn, decide_true, Bool.not_true, Bool.false_or,
      beq_iff_eq] at hcomp
    simp [hcomp]

theorem verify_sound {input certificate : Word} (h : verify input certificate = true) :
    BinarySAT input := by
  cases hd : decodeBinary input with
  | none => simp [verify, hd] at h
  | some f =>
    cases hl : labelCNF f certificate with
    | none => simp [verify, hd, hl] at h
    | some pair =>
      obtain ⟨g, rest⟩ := pair
      have hh : g.all clauseOK = true ∧ consistent (g.flatten.map entry) = true := by
        simpa [verify, hd, hl] using h
      refine (BinarySAT_iff_decode input).mpr ⟨f, hd, assignmentOf g.flatten, ?_⟩
      rw [← labelCNF_fst hl]
      simp only [evalCNF, List.all_map, List.all_eq_true, Function.comp_apply]
      intro c hc
      have hok : clauseOK c = true := List.all_eq_true.mp hh.1 c hc
      obtain ⟨p, hp, hbit⟩ := List.any_eq_true.mp hok
      simp only [evalClause, List.map_map, List.any_map, List.any_eq_true, Function.comp_apply]
      refine ⟨p, hp, ?_⟩
      have hflat : p ∈ g.flatten := List.mem_flatten.mpr ⟨c, hc, hp⟩
      have hv := assignmentOf_eq hh.2 hflat
      have hb : p.2 = p.1.positive := by simpa using hbit
      simp only [evalLiteral, BinaryLiteral.toLiteral]
      rw [hv, hb]
      by_cases hpos : p.1.positive = true <;> simp [hpos]

theorem flatten_length_le_encodeBinary (f : List (List BinaryLiteral)) :
    f.flatten.length ≤ (encodeBinary f).length := by
  have hclause : ∀ c : List BinaryLiteral, c.length ≤ (encodeBinaryClause c).length := by
    intro c
    simp only [encodeBinaryClause, writeList, List.length_append, SATBounds.writeNat_length]
    omega
  have hvalues : ∀ g : List (List BinaryLiteral),
      g.flatten.length ≤ (writeValues encodeBinaryClause g).length := by
    intro g
    induction g with
    | nil => simp [writeValues]
    | cons c g ih =>
      simp only [List.flatten_cons, List.length_append, writeValues]
      have := hclause c
      omega
  have := hvalues f
  simp only [encodeBinary_eq, writeList, List.length_append, SATBounds.writeNat_length]
  omega

theorem verify_complete {input : Word} (h : BinarySAT input) :
    ∃ certificate : Word,
      certificate.length ≤ input.length ∧ verify input certificate = true := by
  obtain ⟨f, rfl, a, ha⟩ := h
  let bit : BinaryLiteral → Bool := fun l => a (binaryValue l.bits)
  refine ⟨f.flatten.map bit, ?_, ?_⟩
  · rw [List.length_map]; exact flatten_length_le_encodeBinary f
  · have hl := labelCNF_map f bit []
    simp only [List.append_nil] at hl
    simp only [verify, decodeBinary_encode, hl, Bool.and_eq_true]
    constructor
    · simp only [evalCNF, List.all_map, List.all_eq_true, Function.comp_apply] at ha
      simp only [List.all_map, List.all_eq_true, Function.comp_apply]
      intro c hc
      have hcl := ha c hc
      simp only [evalClause, List.any_map, List.any_eq_true, Function.comp_apply] at hcl
      obtain ⟨l, hl, hev⟩ := hcl
      simp only [clauseOK, List.any_map, List.any_eq_true, Function.comp_apply]
      refine ⟨l, hl, ?_⟩
      cases hpos : l.positive <;>
        simp_all [evalLiteral, BinaryLiteral.toLiteral, bit]
    · have key : ∀ p ∈ (f.map (List.map fun l => (l, bit l))).flatten, p.2 = bit p.1 := by
        intro p hp
        obtain ⟨c, hc, hpc⟩ := List.mem_flatten.mp hp
        obtain ⟨c', _, rfl⟩ := List.mem_map.mp hc
        obtain ⟨l, _, rfl⟩ := List.mem_map.mp hpc
        rfl
      unfold consistent
      rw [List.all_eq_true]
      intro e₁ h₁
      rw [List.all_eq_true]
      intro e₂ h₂
      obtain ⟨p₁, hp₁, rfl⟩ := List.mem_map.mp h₁
      obtain ⟨p₂, hp₂, rfl⟩ := List.mem_map.mp h₂
      simp only [compatible, entry, key p₁ hp₁, key p₂ hp₂]
      by_cases hn : norm p₁.1.bits = norm p₂.1.bits
      · simp [bit, (norm_eq_norm_iff _ _).mp hn]
      · simp [hn]

/-- Semantic certificate characterization of binary SAT. -/
theorem BinarySAT_iff_exists_certificate (input : Word) :
    BinarySAT input ↔ ∃ certificate : Word,
      certificate.length ≤ input.length ∧ verify input certificate = true := by
  constructor
  · exact verify_complete
  · rintro ⟨certificate, _, hc⟩
    exact verify_sound hc

end Complexity.Binary
