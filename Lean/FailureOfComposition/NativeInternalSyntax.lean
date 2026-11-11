/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import FailureOfComposition.NativeProofChecker
public import Foundation.FirstOrder.Arithmetic.HFS.PRF

/-!
# Internal syntax operations for the native proof checker

This module separates the three assumptions placed on an axiom-bit graph.
The graph has output-first coordinates `(bit, formulaCode)`, and the bit
convention is `0` for rejection and `1` for acceptance.  Computational
interpretation concerns every element of a PA model.  Theory agreement and
the comparison with a numerical axiom test concern only valid formula codes.

The remaining definitions internalize the guarded syntax operations used by
`NativeProofChecker`.  In particular, an invalid formula shifts to zero, and
the sequent shift maps every coded member through that guarded operation.
Thus its behavior on malformed finite sets is fixed independently of
Foundation's unguarded `setShift`.
-/

@[expose] public section

set_option autoImplicit false

open Encodable FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic

namespace FailureOfComposition.NativeInternalSyntax

open FFL.FirstOrder.Arithmetic.Bootstrapping
open FailureOfComposition.NativeContextMP
open FailureOfComposition.NativeSubstitution
open FailureOfComposition.NativeSyntaxShift

/-- Interpret an external Boolean as the numerical bit `0` or `1`. -/
def boolBit (b : Bool) : ℕ := if b then 1 else 0

@[simp] theorem boolBit_false : boolBit false = 0 := rfl

@[simp] theorem boolBit_true : boolBit true = 1 := rfl

/-- A two-place Sigma-one formula computes one Boolean bit at every input.
The coordinates are `(bit, formulaCode)`. -/
structure ComputationalAxiomGraph
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (A : 𝚺₁.Semisentence 2) : Prop where
  existsUnique : ∀ a : V, ∃! b : V,
    Semiformula.Evalb (M := V) ![b, a] A.val
  bit : ∀ {b a : V}, Semiformula.Evalb (M := V) ![b, a] A.val →
    b = 0 ∨ b = 1

/-- Agreement of an axiom-bit graph with a theory is required only at valid
formula codes. -/
def TheoryAxiomAgreement
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (A : 𝚺₁.Semisentence 2) (S : ArithmeticTheory) [S.Δ₁] : Prop :=
  ∀ a : V, IsFormula ℒₒᵣ a →
    (Semiformula.Evalb (M := V) ![1, a] A.val ↔
      a ∈ S.Δ₁Class)

/-- Full-domain numerical comparison needs the supplied executable axiom test
only at valid formula codes. -/
def NumericalAxiomAgreement (A : 𝚺₁.Semisentence 2)
    (ax : ℕ → Bool) : Prop :=
  ∀ a : ℕ, IsFormula ℒₒᵣ a →
    Semiformula.Evalb (M := ℕ) ![boolBit (ax a), a] A.val

/-- The value selected by a computational axiom-bit graph. -/
noncomputable def axiomBitValue
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    {A : 𝚺₁.Semisentence 2} (hA : ComputationalAxiomGraph (V := V) A)
    (a : V) : V :=
  Classical.choose! (hA.existsUnique a)

theorem axiomBitValue_spec
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    {A : 𝚺₁.Semisentence 2} (hA : ComputationalAxiomGraph (V := V) A)
    (a : V) :
    Semiformula.Evalb (M := V) ![axiomBitValue hA a, a] A.val :=
  Classical.choose!_spec (hA.existsUnique a)

theorem axiomBitValue_eq_iff
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    {A : 𝚺₁.Semisentence 2} (hA : ComputationalAxiomGraph (V := V) A)
    (b a : V) :
    Semiformula.Evalb (M := V) ![b, a] A.val ↔
      b = axiomBitValue hA a := by
  constructor
  · intro hb
    exact (hA.existsUnique a).unique hb (axiomBitValue_spec hA a)
  · rintro rfl
    exact axiomBitValue_spec hA a

theorem axiomBitValue_isBit
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    {A : 𝚺₁.Semisentence 2} (hA : ComputationalAxiomGraph (V := V) A)
    (a : V) : axiomBitValue hA a = 0 ∨ axiomBitValue hA a = 1 :=
  hA.bit (axiomBitValue_spec hA a)

/-! ## Guarded formula shift -/

/-- Internal guarded shift at bound arity `n`. -/
noncomputable def formulaShiftValue
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (n p : V) : V :=
  @ite V (IsSemiformula ℒₒᵣ n p) (Classical.propDecidable _)
    (shift ℒₒᵣ p) 0

/-- Exact output-first graph `(output,input)` of the guarded shift at arity
`n`.  Both `n=0` and `n=1` are used by the checker. -/
noncomputable def formulaShiftGraph (n : ℕ) : 𝚺₁.Semisentence 2 := .mkSigma
  “y p.
    ((!(isSemiformula ℒₒᵣ).sigma ↑n p ∧
      !(shiftGraph ℒₒᵣ) y p) ∨
    (¬!(isSemiformula ℒₒᵣ).pi ↑n p ∧ y = 0))”

theorem formulaShiftGraph_iff
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (n : ℕ) (y p : V) :
    Semiformula.Evalb (M := V) ![y, p] (formulaShiftGraph n).val ↔
      y = formulaShiftValue (n : V) p := by
  by_cases hp : IsSemiformula ℒₒᵣ (n : V) p <;>
    simp [formulaShiftGraph, formulaShiftValue, numeral_eq_natCast, hp,
      HierarchySymbol.Semiformula.val_sigma,
      IsSemiformula.defined.iff, shift.defined.iff]

theorem formulaShiftGraph_total
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (n : ℕ) (p : V) :
    ∃ y : V, Semiformula.Evalb (M := V) ![y, p]
      (formulaShiftGraph n).val :=
  ⟨formulaShiftValue (n : V) p,
    (formulaShiftGraph_iff n _ _).mpr rfl⟩

theorem formulaShiftGraph_functional
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (n : ℕ) {y z p : V}
    (hy : Semiformula.Evalb (M := V) ![y, p]
      (formulaShiftGraph n).val)
    (hz : Semiformula.Evalb (M := V) ![z, p]
      (formulaShiftGraph n).val) : y = z :=
  (formulaShiftGraph_iff n y p).mp hy |>.trans
    ((formulaShiftGraph_iff n z p).mp hz).symm

theorem formulaShiftValue_eq_shift
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    {n p : V} (hp : IsSemiformula ℒₒᵣ n p) :
    formulaShiftValue n p = shift ℒₒᵣ p := by
  simp [formulaShiftValue, hp]

theorem formulaShiftValue_eq_zero_of_invalid
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    {n p : V} (hp : ¬IsSemiformula ℒₒᵣ n p) :
    formulaShiftValue n p = 0 := by
  simp [formulaShiftValue, hp]

theorem formulaShiftValue_nat (n p : ℕ) :
    formulaShiftValue n p = formulaShiftCode n p := by
  by_cases hp : IsSemiformula ℒₒᵣ n p
  · rw [formulaShiftValue_eq_shift hp,
      ← formulaShiftCode_eq_shift hp]
  · rw [formulaShiftValue_eq_zero_of_invalid hp,
      formulaShiftCode_eq_zero_of_invalid hp]

theorem formulaShiftGraph_nat_iff (n y p : ℕ) :
    Semiformula.Evalb (M := ℕ) ![y, p] (formulaShiftGraph n).val ↔
      y = formulaShiftCode n p := by
  simpa only [natCast_nat, formulaShiftValue_nat] using
    (formulaShiftGraph_iff (V := ℕ) n y p)

/-! ## Free body and guarded sequent image -/

/-- The internal counterpart of `formulaFreeCode`. -/
noncomputable def formulaFreeValue
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (p : V) : V :=
  subst1Value ^&0 (formulaShiftValue 1 p)

/-- Exact output-first graph `(output,body)` of `formulaFreeValue`. -/
noncomputable def formulaFreeGraph : 𝚺₁.Semisentence 2 := .mkSigma
  “y p. ∃ fz, !qqFvarDef fz 0 ∧
    ∃ sp, !(formulaShiftGraph 1).val sp p ∧
      !subst1Graph y fz sp”

theorem formulaFreeGraph_iff
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (y p : V) :
    Semiformula.Evalb (M := V) ![y, p] formulaFreeGraph.val ↔
      y = formulaFreeValue p := by
  simp [formulaFreeGraph, formulaFreeValue, formulaShiftGraph_iff,
    subst1Graph_iff]

theorem formulaFreeGraph_total
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (p : V) :
    ∃ y : V, Semiformula.Evalb (M := V) ![y, p]
      formulaFreeGraph.val :=
  ⟨formulaFreeValue p, (formulaFreeGraph_iff _ _).mpr rfl⟩

theorem formulaFreeGraph_functional
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    {y z p : V}
    (hy : Semiformula.Evalb (M := V) ![y, p] formulaFreeGraph.val)
    (hz : Semiformula.Evalb (M := V) ![z, p] formulaFreeGraph.val) :
    y = z :=
  (formulaFreeGraph_iff y p).mp hy |>.trans
    ((formulaFreeGraph_iff z p).mp hz).symm

theorem formulaFreeValue_eq_free
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    {p : V} (hp : IsSemiformula ℒₒᵣ 1 p) :
    formulaFreeValue p = free ℒₒᵣ p := by
  rw [formulaFreeValue, formulaShiftValue_eq_shift hp]
  simp [free, subst1Value, hp.shift]

theorem formulaFreeValue_nat (p : ℕ) :
    formulaFreeValue p = formulaFreeCode p := by
  simp only [formulaFreeValue, formulaFreeCode, subst1Value_nat,
    formulaShiftValue_nat]
  congr 1
  exact Semiterm.quote_eq_encode_standard (&0 : SyntacticTerm ℒₒᵣ)

theorem formulaFreeGraph_nat_iff (y p : ℕ) :
    Semiformula.Evalb (M := ℕ) ![y, p] formulaFreeGraph.val ↔
      y = formulaFreeCode p := by
  rw [formulaFreeGraph_iff, formulaFreeValue_nat]

private instance formulaShiftValue_defined
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (n : ℕ) :
    𝚺₁-Function₁[V] (formulaShiftValue (n : V)) via formulaShiftGraph n :=
  .mk fun v => by
    have hv : v = ![v 0, v 1] := by ext i; fin_cases i <;> rfl
    rw [hv]
    exact formulaShiftGraph_iff n (v 0) (v 1)

private instance formulaShiftValue_definable
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (n : ℕ) : 𝚺₁-Function₁[V] (formulaShiftValue (n : V)) :=
  (formulaShiftValue_defined n).to_definable

/-- Existence and uniqueness of the finite set obtained by mapping every
member of `s` through the guarded arity-zero formula shift. -/
theorem sequentShift_existsUnique
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (s : V) :
    ∃! t : V, ∀ y, y ∈ t ↔ ∃ x ∈ s,
      y = formulaShiftValue 0 x := by
  exact sigma₁_replacement (formulaShiftValue_definable 0) s

/-- Internal finite-set image under the guarded arity-zero shift. -/
noncomputable def sequentShiftValue
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (s : V) : V :=
  Classical.choose! (sequentShift_existsUnique s)

theorem mem_sequentShiftValue_iff
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    {s y : V} :
    y ∈ sequentShiftValue s ↔ ∃ x ∈ s,
      y = formulaShiftValue 0 x :=
  Classical.choose!_spec (sequentShift_existsUnique s) y

/-- Exact output-first graph `(output,sequent)` of the guarded finite-set
image. -/
noncomputable def sequentShiftGraph : 𝚺₁.Semisentence 2 := .mkSigma
  “t s.
    (∀ y ∈' t, ∃ x ∈' s, !(formulaShiftGraph 0).val y x) ∧
    (∀ x ∈' s, ∃ y, !(formulaShiftGraph 0).val y x ∧ y ∈ t)”

private theorem sequentShift_graph
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (t s : V) :
    t = sequentShiftValue s ↔
      (∀ y ∈ t, ∃ x ∈ s, y = formulaShiftValue 0 x) ∧
      (∀ x ∈ s, formulaShiftValue 0 x ∈ t) := by
  constructor
  · rintro rfl
    constructor
    · intro y hy
      exact mem_sequentShiftValue_iff.mp hy
    · intro x hx
      exact mem_sequentShiftValue_iff.mpr ⟨x, hx, rfl⟩
  · rintro ⟨h₁, h₂⟩
    apply mem_ext
    intro y
    constructor
    · intro hy
      exact mem_sequentShiftValue_iff.mpr (h₁ y hy)
    · intro hy
      rcases mem_sequentShiftValue_iff.mp hy with ⟨x, hx, rfl⟩
      exact h₂ x hx

theorem sequentShiftGraph_iff
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (t s : V) :
    Semiformula.Evalb (M := V) ![t, s] sequentShiftGraph.val ↔
      t = sequentShiftValue s := by
  simpa [sequentShiftGraph, formulaShiftGraph_iff] using
    (sequentShift_graph t s).symm

theorem sequentShiftGraph_total
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (s : V) :
    ∃ t : V, Semiformula.Evalb (M := V) ![t, s]
      sequentShiftGraph.val :=
  ⟨sequentShiftValue s, (sequentShiftGraph_iff _ _).mpr rfl⟩

theorem sequentShiftGraph_functional
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    {t u s : V}
    (ht : Semiformula.Evalb (M := V) ![t, s] sequentShiftGraph.val)
    (hu : Semiformula.Evalb (M := V) ![u, s] sequentShiftGraph.val) :
    t = u :=
  (sequentShiftGraph_iff t s).mp ht |>.trans
    ((sequentShiftGraph_iff u s).mp hu).symm

theorem sequentShiftValue_eq_setShift
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    {s : V} (hs : IsFormulaSet ℒₒᵣ s) :
    sequentShiftValue s = setShift ℒₒᵣ s := by
  apply mem_ext
  intro y
  rw [mem_sequentShiftValue_iff, mem_setShift_iff]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, formulaShiftValue_eq_shift (hs x hx)⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, (formulaShiftValue_eq_shift (hs x hx)).symm⟩

private theorem mem_shiftFold (s : ℕ) (l : List ℕ) (y : ℕ) :
    y ∈ l.foldr (fun p t => if s / 2 ^ p % 2 = 1 then
      sequentInsertCode (formulaShiftCode 0 p) t else t) 0 ↔
      ∃ p ∈ l, p ∈ s ∧ y = formulaShiftCode 0 p := by
  induction l with
  | nil => simp
  | cons p l ih =>
      by_cases hp : s / 2 ^ p % 2 = 1
      · rw [List.foldr_cons, ite_eq_left hp,
          show sequentInsertCode (formulaShiftCode 0 p)
            (l.foldr (fun p t => if s / 2 ^ p % 2 = 1 then
              sequentInsertCode (formulaShiftCode 0 p) t else t) 0) =
            insert (formulaShiftCode 0 p)
              (l.foldr (fun p t => if s / 2 ^ p % 2 = 1 then
                sequentInsertCode (formulaShiftCode 0 p) t else t) 0) from
            (nat_insert_eq _ _).symm,
          mem_bitInsert_iff, ih]
        simp only [List.mem_cons]
        constructor
        · rintro (h | ⟨q, hq, hqs, hy⟩)
          · exact ⟨p, Or.inl rfl, nat_mem_iff.mpr hp, h⟩
          · exact ⟨q, Or.inr hq, hqs, hy⟩
        · rintro ⟨q, (rfl | hq), hqs, hy⟩
          · exact Or.inl hy
          · exact Or.inr ⟨q, hq, hqs, hy⟩
      · simp only [List.foldr_cons, hp, ↓reduceIte, ih, List.mem_cons]
        constructor
        · rintro ⟨q, hq, hqs, hy⟩
          exact ⟨q, Or.inr hq, hqs, hy⟩
        · rintro ⟨q, (rfl | hq), hqs, hy⟩
          · exact False.elim (hp (nat_mem_iff.mp hqs))
          · exact ⟨q, hq, hqs, hy⟩

private theorem mem_sequentShiftCode_iff (s y : ℕ) :
    y ∈ sequentShiftCode s ↔
      ∃ x ∈ s, y = formulaShiftCode 0 x := by
  rw [sequentShiftCode, mem_shiftFold]
  constructor
  · rintro ⟨x, _, hx, hy⟩
    exact ⟨x, hx, hy⟩
  · rintro ⟨x, hx, hy⟩
    exact ⟨x, List.mem_range.mpr (lt_of_mem hx), hx, hy⟩

theorem sequentShiftValue_nat (s : ℕ) :
    sequentShiftValue s = sequentShiftCode s := by
  apply mem_ext
  intro y
  rw [mem_sequentShiftValue_iff, mem_sequentShiftCode_iff]
  constructor <;> rintro ⟨x, hx, rfl⟩
  · exact ⟨x, hx, formulaShiftValue_nat 0 x⟩
  · exact ⟨x, hx, (formulaShiftValue_nat 0 x).symm⟩

theorem sequentShiftGraph_nat_iff (t s : ℕ) :
    Semiformula.Evalb (M := ℕ) ![t, s] sequentShiftGraph.val ↔
      t = sequentShiftCode s := by
  rw [sequentShiftGraph_iff, sequentShiftValue_nat]

end FailureOfComposition.NativeInternalSyntax
