/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import FailureOfComposition.NativeInternalApplications
import Foundation.FirstOrder.Arithmetic.Bootstrapping.DerivabilityCondition.D3

/-!
# Equality extraction for evaluator families

The evaluator relation has coordinates `(program,input,output)`. Its program
coordinate may be any internal element. Only the two external indices `h,k`
are used with the PA functionality theorem. Family equality quantifies in
the order `u,x,z`; the extraction seed quantifies in the order `u,y,y'`.
-/

set_option autoImplicit false

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.Entailment
open scoped FFL.FirstOrder.Arithmetic

namespace FailureOfComposition.NativeFamilyExtraction

open FFL.FirstOrder.Arithmetic.Bootstrapping
open FailureOfComposition.ProofSearch
open FailureOfComposition.ConcreteEvaluator
open FailureOfComposition.NativeEqualityTransport
open CategoricalRiceShapiro.Evaluator

-- Keep internal-syntax model coercions local to this new proof layer.
private noncomputable instance {V : Type*} [ORingStructure V] [hPA : V↓[ℒₒᵣ] ⊧* 𝗣𝗔] :
    V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ :=
  @models_of_subtheory ℒₒᵣ 𝗜𝚺₁ 𝗣𝗔 V ⟨0⟩ _ inferInstance hPA

/-- The actual evaluator, with an internal program parameter. -/
noncomputable def programGraph : 𝚺₁.Semisentence 3 := .mkSigma
  “q x z. ∃ s, !evalnCertificateFormula s q x z”

noncomputable def outputGraph (h : ℕ) : 𝚺₁.Semisentence 2 := eventualGraph h

noncomputable def familyGraph (h : ℕ) : 𝚺₁.Semisentence 3 := .mkSigma
  “u x z. ∃ y, !(outputGraph h) u y ∧ !programGraph y x z”

/-- This is arithmetic family equality, not yet categorical equality. -/
noncomputable def familyEq (M : 𝚺₁.Semisentence 1) (h k : ℕ) : ArithmeticSentence :=
  “∀ u, !M u → ∀ x z, (!(familyGraph h) u x z ↔ !(familyGraph k) u x z)”

/-- Matrix coordinates `(y',y,u)`, matching specialization in order `u,y,y'`. -/
def extractionMatrixFor (F : ArithmeticSentence) (M : ArithmeticSemisentence 1)
    (H K E : ArithmeticSemisentence 2) : ArithmeticSemisentence 3 :=
  “r y u. !F → !M u → !H u y → !K u r → !E y r”

noncomputable def extractionMatrix (M : 𝚺₁.Semisentence 1) (h k : ℕ) :
    ArithmeticSemisentence 3 := extractionMatrixFor (familyEq M h k) M.val
      (outputGraph h).val (outputGraph k).val equalityFormula

noncomputable def extractionBodyY (M : 𝚺₁.Semisentence 1) (h k : ℕ) :
    ArithmeticSemisentence 2 := ∀¹ extractionMatrix M h k

noncomputable def extractionBodyU (M : 𝚺₁.Semisentence 1) (h k : ℕ) :
    ArithmeticSemisentence 1 := ∀¹ extractionBodyY M h k

noncomputable def extractionSeed (M : 𝚺₁.Semisentence 1) (h k : ℕ) :
    ArithmeticSentence := ∀¹ extractionBodyU M h k

@[simp] theorem programGraph_eval {V : Type*} [ORingStructure V] (q x z : V) :
    programGraph.val.Evalb ![q, x, z] ↔
      ∃ s : V, evalnCertificateFormula.val.Evalb ![s, q, x, z] := by
  simp [programGraph]

@[simp] theorem outputGraph_eval {V : Type*} [ORingStructure V] (h : ℕ) (u y : V) :
    (outputGraph h).val.Evalb ![u, y] ↔ (eventualGraph h).val.Evalb ![u, y] := by
  rfl

theorem outputGraph_programGraph {V : Type*} [ORingStructure V] (h : ℕ) (u y : V) :
    (outputGraph h).val.Evalb ![u, y] ↔
      programGraph.val.Evalb ![ORingStructure.numeral h, u, y] := by
  rw [outputGraph_eval, eventualGraph_eval, programGraph_eval]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]

@[simp] theorem familyGraph_eval {V : Type*} [ORingStructure V] (h : ℕ) (u x z : V) :
    (familyGraph h).val.Evalb ![u, x, z] ↔
      ∃ y : V, (outputGraph h).val.Evalb ![u, y] ∧ programGraph.val.Evalb ![y, x, z] := by
  simp [familyGraph]

@[simp] theorem familyEq_eval {V : Type*} [ORingStructure V]
    (M : 𝚺₁.Semisentence 1) (h k : ℕ) :
    V↓[ℒₒᵣ] ⊧ familyEq M h k ↔
      ∀ u : V, M.val.Evalb ![u] → ∀ x z : V,
        (familyGraph h).val.Evalb ![u, x, z] ↔
          (familyGraph k).val.Evalb ![u, x, z] := by
  simp [familyEq, models_iff]

theorem equalityFormula_eval {V : Type*} [ORingStructure V] (y r : V) :
    equalityFormula.Evalb ![y, r] ↔ ∀ x z : V,
      programGraph.val.Evalb ![y, x, z] ↔ programGraph.val.Evalb ![r, x, z] := by
  simp [equalityFormula, equalityFormulaFor, programGraph]

theorem extractionMatrix_eval {V : Type*} [ORingStructure V]
    (M : 𝚺₁.Semisentence 1) (h k : ℕ) (u y r : V) :
    (extractionMatrix M h k).Evalb ![r, y, u] ↔
      (V↓[ℒₒᵣ] ⊧ familyEq M h k) → M.val.Evalb ![u] →
        (outputGraph h).val.Evalb ![u, y] → (outputGraph k).val.Evalb ![u, r] →
          equalityFormula.Evalb ![y, r] := by
  simp [extractionMatrix, extractionMatrixFor, models_iff]

/-- Forward extraction uses functionality of `k`; reverse extraction uses
functionality of `h`. No functionality at internal program indices is used. -/
theorem extractionMatrix_valid {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (M : 𝚺₁.Semisentence 1) (h k : ℕ) (u y r : V) :
    (extractionMatrix M h k).Evalb ![r, y, u] := by
  rw [extractionMatrix_eval, equalityFormula_eval]
  intro he hm hh hk x z
  have hf := (familyEq_eval M h k).mp he u hm x z
  constructor
  · intro hy
    obtain ⟨r', hr', hz⟩ := (familyGraph_eval k u x z).mp
      (hf.mp ((familyGraph_eval h u x z).mpr ⟨y, hh, hy⟩))
    have hr : r' = r := eventualGraph_output_unique k u r' r
      ((outputGraph_eval k u r').mp hr') ((outputGraph_eval k u r).mp hk)
    simpa [hr] using hz
  · intro hr
    obtain ⟨y', hy', hz⟩ := (familyGraph_eval h u x z).mp
      (hf.mpr ((familyGraph_eval k u x z).mpr ⟨r, hk, hr⟩))
    have hy : y' = y := eventualGraph_output_unique h u y' y
      ((outputGraph_eval h u y').mp hy') ((outputGraph_eval h u y).mp hh)
    simpa [hy] using hz

theorem extractionSeed_provable (M : 𝚺₁.Semisentence 1) (h k : ℕ) :
    𝗣𝗔 ⊢ extractionSeed M h k := by
  apply complete.{0} 𝗣𝗔
  intro V _ _
  simp only [models_iff, extractionSeed, extractionBodyU, extractionBodyY,
    Semiformula.eval_all]
  intro u y r
  exact extractionMatrix_valid M h k u y r

end FailureOfComposition.NativeFamilyExtraction
