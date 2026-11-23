/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46EnumerableCarrierEnumeration
public import CategoricalEssentialIncompleteness.V46ModelFamilyDiagonal
public import CategoricalEssentialIncompleteness.V46ObservationCoding
public import CategoricalEssentialIncompleteness.V46RegularActionPoints

/-! # Statement checks for the unnumbered examples in §§4, 5, 8 and Appendix D -/

public section
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.RestrictionCategory
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoricalEssentialIncompleteness CategoricalEssentialIncompleteness.LocalConnectedness
open FailureOfComposition.TypedProgramCategory FailureOfComposition.TypedTuringMorphism
open CategoricalEssentialIncompleteness.V46 ClassicalPrograms
open scoped EnumerableCarrierEnumeration ModelFamilyDiagonal

namespace CategoricalEssentialIncompleteness.V46.ManuscriptExamplesChecks

example (G : Type u) [Group G] [Nontrivial G] :
    Nonempty (IsTerminal (RegularActionPoints.singleton G)) ∧
    Nonempty (IsColimit (BinaryCofan.mk (RegularActionPoints.inclusion G)
      (RegularActionPoints.regularInclusion G))) ∧
    Mono (RegularActionPoints.inclusion G) ∧ ¬ IsIso (RegularActionPoints.inclusion G) ∧
    ∀ p : RegularActionPoints.singleton G ⟶ RegularActionPoints.sumAction G,
      ∃ q : RegularActionPoints.singleton G ⟶ RegularActionPoints.singleton G,
        q ≫ RegularActionPoints.inclusion G = p :=
  ⟨⟨RegularActionPoints.singletonIsTerminal G⟩, ⟨RegularActionPoints.sumIsColimit G⟩,
    RegularActionPoints.inclusion_mono G, RegularActionPoints.inclusion_not_iso G,
    RegularActionPoints.globalPoint_factors G⟩

example (A : Set ℕ) (hA : REPred (· ∈ A)) (h : A.Infinite) :
    ∃ (e : ℕ → ℕ) (r : ℕ → Part ℕ) (i : parameterObject ≅ ceObject A hA),
      Computable e ∧ Function.Injective e ∧ Set.range e = A ∧ Partrec r ∧
      (∀ x, (r x).Dom ↔ x ∈ A) ∧ (∀ n, r (e n) = Part.some n) ∧
      (∀ x, (r x).bind (fun n => Part.some (e n)) = supportIdentity A x) ∧
      J.map i.hom.hom = (fun n => Part.some (e n)) ∧ J.map i.inv.hom = r ∧
      isTotal i.hom ∧ isTotal i.inv ∧
      ∃ E : PartialMaps.Par (Over (⟨parameterObject⟩ : EnumerableCarrierEnumeration.TotalSplit)) ≌
        PartialMaps.Par (Over (⟨ceObject A hA⟩ : EnumerableCarrierEnumeration.TotalSplit)),
        E.functor = MonicPartialSliceComparison.postcompose
          (EnumerableCarrierEnumeration.totalSplitIso i).hom := by
  obtain ⟨e, r, he, hi, himage, hr, hd, hl, hh, i, hf, hg, ht, hu, E, hE⟩ :=
    EnumerableCarrierEnumeration.infinite_enumerable_carrier A hA h
  exact ⟨e, r, i, he, hi, himage, hr, hd, fun n => by simpa only [Part.bind_some] using hl n,
    hh, hf, hg, ht, hu, E, hE⟩

example (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] (hT : Consistent T) :
    RecursionCategory.IsTuringMorphism (typedTau T) ∧
      ¬ RecursionCategory.IsTuringMorphism
        (W := (SyntacticModel.familyFunctor T).obj (omegaObject T))
        (X := (SyntacticModel.familyFunctor T).obj (omegaObject T))
        (Y := (SyntacticModel.familyFunctor T).obj (omegaObject T))
        ((SyntacticModel.familyFunctor T).map (typedTau T)) :=
  ⟨typedTau_isTuringMorphism T, ModelFamilyDiagonal.image_not_turing T hT⟩

example (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] (j : ℕ) (x : M) :
    ((ClassicalPrograms.outputPredicate j).val.Evalb ![x] ↔
      ∃ m : M, UniformTrace.graph.val.Evalb ![pi₁ x, pair (pi₂ x) x, 2 * m + (j : M)]) ∧
    ((ArithmeticDiagonalCodes.outputPredicate j).val.Evalb ![x] ↔
      ∃ m : M, UniformTrace.graph.val.Evalb ![x,x,2 * m + (j : M)]) :=
  ⟨ObservationCoding.native_output j x, ObservationCoding.named_source_output j x⟩

end CategoricalEssentialIncompleteness.V46.ManuscriptExamplesChecks
