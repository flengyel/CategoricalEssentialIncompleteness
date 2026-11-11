/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.StandardTrueTheory
public import CategoricalEssentialIncompleteness.V46KaroubiRestriction
public import CategoricalEssentialIncompleteness.V46NumericalTuplesPartialMaps
public import CategoricalEssentialIncompleteness.V46SyntacticListsTotal

/-! # Stable list algebras in the numerical tuple category -/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.RestrictionCategory CategoryTheory.Limits
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoricalEssentialIncompleteness.LocalConnectedness

namespace CategoricalEssentialIncompleteness.V46.NumericalStableLists

/-- The actual standard-model comparison preserves restriction domains. -/
theorem standardComparison_preserves : PreservesRestriction StandardTrueTheory.comparison := by
  intro X Y f
  apply FunctorImage.Hom.ext
  change (SyntacticModel.modelFunctor 𝗧𝗔 ℕ).map (rst f) =
    ClassicalPrograms.J.map (rst (StandardTrueTheory.comparison.map f))
  rw [ClassicalPrograms.J_rst]
  exact SyntacticModel.model_map_restriction 𝗧𝗔 ℕ f

theorem standardInverse_preserves :
    PreservesRestriction StandardTrueTheory.equivalence.inverse := by
  intro X Y f
  exact LocalConnectedness.V46.equivalence_inverse_preserves
    StandardTrueTheory.equivalence standardComparison_preserves f

/-- The full standard theory and ordinary recursive maps have equivalent
restriction splittings, with the actual idempotent and morphism maps. -/
def standardSplittingEquivalence :
    SplitObject (FailureOfComposition.TypedProgramCategory.CodedProgramCategory 𝗧𝗔) ≌
      SplitObject ClassicalPrograms.Rec :=
  splittingEquivalenceOfRestriction StandardTrueTheory.equivalence
    standardComparison_preserves standardInverse_preserves

theorem standardSplitting_preserves :
    PreservesRestriction standardSplittingEquivalence.functor :=
  PreservesRestriction.splitFunctor_rst standardComparison_preserves

/-- Total arrows, rather than merely underlying set functions, are compared. -/
def standardTotalEquivalence : SyntacticPredicates.TotalSplit 𝗧𝗔 ≌
    PartialSpans.Total (SplitObject ClassicalPrograms.Rec) :=
  PreservesRestriction.totalEquivalence standardSplitting_preserves

/-- The syntactic total category of the full standard theory presents
the literal numerical tuple category. -/
def numericalEquivalence : SyntacticPredicates.TotalSplit 𝗧𝗔 ≌ NumericalTuples.Object :=
  standardTotalEquivalence.trans NumericalTuples.classicalTotalEquivalence.symm

/-- Every numerical coefficient object has a constructed list algebra
initial in the base category and in every parameter slice. -/
def stableListAlgebra (V : NumericalTuples.Object) : StableListAlgebra V :=
  SyntacticLists.Transport.mappedStableListAlgebra numericalEquivalence
    (numericalEquivalence.inverse.obj V) V (numericalEquivalence.counitIso.app V)
      (SyntacticLists.totalStableListAlgebra 𝗧𝗔 (numericalEquivalence.inverse.obj V))

end CategoricalEssentialIncompleteness.V46.NumericalStableLists
