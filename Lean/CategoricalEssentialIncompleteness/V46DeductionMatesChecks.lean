/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46DeductionMates

/-! # Statement checks for the deduction comparison -/

@[expose] public section

noncomputable section

universe v₁ v₂ u₁ u₂

open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46

open DeductionMates

section Algebras
variable {C₁ : Type u₁} {C₂ : Type u₂} [Category.{v₁} C₁] [Category.{v₂} C₂]
variable {K : C₁ ⥤ C₂} {R : C₂ ⥤ C₁} (adj : K ⊣ R)
variable {H₁ : C₁ ⥤ C₁} {H₂ : C₂ ⥤ C₂} (rules : H₁ ⋙ K ⟶ K ⋙ H₂)
variable (A : Endofunctor.Algebra H₁) (hA : IsInitial A) (B : Endofunctor.Algebra H₂)

example : K.map A.str ≫ fold adj rules A hA B =
    rules.app A.a ≫ H₂.map (fold adj rules A hA B) ≫ B.str :=
  fold_constructor adj rules A hA B
end Algebras

variable {D₁ : Type u₁} {D₂ : Type u₂}
variable [Category.{v₁} D₁] [Category.{v₂} D₂]
variable [Regular D₁] [Regular D₂] [FinitaryExtensive D₁] [FinitaryExtensive D₂]
variable {G : D₁ ⥤ D₂} {H : D₂ ⥤ D₁} (adj : G ⊣ H)
variable {V₁ : D₁} {V₂ : D₂}
variable (P : FirstOrderPresentation V₁) (Q : FirstOrderPresentation V₂)
variable (σ : G.obj P.syntaxData.sentenceObject ⟶ Q.syntaxData.sentenceObject)
variable (σΦ : G.obj P.syntaxData.algebra.a.2 ⟶ Q.syntaxData.algebra.a.2)
variable (hs : G.map P.syntaxData.sentenceInclusion ≫ σΦ =
  σ ≫ Q.syntaxData.sentenceInclusion)
variable (rules : ∀ A : Subobject P.syntaxData.sentenceObject,
  (P.syntaxData.logicalRules A.arrow).inference ⋙
      DeductionComparison.presentationFunctor G σΦ ⟶
    DeductionComparison.presentationFunctor G σΦ ⋙
      (Q.syntaxData.logicalRules (DeductionComparison.imageObject G σ A).arrow).inference)
variable (regularEpis : ∀ {X Y : D₁} (f : X ⟶ Y),
  IsRegularEpi f → IsRegularEpi (G.map f))

example (A : Subobject P.syntaxData.sentenceObject) :
    comparisonMap adj P Q σ σΦ hs rules A ≫
        FirstOrderReflection.conclusion Q.proofs (DeductionComparison.imageObject G σ A) =
      G.map (FirstOrderReflection.conclusion P.proofs A) ≫ σ :=
  comparisonMap_conclusion adj P Q σ σΦ hs rules A

include adj hs rules regularEpis in
example : FirstOrderReflection.generation P.proofs P.initial ⋙
      DeductionComparison.theoryFunctor G P Q σ =
    DeductionComparison.imageFunctor G σ ⋙ FirstOrderReflection.generation Q.proofs Q.initial :=
  generation_square_from_rules adj P Q σ σΦ hs rules regularEpis

include adj hs rules regularEpis in
example : DeductionComparison.presentationFunctor G σ ⋙
      FirstOrderReflection.presentationGeneration Q.proofs Q.initial =
    FirstOrderReflection.presentationGeneration P.proofs P.initial ⋙
      DeductionComparison.theoryFunctor G P Q σ :=
  presentation_square_from_rules adj P Q σ σΦ hs rules regularEpis

example : DeductionComparison.theoryFunctor G P Q σ ⊣
    DeductionComparison.restrictedRight G regularEpis P Q σ
      (comparisonMap adj P Q σ σΦ hs rules)
      (comparisonMap_conclusion adj P Q σ σΦ hs rules)
      (DeductionSliceAdjunction.rightOrder adj σ)
      (DeductionSliceAdjunction.orderAdjunction adj σ) :=
  theoryAdjunction adj P Q σ σΦ hs rules regularEpis

#print axioms CategoricalEssentialIncompleteness.V46.DeductionMates.algebra
#print axioms CategoricalEssentialIncompleteness.V46.DeductionMates.fold_constructor
#print axioms CategoricalEssentialIncompleteness.V46.DeductionMates.comparisonMap
#print axioms CategoricalEssentialIncompleteness.V46.DeductionMates.comparisonMap_conclusion
#print axioms CategoricalEssentialIncompleteness.V46.DeductionMates.generation_square_from_rules
#print axioms CategoricalEssentialIncompleteness.V46.DeductionMates.presentation_square_from_rules
#print axioms CategoricalEssentialIncompleteness.V46.DeductionMates.theoryAdjunction
