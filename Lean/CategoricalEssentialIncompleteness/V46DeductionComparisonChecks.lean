/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46DeductionComparison

/-! # Statement checks for the deduction comparison -/

@[expose] public section

noncomputable section

universe v₁ v₂ u₁ u₂

open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46

open DeductionComparison

variable {D₁ : Type u₁} {D₂ : Type u₂}
variable [Category.{v₁} D₁] [Category.{v₂} D₂] [Regular D₁] [Regular D₂]
variable [FinitaryExtensive D₁] [FinitaryExtensive D₂]
variable (G : D₁ ⥤ D₂)
variable (regularEpis : ∀ {X Y : D₁} (f : X ⟶ Y),
  IsRegularEpi f → IsRegularEpi (G.map f))
variable {V₁ : D₁} {V₂ : D₂}
variable (P : FirstOrderPresentation V₁) (Q : FirstOrderPresentation V₂)
variable (σ : G.obj P.syntaxData.sentenceObject ⟶ Q.syntaxData.sentenceObject)
variable (p : ∀ A : Subobject P.syntaxData.sentenceObject,
  G.obj (pullback (P.proofs A).a.hom P.syntaxData.sentenceInclusion) ⟶
    pullback (Q.proofs (imageObject G σ A)).a.hom Q.syntaxData.sentenceInclusion)
variable (hp : ∀ A, p A ≫ FirstOrderReflection.conclusion Q.proofs (imageObject G σ A) =
  G.map (FirstOrderReflection.conclusion P.proofs A) ≫ σ)

include regularEpis hp in
example : FirstOrderReflection.generation P.proofs P.initial ⋙ theoryFunctor G P Q σ =
    imageFunctor G σ ⋙ FirstOrderReflection.generation Q.proofs Q.initial :=
  generation_square G regularEpis P Q σ p hp

include regularEpis hp in
example : presentationFunctor G σ ⋙ FirstOrderReflection.presentationGeneration Q.proofs Q.initial =
    FirstOrderReflection.presentationGeneration P.proofs P.initial ⋙ theoryFunctor G P Q σ :=
  presentation_square G regularEpis P Q σ p hp

example : FirstOrderReflection.presentationInclusion P.proofs ⋙ presentationFunctor G σ ⟶
    theoryFunctor G P Q σ ⋙ FirstOrderReflection.presentationInclusion Q.proofs :=
  inclusionComparison G P Q σ

variable (R : Subobject Q.syntaxData.sentenceObject ⥤ Subobject P.syntaxData.sentenceObject)
variable (hR : imageFunctor G σ ⊣ R)

include regularEpis hp hR in
example (B : Q.Theories) : FirstOrderReflection.generated P.proofs (R.obj B.val) = R.obj B.val :=
  right_closed G regularEpis P Q σ p hp R hR B

include regularEpis hp hR in
example : theoryFunctor G P Q σ ⊣ restrictedRight G regularEpis P Q σ p hp R hR :=
  restrictedAdjunction G regularEpis P Q σ p hp R hR

#print axioms CategoricalEssentialIncompleteness.V46.DeductionComparison.image_presentation
#print axioms CategoricalEssentialIncompleteness.V46.DeductionComparison.generation_square
#print axioms CategoricalEssentialIncompleteness.V46.DeductionComparison.presentation_square
#print axioms CategoricalEssentialIncompleteness.V46.DeductionComparison.inclusionComparison
#print axioms CategoricalEssentialIncompleteness.V46.DeductionComparison.right_closed
#print axioms CategoricalEssentialIncompleteness.V46.DeductionComparison.restrictedAdjunction
