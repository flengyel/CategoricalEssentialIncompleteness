/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46DeductionSliceAdjunction

/-! # Transposing an inference algebra

A rule transformation and an adjunction construct an algebra on the
right-adjoint carrier. Source initiality gives its fold; transposition
gives the comparison and its constructor equation.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v₁ v₂ u₁ u₂

open CategoryTheory CategoryTheory.Limits

namespace CategoricalEssentialIncompleteness.V46.DeductionMates

variable {C₁ : Type u₁} {C₂ : Type u₂} [Category.{v₁} C₁] [Category.{v₂} C₂]
variable {K : C₁ ⥤ C₂} {R : C₂ ⥤ C₁} (adj : K ⊣ R)
variable {H₁ : C₁ ⥤ C₁} {H₂ : C₂ ⥤ C₂} (rules : H₁ ⋙ K ⟶ K ⋙ H₂)

def algebra (B : Endofunctor.Algebra H₂) : Endofunctor.Algebra H₁ where
  a := R.obj B.a
  str := adj.homEquiv _ _
    (rules.app (R.obj B.a) ≫ H₂.map (adj.counit.app B.a) ≫ B.str)

theorem algebra_counit (B : Endofunctor.Algebra H₂) :
    K.map (algebra adj rules B).str ≫ adj.counit.app B.a =
      rules.app (R.obj B.a) ≫ H₂.map (adj.counit.app B.a) ≫ B.str := by
  change K.map (adj.homEquiv (H₁.obj (R.obj B.a)) B.a
    (rules.app (R.obj B.a) ≫ H₂.map (adj.counit.app B.a) ≫ B.str)) ≫
      adj.counit.app B.a = _
  have h := (adj.homEquiv (H₁.obj (R.obj B.a)) B.a).symm_apply_apply
    (rules.app (R.obj B.a) ≫ H₂.map (adj.counit.app B.a) ≫ B.str)
  rw [adj.homEquiv_counit] at h
  exact h

def fold (A : Endofunctor.Algebra H₁) (hA : IsInitial A)
    (B : Endofunctor.Algebra H₂) : K.obj A.a ⟶ B.a :=
  K.map (hA.to (algebra adj rules B)).f ≫ adj.counit.app B.a

theorem fold_transpose (A : Endofunctor.Algebra H₁) (hA : IsInitial A)
    (B : Endofunctor.Algebra H₂) :
    (adj.homEquiv _ _).symm (hA.to (algebra adj rules B)).f = fold adj rules A hA B :=
  adj.homEquiv_counit A.a B.a _

theorem fold_constructor (A : Endofunctor.Algebra H₁) (hA : IsInitial A)
    (B : Endofunctor.Algebra H₂) :
    K.map A.str ≫ fold adj rules A hA B =
      rules.app A.a ≫ H₂.map (fold adj rules A hA B) ≫ B.str := by
  let m := hA.to (algebra adj rules B)
  have hn := rules.naturality m.f
  change K.map (H₁.map m.f) ≫ rules.app (R.obj B.a) =
    rules.app A.a ≫ H₂.map (K.map m.f) at hn
  change K.map A.str ≫ (K.map m.f ≫ adj.counit.app B.a) = _
  calc
    _ = K.map (A.str ≫ m.f) ≫ adj.counit.app B.a := by
      rw [K.map_comp, Category.assoc]
    _ = K.map (H₁.map m.f ≫ (algebra adj rules B).str) ≫ adj.counit.app B.a := by
      rw [m.h]
    _ = K.map (H₁.map m.f) ≫ rules.app (R.obj B.a) ≫
        H₂.map (adj.counit.app B.a) ≫ B.str := by
      rw [K.map_comp, Category.assoc, algebra_counit]
    _ = rules.app A.a ≫ H₂.map (K.map m.f) ≫
        H₂.map (adj.counit.app B.a) ≫ B.str := by
      simpa only [Category.assoc] using
        congrArg (fun f => f ≫ H₂.map (adj.counit.app B.a) ≫ B.str) hn
    _ = rules.app A.a ≫ H₂.map (fold adj rules A hA B) ≫ B.str := by
      rw [fold, H₂.map_comp, Category.assoc]

section Sentences

variable {D₁ : Type u₁} {D₂ : Type u₂}
variable [Category.{v₁} D₁] [Category.{v₂} D₂] [Regular D₁] [Regular D₂]
variable (G : D₁ ⥤ D₂) {F₁ S₁ : D₁} {F₂ S₂ : D₂}
variable (j₁ : S₁ ⟶ F₁) (j₂ : S₂ ⟶ F₂)
variable (σ : G.obj S₁ ⟶ S₂) (σΦ : G.obj F₁ ⟶ F₂)
variable (hs : G.map j₁ ≫ σΦ = σ ≫ j₂)
variable (RΦ : Over F₂ ⥤ Over F₁)
variable (a : DeductionComparison.presentationFunctor G σΦ ⊣ RΦ)
variable {I₁ : Over F₁ ⥤ Over F₁} {I₂ : Over F₂ ⥤ Over F₂}
variable (ruleTransformation : I₁ ⋙ DeductionComparison.presentationFunctor G σΦ ⟶
  DeductionComparison.presentationFunctor G σΦ ⋙ I₂)

def sentenceMap (A : Endofunctor.Algebra I₁) (hA : IsInitial A)
    (B : Endofunctor.Algebra I₂) :
    G.obj (pullback A.a.hom j₁) ⟶ pullback B.a.hom j₂ := by
  let f := fold a ruleTransformation A hA B
  refine pullback.lift (G.map (pullback.fst A.a.hom j₁) ≫ f.left)
    (G.map (pullback.snd A.a.hom j₁) ≫ σ) ?_
  rw [Category.assoc, Over.w f]
  change G.map (pullback.fst A.a.hom j₁) ≫ (G.map A.a.hom ≫ σΦ) = _
  rw [← Category.assoc, ← G.map_comp, pullback.condition, G.map_comp,
    Category.assoc, hs, ← Category.assoc]

theorem sentenceMap_conclusion (A : Endofunctor.Algebra I₁) (hA : IsInitial A)
    (B : Endofunctor.Algebra I₂) :
    sentenceMap G j₁ j₂ σ σΦ hs RΦ a ruleTransformation A hA B ≫ pullback.snd B.a.hom j₂ =
      G.map (pullback.snd A.a.hom j₁) ≫ σ := by
  simp [sentenceMap]

end Sentences

section FirstOrder

variable {D₁ : Type u₁} {D₂ : Type u₂}
variable [Category.{v₁} D₁] [Category.{v₂} D₂]
variable [Regular D₁] [Regular D₂] [FinitaryExtensive D₁] [FinitaryExtensive D₂]
variable {G : D₁ ⥤ D₂} {H : D₂ ⥤ D₁} (baseAdjunction : G ⊣ H)
variable {V₁ : D₁} {V₂ : D₂}
variable (P : FirstOrderPresentation V₁) (Q : FirstOrderPresentation V₂)
variable (σ : G.obj P.syntaxData.sentenceObject ⟶ Q.syntaxData.sentenceObject)
variable (σΦ : G.obj P.syntaxData.algebra.a.2 ⟶ Q.syntaxData.algebra.a.2)
variable (hs : G.map P.syntaxData.sentenceInclusion ≫ σΦ =
  σ ≫ Q.syntaxData.sentenceInclusion)
variable (ruleTransformation : ∀ A : Subobject P.syntaxData.sentenceObject,
  (P.syntaxData.logicalRules A.arrow).inference ⋙
      DeductionComparison.presentationFunctor G σΦ ⟶
    DeductionComparison.presentationFunctor G σΦ ⋙
      (Q.syntaxData.logicalRules (DeductionComparison.imageObject G σ A).arrow).inference)

/-- Transposition of the rule transformation, followed by restriction to
sentence conclusions. The right adjoint is the displayed pullback along
the unit of the ambient adjunction. -/
def comparisonMap (A : Subobject P.syntaxData.sentenceObject) :
    G.obj (pullback (P.proofs A).a.hom P.syntaxData.sentenceInclusion) ⟶
      pullback (Q.proofs (DeductionComparison.imageObject G σ A)).a.hom
        Q.syntaxData.sentenceInclusion :=
  sentenceMap G P.syntaxData.sentenceInclusion Q.syntaxData.sentenceInclusion σ σΦ hs
    (DeductionSliceAdjunction.rightFunctor baseAdjunction σΦ)
    (DeductionSliceAdjunction.adjunction baseAdjunction σΦ)
    (ruleTransformation A) (P.proofs A) (P.initial A)
    (Q.proofs (DeductionComparison.imageObject G σ A))

theorem comparisonMap_conclusion (A : Subobject P.syntaxData.sentenceObject) :
    comparisonMap baseAdjunction P Q σ σΦ hs ruleTransformation A ≫
        FirstOrderReflection.conclusion Q.proofs (DeductionComparison.imageObject G σ A) =
      G.map (FirstOrderReflection.conclusion P.proofs A) ≫ σ :=
  sentenceMap_conclusion G P.syntaxData.sentenceInclusion Q.syntaxData.sentenceInclusion
    σ σΦ hs _ _ (ruleTransformation A) (P.proofs A) (P.initial A) _

variable (regularEpis : ∀ {X Y : D₁} (f : X ⟶ Y),
  IsRegularEpi f → IsRegularEpi (G.map f))

include baseAdjunction regularEpis hs ruleTransformation in
theorem generation_square_from_rules :
    FirstOrderReflection.generation P.proofs P.initial ⋙
        DeductionComparison.theoryFunctor G P Q σ =
      DeductionComparison.imageFunctor G σ ⋙
        FirstOrderReflection.generation Q.proofs Q.initial :=
  DeductionComparison.generation_square G regularEpis P Q σ
    (comparisonMap baseAdjunction P Q σ σΦ hs ruleTransformation)
    (comparisonMap_conclusion baseAdjunction P Q σ σΦ hs ruleTransformation)

include baseAdjunction regularEpis hs ruleTransformation in
theorem presentation_square_from_rules :
    DeductionComparison.presentationFunctor G σ ⋙
        FirstOrderReflection.presentationGeneration Q.proofs Q.initial =
      FirstOrderReflection.presentationGeneration P.proofs P.initial ⋙
        DeductionComparison.theoryFunctor G P Q σ :=
  DeductionComparison.presentation_square G regularEpis P Q σ
    (comparisonMap baseAdjunction P Q σ σΦ hs ruleTransformation)
    (comparisonMap_conclusion baseAdjunction P Q σ σΦ hs ruleTransformation)

def theoryAdjunction :=
  DeductionComparison.restrictedAdjunction G regularEpis P Q σ
    (comparisonMap baseAdjunction P Q σ σΦ hs ruleTransformation)
    (comparisonMap_conclusion baseAdjunction P Q σ σΦ hs ruleTransformation)
    (DeductionSliceAdjunction.rightOrder baseAdjunction σ)
    (DeductionSliceAdjunction.orderAdjunction baseAdjunction σ)

end FirstOrder
end CategoricalEssentialIncompleteness.V46.DeductionMates
