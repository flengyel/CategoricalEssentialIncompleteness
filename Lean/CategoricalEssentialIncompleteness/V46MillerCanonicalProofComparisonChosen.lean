/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerCanonicalProofComparison
public import CategoricalEssentialIncompleteness.V46FirstOrderInference

/-! # The chosen canonical Γ pullback and its actual generated image

The transported Γ object is a genuine pullback. This last comparison
replaces it by the selected canonical pullback, then uses the two actual
initial derivation algebras to prove equality of the sentence images.
No selected proof of an axiom is needed.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
namespace CategoricalEssentialIncompleteness.V46.Miller.CanonicalPresentation
def selectedPullback {C : Type} [Category.{0} C] [HasPullbacks C]
    {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) : C :=
  @pullback C _ X Y Z f g (HasLimitsOfShape.has_limit (cospan f g))

def selectedFst {C : Type} [Category.{0} C] [HasPullbacks C]
    {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) : selectedPullback f g ⟶ X :=
  @pullback.fst C _ X Y Z f g (HasLimitsOfShape.has_limit (cospan f g))

def selectedIso {C : Type} [Category.{0} C] [HasPullbacks C]
    {W X Y Z : C} (p : W ⟶ X) (q : W ⟶ Y) (f : X ⟶ Z) (g : Y ⟶ Z)
    (h : IsPullback p q f g) : W ≅ selectedPullback f g := h.isoPullback

private theorem selectedIso_fst {C : Type} [Category.{0} C] [HasPullbacks C]
    {W X Y Z : C} (p : W ⟶ X) (q : W ⟶ Y) (f : X ⟶ Z) (g : Y ⟶ Z)
    (h : IsPullback p q f g) : (selectedIso p q f g h).hom ≫ selectedFst f g=p :=
  h.isoPullback_hom_fst

private theorem selectedFst_mono {C : Type} [Category.{0} C] [HasPullbacks C]
    {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [Mono g] : Mono (selectedFst f g) := by
  dsimp only [selectedFst]
  infer_instance

variable (a : Point) (σ π : ℕ → Carrier) (d : ℕ)
variable (Γ : Set ℕ) (hΓ : Uniform.Enumerable (Uniform.Family.ofPoint a) (· ∈ Γ))
local notation "P" => Uniform.Family.ofPoint a
local notation "E" => Total.pointPresentation a
local notation "V" => (NamedPostfixEncoding.variableCarrier : PredicateCategory 𝗣𝗔)
local notation "S₀" => NamedSyntaxComparison.sourceSyntax (V) σ π d
local notation "S₂" => NamedSyntaxComparison.canonicalPresentedSyntax a (V) σ π d

def firstArrow : (S₂).sentenceObject ⟶
    (E).functor.obj ((Syntax.predicateFunctor (P)).obj (S₀).algebra.a.2) :=
  canonicalSentenceWord a σ π d

def secondArrow :
    (E).functor.obj (AxiomSubobjects.axCarrier (P) (S₀).algebra.a.2 Γ hΓ) ⟶
      (E).functor.obj ((Syntax.predicateFunctor (P)).obj (S₀).algebra.a.2) :=
  (E).functor.map (AxiomSubobjects.axiomInclusion (P) (S₀).algebra.a.2 Γ hΓ)

private instance secondArrow_mono : Mono (secondArrow a σ π d Γ hΓ) := by
  dsimp only [secondArrow]
  infer_instance

def chosenAxiomObject : Total.CanonicalTotal a :=
  selectedPullback (firstArrow a σ π d) (secondArrow a σ π d Γ hΓ)

def chosenAxioms : chosenAxiomObject a σ π d Γ hΓ ⟶ (S₂).sentenceObject :=
  selectedFst (firstArrow a σ π d) (secondArrow a σ π d Γ hΓ)

instance chosenAxioms_mono : Mono (chosenAxioms a σ π d Γ hΓ) :=
  selectedFst_mono _ _

def canonicalAxiomIso : canonicalAxiomObject a σ π d Γ hΓ ≅ chosenAxiomObject a σ π d Γ hΓ :=
  selectedIso _ _ _ _ (canonicalAxiomPullback a σ π d Γ hΓ)

theorem canonicalAxiomIso_inclusion :
    (canonicalAxiomIso a σ π d Γ hΓ).hom ≫ chosenAxioms a σ π d Γ hΓ =
      canonicalAxioms a σ π d Γ hΓ :=
  selectedIso_fst _ _ _ _ (canonicalAxiomPullback a σ π d Γ hΓ)

theorem canonicalAxiomIso_inverse_inclusion :
    (canonicalAxiomIso a σ π d Γ hΓ).inv ≫ canonicalAxioms a σ π d Γ hΓ =
      chosenAxioms a σ π d Γ hΓ := by
  rw [← canonicalAxiomIso_inclusion, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

def chosenRules : RulePresentation (S₂).algebra.a.2 2 :=
  (S₂).logicalRules (chosenAxioms a σ π d Γ hΓ)

def chosenProofAlgebra : Endofunctor.Algebra (chosenRules a σ π d Γ hΓ).inference :=
  Derivation.Canonical.derivationAlgebra a (chosenRules a σ π d Γ hΓ)

def chosenProofInitial : IsInitial (chosenProofAlgebra a σ π d Γ hΓ) :=
  Derivation.Canonical.derivationInitial a (chosenRules a σ π d Γ hΓ)

def chosenConclusion : (chosenProofAlgebra a σ π d Γ hΓ).a.left ⟶ (S₂).algebra.a.2 :=
  (chosenProofAlgebra a σ π d Γ hΓ).a.hom

def chosenSentenceProofObject : Total.CanonicalTotal a :=
  pullback (chosenConclusion a σ π d Γ hΓ) (S₂).sentenceInclusion

def chosenSentenceConclusion : chosenSentenceProofObject a σ π d Γ hΓ ⟶ (S₂).sentenceObject :=
  pullback.snd (chosenConclusion a σ π d Γ hΓ) (S₂).sentenceInclusion

theorem chosen_sentenceTheory_eq_transport :
    imageSubobject (chosenSentenceConclusion a σ π d Γ hΓ) =
      imageSubobject (canonicalSentenceConclusion a σ π d Γ hΓ) := by
  apply le_antisymm
  · exact firstOrder_sentence_image_monotone
      (S₂).logicalAxioms (S₂).sentenceInclusion (chosenAxioms a σ π d Γ hΓ)
      (canonicalAxioms a σ π d Γ hΓ) (S₂).quantifierConstructor (S₂).implicationConstructor
      (canonicalAxiomIso a σ π d Γ hΓ).inv (canonicalAxiomIso_inverse_inclusion a σ π d Γ hΓ)
      (chosenProofAlgebra a σ π d Γ hΓ) (chosenProofInitial a σ π d Γ hΓ)
      (canonicalProofAlgebra a σ π d Γ hΓ)
  · exact firstOrder_sentence_image_monotone
      (S₂).logicalAxioms (S₂).sentenceInclusion (canonicalAxioms a σ π d Γ hΓ)
      (chosenAxioms a σ π d Γ hΓ) (S₂).quantifierConstructor (S₂).implicationConstructor
      (canonicalAxiomIso a σ π d Γ hΓ).hom (canonicalAxiomIso_inclusion a σ π d Γ hΓ)
      (canonicalProofAlgebra a σ π d Γ hΓ) (canonicalProofInitial a σ π d Γ hΓ)
      (chosenProofAlgebra a σ π d Γ hΓ)

/-- This endpoint uses all three chosen canonical objects: the sentence
pullback, the Γ axiom pullback, and the successful derivation algebra. -/
theorem chosen_canonical_sentenceTheory_eq :
    imageSubobject (chosenSentenceConclusion a σ π d Γ hΓ) =
      Subobject.mk ((E).functor.map (image.ι (NamedProofImage.sentenceConclusion (P) σ π d Γ hΓ)) ≫
        (mappedSentenceIso a (V) σ π d).hom) :=
  (chosen_sentenceTheory_eq_transport a σ π d Γ hΓ).trans (canonical_sentenceTheory_eq a σ π d Γ hΓ)
end CategoricalEssentialIncompleteness.V46.Miller.CanonicalPresentation
