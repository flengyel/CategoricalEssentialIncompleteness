import CategoricalEssentialIncompleteness.V46MillerCanonicalProofComparisonChosen
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
namespace CategoricalEssentialIncompleteness.V46.Miller.CanonicalPresentation
variable (a : Point) (σ π : ℕ → Carrier) (d : ℕ)
variable (Γ : Set ℕ) (hΓ : Uniform.Enumerable (Uniform.Family.ofPoint a) (· ∈ Γ))
local notation "P" => Uniform.Family.ofPoint a
local notation "E" => Total.pointPresentation a
local notation "V" => (NamedPostfixEncoding.variableCarrier : PredicateCategory 𝗣𝗔)
example : canonicalAxiomObject a σ π d Γ hΓ ≅ chosenAxiomObject a σ π d Γ hΓ := canonicalAxiomIso a σ π d Γ hΓ
example : IsInitial (chosenProofAlgebra a σ π d Γ hΓ) := chosenProofInitial a σ π d Γ hΓ
example : imageSubobject (chosenSentenceConclusion a σ π d Γ hΓ) =
    Subobject.mk ((E).functor.map (image.ι (NamedProofImage.sentenceConclusion (P) σ π d Γ hΓ)) ≫
      (mappedSentenceIso a (V) σ π d).hom) := chosen_canonical_sentenceTheory_eq a σ π d Γ hΓ
example : (canonicalAxiomIso a σ π d Γ hΓ).hom ≫ chosenAxioms a σ π d Γ hΓ =
    canonicalAxioms a σ π d Γ hΓ := canonicalAxiomIso_inclusion a σ π d Γ hΓ

example : (canonicalAxiomIso a σ π d Γ hΓ).inv ≫ canonicalAxioms a σ π d Γ hΓ =
    chosenAxioms a σ π d Γ hΓ := canonicalAxiomIso_inverse_inclusion a σ π d Γ hΓ

example : imageSubobject (chosenSentenceConclusion a σ π d Γ hΓ) =
    imageSubobject (canonicalSentenceConclusion a σ π d Γ hΓ) :=
  chosen_sentenceTheory_eq_transport a σ π d Γ hΓ

end CategoricalEssentialIncompleteness.V46.Miller.CanonicalPresentation
