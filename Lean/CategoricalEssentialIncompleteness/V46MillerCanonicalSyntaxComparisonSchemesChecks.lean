import CategoricalEssentialIncompleteness.V46MillerCanonicalSyntaxComparisonSchemes
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
namespace CategoricalEssentialIncompleteness.V46.Miller.CanonicalPresentation
variable (a : Point) (V : PredicateCategory 𝗣𝗔) (σ π : ℕ → PredicateCategory 𝗣𝗔) (d : ℕ)
local notation "E" => Total.pointPresentation a
local notation "S₁" => NamedSyntaxComparison.presentedSyntax (Uniform.Family.ofPoint a) V σ π d
local notation "S₂" => NamedSyntaxComparison.canonicalPresentedSyntax a V σ π d
example : (E).functor.obj (S₁).logicalParameters ≅ (S₂).logicalParameters := logicalParametersIso a V σ π d
example : (E).functor.map (S₁).distributionAbsence ≫
      (DecidableVariables.Transport.booleanIso (E)).hom =
    (distributionBaseIso a V σ π d).hom ≫ (S₂).distributionAbsence := distributionAbsence_comparison a V σ π d
example : (E).functor.map (S₁).logicalAxioms ≫ (formulaIso a V σ π d).hom =
    (logicalParametersIso a V σ π d).hom ≫ (S₂).logicalAxioms := logicalAxioms_comparison a V σ π d
example : (E).functor.map (S₁).hilbertInstantiation ≫ (formulaIso a V σ π d).hom =
    (instantiationIso a V σ π d).hom ≫ (S₂).hilbertInstantiation := hilbertInstantiation_comparison a V σ π d
example : (E).functor.map (S₁).hilbertEquality ≫ (formulaIso a V σ π d).hom =
    (equalitySchemeIso a V σ π d).hom ≫ (S₂).hilbertEquality := hilbertEquality_comparison a V σ π d


/- Every displayed logical axiom is checked at its actual parameter object. -/
example : (E).functor.map (S₁).hilbertOne ≫ (formulaIso a V σ π d).hom =
    (formulaPairIso a V σ π d).hom ≫ (S₂).hilbertOne :=
  hilbertOne_comparison a V σ π d

example : (E).functor.map (S₁).hilbertTwo ≫ (formulaIso a V σ π d).hom =
    (formulaTripleIso a V σ π d).hom ≫ (S₂).hilbertTwo :=
  hilbertTwo_comparison a V σ π d

example : (E).functor.map (S₁).hilbertThree ≫ (formulaIso a V σ π d).hom =
    (formulaPairIso a V σ π d).hom ≫ (S₂).hilbertThree :=
  hilbertThree_comparison a V σ π d

example : (E).functor.map (S₁).hilbertDistribution ≫ (formulaIso a V σ π d).hom =
    (distributionIso a V σ π d).hom ≫ (S₂).hilbertDistribution :=
  hilbertDistribution_comparison a V σ π d

example : (E).functor.map (S₁).hilbertReflexivity ≫ (formulaIso a V σ π d).hom =
    (termIso a V σ π d).hom ≫ (S₂).hilbertReflexivity :=
  hilbertReflexivity_comparison a V σ π d

/- These are the prescribed successful-substitution and absence objects. -/
example : (E).functor.obj (S₁).instantiationParameters ≅ (S₂).instantiationParameters :=
  instantiationIso a V σ π d

example : (E).functor.obj (S₁).distributionParameters ≅ (S₂).distributionParameters :=
  distributionIso a V σ π d

example : (E).functor.obj (S₁).equalitySchemeParameters ≅ (S₂).equalitySchemeParameters :=
  equalitySchemeIso a V σ π d

example : (E).functor.map (S₁).instantiationAdmissible ≫ (admissibleIso a V σ π d).hom =
    (instantiationIso a V σ π d).hom ≫ (S₂).instantiationAdmissible :=
  instantiation_admissible a V σ π d

example : (E).functor.map (S₁).distributionInclusion ≫ (distributionBaseIso a V σ π d).hom =
    (distributionIso a V σ π d).hom ≫ (S₂).distributionInclusion :=
  distribution_inclusion a V σ π d

example : (E).functor.map (S₁).equalityFirstAdmissible ≫ (admissibleIso a V σ π d).hom =
    (equalitySchemeIso a V σ π d).hom ≫ (S₂).equalityFirstAdmissible :=
  equality_first_admissible a V σ π d

example : (E).functor.map (S₁).equalitySecondAdmissible ≫ (admissibleIso a V σ π d).hom =
    (equalitySchemeIso a V σ π d).hom ≫ (S₂).equalitySecondAdmissible :=
  equality_second_admissible a V σ π d

end CategoricalEssentialIncompleteness.V46.Miller.CanonicalPresentation
