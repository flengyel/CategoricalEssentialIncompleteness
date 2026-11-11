/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerCanonicalSyntaxComparisonParameters

/-! # All seven logical parameters in the actual canonical syntax

The Q1 and equality parameters are the prescribed pullbacks of successful
substitution. Q2 is the actual false equalizer of the occurrence classifier.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
namespace CategoricalEssentialIncompleteness.V46.Miller.CanonicalPresentationParameterChecks
open CategoricalEssentialIncompleteness.V46.Miller.CanonicalPresentation
variable (a : Point) (V : PredicateCategory 𝗣𝗔)
variable (σ π : ℕ → PredicateCategory 𝗣𝗔) (d : ℕ)
local notation "P" => Uniform.Family.ofPoint a
local notation "E" => Total.pointPresentation a
local notation "S₁" => NamedSyntaxComparison.presentedSyntax (P) V σ π d
local notation "S₂" => NamedSyntaxComparison.canonicalPresentedSyntax a V σ π d
local notation "iv" => nameIso a V
local notation "it" => termIso a V σ π d
local notation "ifm" => formulaIso a V σ π d
local notation "ip" => parameterIso a V σ π d
local notation "ia" => admissibleIso a V σ π d

example :
    (E).functor.map (S₁).instantiationInput ≫
        (SyntaxOptionTransport.productIso (E) (ifm) (ip)).hom =
      (instantiationBaseIso a V σ π d).hom ≫ (S₂).instantiationInput := instantiationInput_comparison a V σ π d

example :
    (E).functor.map (S₁).instantiationInclusion ≫ (instantiationBaseIso a V σ π d).hom =
      (instantiationIso a V σ π d).hom ≫ (S₂).instantiationInclusion := instantiation_inclusion a V σ π d

example :
    (E).functor.map (S₁).instantiationAdmissible ≫ (ia).hom =
      (instantiationIso a V σ π d).hom ≫ (S₂).instantiationAdmissible := instantiation_admissible a V σ π d

example :
    (E).functor.map (S₁).distributionAbsence ≫
        (DecidableVariables.Transport.booleanIso (E)).hom =
      (distributionBaseIso a V σ π d).hom ≫ (S₂).distributionAbsence := distributionAbsence_comparison a V σ π d

example :
    (E).functor.map (S₁).distributionInclusion ≫ (distributionBaseIso a V σ π d).hom =
      (distributionIso a V σ π d).hom ≫ (S₂).distributionInclusion := distribution_inclusion a V σ π d

example :
    (E).functor.map (S₁).equalitySchemeInclusion ≫ (equalityBaseIso a V σ π d).hom =
      (equalitySchemeIso a V σ π d).hom ≫ (S₂).equalitySchemeInclusion := equality_inclusion a V σ π d

example :
    (E).functor.map (S₁).equalityFirstAdmissible ≫ (ia).hom =
      (equalitySchemeIso a V σ π d).hom ≫ (S₂).equalityFirstAdmissible := equality_first_admissible a V σ π d

example :
    (E).functor.map (S₁).equalitySecondAdmissible ≫ (ia).hom =
      (equalitySchemeIso a V σ π d).hom ≫ (S₂).equalitySecondAdmissible := equality_second_admissible a V σ π d

end CategoricalEssentialIncompleteness.V46.Miller.CanonicalPresentationParameterChecks
