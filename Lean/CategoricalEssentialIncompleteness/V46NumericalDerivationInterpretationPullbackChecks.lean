/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NumericalDerivationInterpretationPullback


/-! # Statement checks in `V46NumericalDerivationInterpretationPullbackChecks` -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
namespace CategoricalEssentialIncompleteness.V46.NumericalDerivationInterpretation
open SyntacticDerivation
variable {F : PredicateCategory 𝗣𝗔} {N : ℕ} (R : RulePresentation F N)
example : IsInitial (mappedOrdinaryAlgebra R (SyntacticDerivation.ordinaryTree 𝗣𝗔 R)) := mappedOrdinaryInitial R
example : K.map (SyntacticDerivation.validatorFold 𝗣𝗔 R).f ≫ (optionIso F).hom =
    (sourceOrdinaryIso R).hom.f ≫ (NumericalDerivation.validatorFold (interpretedRules R)).f :=
  sourceValidator_square R
example : IsPullback (sourceTreeMap R) (K.map (SyntacticDerivation.derivationAlgebra 𝗣𝗔 R).a.hom)
    (NumericalDerivation.validatorFold (interpretedRules R)).f
    (coprod.inr : K.obj F ⟶ OptionSyntax.obj (K.obj F)) := mappedSourceSuccessful_pullback R
example : NumericalDerivation.codeObject (interpretedRules R) ≅
    K.obj (SyntacticDerivation.derivationAlgebra 𝗣𝗔 R).a.left := interpretationCarrierIso R
example : (interpretationCarrierIso R).hom ≫ K.map (SyntacticDerivation.derivationAlgebra 𝗣𝗔 R).a.hom =
    NumericalDerivation.codeConclusion (interpretedRules R) := interpretationCarrierIso_conclusion R
example : (interpretationCarrierIso R).hom ≫ sourceTreeMap R =
    NumericalDerivation.codeTreeInclusion (interpretedRules R) := interpretationCarrierIso_tree R
end CategoricalEssentialIncompleteness.V46.NumericalDerivationInterpretation
