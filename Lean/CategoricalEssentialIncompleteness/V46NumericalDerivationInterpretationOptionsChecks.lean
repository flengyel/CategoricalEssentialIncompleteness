/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NumericalDerivationInterpretationOptions


/-! # Statement checks in `V46NumericalDerivationInterpretationOptionsChecks` -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
namespace CategoricalEssentialIncompleteness.V46.NumericalDerivationInterpretation
open SyntacticDerivation
example (F : PredicateCategory 𝗣𝗔) :
    K.map (coprod.inr : F ⟶ OptionSyntax.obj F) ≫ (optionIso F).hom = coprod.inr := optionIso_inr F
variable {F : PredicateCategory 𝗣𝗔} {N : ℕ} (R : RulePresentation F N)
example (i : Fin (N+1)) :
    (rootInputIso R i).hom ≫ prod.fst = K.map prod.fst := rootInputIso_fst R i
example (i : Fin (N+1)) :
    K.map (prod.lift (𝟙 (R.instances i))
      (R.premises i ≫ finitePowerMap (coprod.inr : F ⟶ OptionSyntax.obj F) i.val)) ≫
        (rootInputIso R i).hom =
      prod.lift (𝟙 ((interpretedRules R).instances i))
        ((interpretedRules R).premises i ≫
          finitePowerMap (coprod.inr : K.obj F ⟶ OptionSyntax.obj (K.obj F)) i.val) :=
  rootInputIso_matching R i
example (i : Fin (N+1)) :
    IsPullback (RootGeometry.successfulInput R i) (R.conclusion i)
      (sourceRootValidator R i) coprod.inr := sourceRootValidator_isPullback R i
example (i : Fin (N+1)) :
    IsPullback (RootGeometry.successfulInput (interpretedRules R) i) ((interpretedRules R).conclusion i)
      (targetRootValidator R i) coprod.inr := targetRootValidator_isPullback R i
example (i : Fin (N+1)) :
    K.map (sourceRootValidator R i) ≫ (optionIso F).hom =
      (rootInputIso R i).hom ≫ targetRootValidator R i := rootValidator_comparison R i
example : mappedOrdinaryAlgebra R (SuccessComparison.validator 𝗣𝗔 R) ≅
    NumericalDerivation.validator (interpretedRules R) := validatorAlgebraIso R
example : (mappedValidatorFold R).f =
    K.map (SyntacticDerivation.validatorFold 𝗣𝗔 R).f ≫ (optionIso F).hom := mappedValidatorFold_arrow R
end CategoricalEssentialIncompleteness.V46.NumericalDerivationInterpretation
