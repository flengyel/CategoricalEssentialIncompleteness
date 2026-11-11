/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NumericalDerivationInterpretationInitial
public import CategoricalEssentialIncompleteness.V46NumericalDerivationInterpretationCoherence
public import CategoricalEssentialIncompleteness.V46NumericalDerivationInterpretationOptions

/-! # The actual interpreted validator and successful derivation pullback

Source ordinary-tree initiality is proved from the constructed TA algebra,
not assumed of the arithmetic interpretation. Its unique fold then
identifies the validator square, and the two actual successful pullbacks
supply the comparison of derivation carriers and conclusions.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
namespace CategoricalEssentialIncompleteness.V46.NumericalDerivationInterpretation
open SyntacticSyntax SyntacticDerivation
variable {F : PredicateCategory 𝗣𝗔} {N : ℕ} (R : RulePresentation F N)

def mappedOrdinaryInitial :
    IsInitial (mappedOrdinaryAlgebra R (SyntacticDerivation.ordinaryTree 𝗣𝗔 R)) :=
  (Coherence.targetMappedInitial R (oneSortAlgebra 𝗣𝗔 (PolynomialComparison.coefficients R) N)
    (Initial.mappedOneSortInitial (PolynomialComparison.coefficients R) N)).ofIso
      (Coherence.mappedAlgebraIso R (oneSortAlgebra 𝗣𝗔 (PolynomialComparison.coefficients R) N)).symm

def sourceOrdinaryIso :
    mappedOrdinaryAlgebra R (SyntacticDerivation.ordinaryTree 𝗣𝗔 R) ≅
      NumericalDerivation.ordinaryTree (interpretedRules R) :=
  (mappedOrdinaryInitial R).uniqueUpToIso (NumericalDerivation.ordinaryTreeInitial (interpretedRules R))

/-- Equality is among actual algebra morphisms into the validator. -/
theorem sourceValidator_square :
    K.map (SyntacticDerivation.validatorFold 𝗣𝗔 R).f ≫ (optionIso F).hom =
      (sourceOrdinaryIso R).hom.f ≫ (NumericalDerivation.validatorFold (interpretedRules R)).f := by
  have h := congrArg Endofunctor.Algebra.Hom.f
    ((mappedOrdinaryInitial R).hom_ext (mappedValidatorFold R)
      ((sourceOrdinaryIso R).hom ≫ NumericalDerivation.validatorFold (interpretedRules R)))
  exact (mappedValidatorFold_arrow R).symm.trans h

private theorem predicateSuccessfulPullback {W F : PredicateCategory 𝗣𝗔}
    (v : W ⟶ OptionSyntax.obj F) :
    IsPullback (representedArrow 𝗣𝗔 (SuccessCarrier.inclusion v))
      (representedArrow 𝗣𝗔 (SuccessCarrier.conclusion v)) v
      (coprod.inr : F ⟶ OptionSyntax.obj F) := by
  let _ : IsIso (SuccessCarrier.comparison v) := SuccessCarrier.comparison_isIso v
  exact IsPullback.of_iso_pullback ⟨SuccessCarrier.square v⟩ (asIso (SuccessCarrier.comparison v))
    (by simp [SuccessCarrier.comparison]) (by simp [SuccessCarrier.comparison])

theorem sourceSuccessful_pullback :
    IsPullback (SyntacticDerivation.treeInclusion 𝗣𝗔 R)
      (SyntacticDerivation.derivationAlgebra 𝗣𝗔 R).a.hom
      (SyntacticDerivation.validatorFold 𝗣𝗔 R).f
      (coprod.inr : F ⟶ OptionSyntax.obj F) :=
  predicateSuccessfulPullback (SyntacticDerivation.validatorFold 𝗣𝗔 R).f

def sourceTreeMap : K.obj (SyntacticDerivation.derivationAlgebra 𝗣𝗔 R).a.left ⟶
    (NumericalDerivation.ordinaryTree (interpretedRules R)).a :=
  K.map (SyntacticDerivation.treeInclusion 𝗣𝗔 R) ≫ (sourceOrdinaryIso R).hom.f

theorem mappedSourceSuccessful_pullback :
    IsPullback (sourceTreeMap R) (K.map (SyntacticDerivation.derivationAlgebra 𝗣𝗔 R).a.hom)
      (NumericalDerivation.validatorFold (interpretedRules R)).f
      (coprod.inr : K.obj F ⟶ OptionSyntax.obj (K.obj F)) := by
  apply ((sourceSuccessful_pullback R).map K).of_iso (Iso.refl _)
    ((Endofunctor.Algebra.forget (PolynomialComparison.ordinary (interpretedRules R))).mapIso
      (sourceOrdinaryIso R)) (Iso.refl _) (optionIso F)
  · simp only [sourceTreeMap,CategoryTheory.Functor.mapIso_hom,Iso.refl_hom,CategoryTheory.Category.id_comp]
    rfl
  · simp only [Iso.refl_hom,CategoryTheory.Category.id_comp,CategoryTheory.Category.comp_id]
  · exact sourceValidator_square R
  · simpa only [Iso.refl_hom,CategoryTheory.Category.id_comp] using optionIso_inr F

/-- Both ends retain the original successful tree carrier. The morphisms
come from the proved pullbacks, with the same conclusion object. -/
def interpretationCarrierIso : NumericalDerivation.codeObject (interpretedRules R) ≅
    K.obj (SyntacticDerivation.derivationAlgebra 𝗣𝗔 R).a.left :=
  (NumericalDerivation.code_isPullback (interpretedRules R)).isoPullback ≪≫
    (mappedSourceSuccessful_pullback R).isoPullback.symm

@[reassoc] theorem interpretationCarrierIso_tree :
    (interpretationCarrierIso R).hom ≫ sourceTreeMap R =
      NumericalDerivation.codeTreeInclusion (interpretedRules R) := by
  simp only [interpretationCarrierIso,Iso.trans_hom,Iso.symm_hom,CategoryTheory.Category.assoc,
    IsPullback.isoPullback_inv_fst,IsPullback.isoPullback_hom_fst]

@[reassoc] theorem interpretationCarrierIso_conclusion :
    (interpretationCarrierIso R).hom ≫ K.map (SyntacticDerivation.derivationAlgebra 𝗣𝗔 R).a.hom =
      NumericalDerivation.codeConclusion (interpretedRules R) := by
  simp only [interpretationCarrierIso,Iso.trans_hom,Iso.symm_hom,CategoryTheory.Category.assoc,
    IsPullback.isoPullback_inv_snd,IsPullback.isoPullback_hom_snd]

def interpretationOverIso :
    (NumericalDerivation.codeAlgebra (interpretedRules R)).a ≅
      (mappedAlgebra R (SyntacticDerivation.derivationAlgebra 𝗣𝗔 R)).a :=
  Over.isoMk (interpretationCarrierIso R) (interpretationCarrierIso_conclusion R)

instance sourceTreeMap_mono : Mono (sourceTreeMap R) :=
  (mappedSourceSuccessful_pullback R).mono_fst_of_mono

end CategoricalEssentialIncompleteness.V46.NumericalDerivationInterpretation
