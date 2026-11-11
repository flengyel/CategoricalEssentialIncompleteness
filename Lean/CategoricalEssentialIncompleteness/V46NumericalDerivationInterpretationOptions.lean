/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NumericalDerivationInterpretationValidation
public import CategoricalEssentialIncompleteness.V46SyntacticDerivationInitial

/-! # Option and root-input comparison for interpreted PA rules

The option comparison preserves the unique failure branch and the original
formula-valued success branch. The root input retains the rule instance
and the actual ordered tuple of successful child conclusions.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
namespace CategoricalEssentialIncompleteness.V46.NumericalDerivationInterpretation
open SyntacticDerivation

namespace RootGeometry
universe v u
variable {D : Type u} [Category.{v} D] [Regular D] [FinitaryExtensive D]
variable {F : D} {N : ℕ} (R : RulePresentation F N) (i : Fin (N+1))

/-- At the identity conclusion map the inference pullback is the given
rule-instance object, with its original prescribed premise tuple. -/
def identityRuleIso : R.instances i ≅ R.ruleObject (Over.mk (𝟙 F)) i where
  hom := pullback.lift (𝟙 _) (R.premises i) (by simp)
  inv := pullback.fst _ _
  hom_inv_id := by simp
  inv_hom_id := by
    apply pullback.hom_ext
    · simp
    · simpa using (pullback.condition (f := R.premises i)
        (g := finitePowerMap (𝟙 F) i.val))

def successfulInput : R.instances i ⟶ R.instances i ⨯ finitePower (OptionSyntax.obj F) i.val :=
  prod.lift (𝟙 _) (R.premises i ≫ finitePowerMap (coprod.inr : F ⟶ OptionSyntax.obj F) i.val)

theorem root_isPullback
    (v : R.instances i ⨯ finitePower (OptionSyntax.obj F) i.val ⟶ OptionSyntax.obj F)
    (hp : IsPullback
      (CheckedRoot.matchingMap R (Over.mk (𝟙 F)) i ≫
        prod.map (𝟙 _) (finitePowerMap (coprod.inr : F ⟶ OptionSyntax.obj F) i.val))
      (R.ruleConclusion (Over.mk (𝟙 F)) i) v coprod.inr) :
    IsPullback (successfulInput R i) (R.conclusion i) v coprod.inr := by
  apply hp.of_iso' (identityRuleIso R i) (Iso.refl _) (Iso.refl _) (Iso.refl _)
  · simp [identityRuleIso,successfulInput,CheckedRoot.matchingMap,prod.comp_lift]
  · simp [identityRuleIso,RulePresentation.ruleConclusion]
  · simp
  · simp

end RootGeometry

private theorem ordinaryMap_hom_ext {I : Type} [Finite I] (X : I → PredicateCategory 𝗣𝗔)
    {Y : NumericalTuples.Object} (f g : K.obj (∐ X) ⟶ Y)
    (hh : ∀ i, K.map (Sigma.ι X i) ≫ f = K.map (Sigma.ι X i) ≫ g) : f = g := by
  apply (cancel_epi (sigmaComparison K X)).mp
  apply Sigma.hom_ext
  intro i
  simpa only [ι_comp_sigmaComparison_assoc] using hh i

def optionIso (F : PredicateCategory 𝗣𝗔) : K.obj (OptionSyntax.obj F) ≅ OptionSyntax.obj (K.obj F) :=
  (asIso (coprodComparison K (⊤_ (PredicateCategory 𝗣𝗔)) F)).symm ≪≫
    coprod.mapIso (asIso (terminalComparison K)) (Iso.refl _)

@[simp,reassoc] theorem optionIso_inr (F : PredicateCategory 𝗣𝗔) :
    K.map (coprod.inr : F ⟶ OptionSyntax.obj F) ≫ (optionIso F).hom = coprod.inr := by
  simp only [optionIso,Iso.trans_hom,Iso.symm_hom,asIso_inv,coprod.mapIso_hom,
    asIso_hom,Iso.refl_hom,map_inr_inv_coprodComparison_assoc,coprod.inr_map,Category.id_comp]

@[simp,reassoc] theorem optionIso_inl (F : PredicateCategory 𝗣𝗔) :
    K.map (coprod.inl : ⊤_ (PredicateCategory 𝗣𝗔) ⟶ OptionSyntax.obj F) ≫ (optionIso F).hom =
      terminalComparison K ≫ coprod.inl := by
  simp only [optionIso,Iso.trans_hom,Iso.symm_hom,asIso_inv,coprod.mapIso_hom,
    asIso_hom,Iso.refl_hom,map_inl_inv_coprodComparison_assoc,coprod.inl_map]

def optionPowerIso (F : PredicateCategory 𝗣𝗔) (n : ℕ) :
    finitePower (K.obj (OptionSyntax.obj F)) n ≅ finitePower (OptionSyntax.obj (K.obj F)) n where
  hom := finitePowerMap (optionIso F).hom n
  inv := finitePowerMap (optionIso F).inv n
  hom_inv_id := by rw [← finitePowerMap_comp,Iso.hom_inv_id,finitePowerMap_id]
  inv_hom_id := by rw [← finitePowerMap_comp,Iso.inv_hom_id,finitePowerMap_id]

variable {F : PredicateCategory 𝗣𝗔} {N : ℕ} (R : RulePresentation F N)

/-- The rule-instance component of the ordinary input comparison is identity. -/
def rootInputIso (i : Fin (N+1)) :
    K.obj (R.instances i ⨯ finitePower (OptionSyntax.obj F) i.val) ≅
      (interpretedRules R).instances i ⨯ finitePower (OptionSyntax.obj (K.obj F)) i.val :=
  ordinaryInputIso R (OptionSyntax.obj F) i ≪≫
    prod.mapIso (Iso.refl _) (optionPowerIso F i.val)

@[simp,reassoc] theorem rootInputIso_fst (i : Fin (N+1)) :
    (rootInputIso R i).hom ≫ prod.fst = K.map prod.fst := by
  simp [rootInputIso]

@[simp,reassoc] theorem rootInputIso_snd (i : Fin (N+1)) :
    (rootInputIso R i).hom ≫ prod.snd =
      K.map prod.snd ≫ (finitePowerIso (OptionSyntax.obj F) i.val).hom ≫
        finitePowerMap (optionIso F).hom i.val := by
  simp only [rootInputIso,Iso.trans_hom,prod.mapIso_hom,Iso.refl_hom,Category.assoc,
    prod.map_snd,ordinaryInputIso_snd_assoc,optionPowerIso]

/-- The successful root input is determined by its label and prescribed
premise tuple. This equation includes arity zero. -/
theorem rootInputIso_matching (i : Fin (N+1)) :
    K.map (prod.lift (𝟙 (R.instances i))
      (R.premises i ≫ finitePowerMap (coprod.inr : F ⟶ OptionSyntax.obj F) i.val)) ≫
        (rootInputIso R i).hom =
      prod.lift (𝟙 ((interpretedRules R).instances i))
        ((interpretedRules R).premises i ≫
          finitePowerMap (coprod.inr : K.obj F ⟶ OptionSyntax.obj (K.obj F)) i.val) := by
  apply prod.hom_ext
  · simp [← Functor.map_comp]
    rfl
  · simp only [Category.assoc,rootInputIso_snd,← Functor.map_comp_assoc,prod.lift_snd]
    rw [Functor.map_comp_assoc]
    change K.map (R.premises i) ≫ K.map
        (finitePowerMap (coprod.inr : F ⟶ OptionSyntax.obj F) i.val) ≫
          (finitePowerIso (OptionSyntax.obj F) i.val).hom ≫ finitePowerMap (optionIso F).hom i.val =
      (K.map (R.premises i) ≫ (finitePowerIso F i.val).hom) ≫
        finitePowerMap (coprod.inr : K.obj F ⟶ OptionSyntax.obj (K.obj F)) i.val
    have hn := finitePowerIso_natural (coprod.inr : F ⟶ OptionSyntax.obj F) i.val
    have he := congrArg (fun k => K.map (R.premises i) ≫ k ≫
      finitePowerMap (optionIso F).hom i.val) hn
    have hp : finitePowerMap (K.map (coprod.inr : F ⟶ OptionSyntax.obj F)) i.val ≫
        finitePowerMap (optionIso F).hom i.val =
      finitePowerMap (coprod.inr : K.obj F ⟶ OptionSyntax.obj (K.obj F)) i.val := by
      rw [← finitePowerMap_comp,optionIso_inr]
    simpa only [Category.assoc,hp] using he

def sourceRootValidator (i : Fin (N+1)) :
    R.instances i ⨯ finitePower (OptionSyntax.obj F) i.val ⟶ OptionSyntax.obj F :=
  OptionAlgebra.component R (SuccessComparison.equality 𝗣𝗔 R) (Over.mk (𝟙 F)) i
    (R.ruleConclusion (Over.mk (𝟙 F)) i)

theorem sourceRootValidator_isPullback (i : Fin (N+1)) :
    IsPullback (RootGeometry.successfulInput R i) (R.conclusion i)
      (sourceRootValidator R i) coprod.inr :=
  RootGeometry.root_isPullback R i _ (SuccessComparison.rootComponent_isPullback 𝗣𝗔 R i)

def targetRootValidator (i : Fin (N+1)) :
    (interpretedRules R).instances i ⨯ finitePower (OptionSyntax.obj (K.obj F)) i.val ⟶
      OptionSyntax.obj (K.obj F) :=
  OptionAlgebra.component (interpretedRules R) (NumericalDerivation.ruleEquality (interpretedRules R))
    (Over.mk (𝟙 (K.obj F))) i ((interpretedRules R).ruleConclusion (Over.mk (𝟙 (K.obj F))) i)

theorem targetRootValidator_isPullback (i : Fin (N+1)) :
    IsPullback (RootGeometry.successfulInput (interpretedRules R) i) ((interpretedRules R).conclusion i)
      (targetRootValidator R i) coprod.inr :=
  RootGeometry.root_isPullback (interpretedRules R) i _
    (SuccessComparisonCore.rootComponent_isPullback NumericalDerivation.interpretation
      (interpretedRules R) (NumericalDerivation.ruleEquality (interpretedRules R)) i)

/-- The transported PA validator is fixed by its exact original-rule
success pullback. This proves comparison, rather than requiring a
standard extensional correctness premise. -/
theorem rootValidator_comparison (i : Fin (N+1)) :
    K.map (sourceRootValidator R i) ≫ (optionIso F).hom =
      (rootInputIso R i).hom ≫ targetRootValidator R i := by
  let v := (rootInputIso R i).inv ≫ K.map (sourceRootValidator R i) ≫ (optionIso F).hom
  have hv : IsPullback (RootGeometry.successfulInput (interpretedRules R) i)
      ((interpretedRules R).conclusion i) v coprod.inr := by
    apply ((sourceRootValidator_isPullback R i).map K).of_iso
      (Iso.refl _) (rootInputIso R i) (Iso.refl _) (optionIso F)
    · simpa only [Iso.refl_hom,Category.id_comp,RootGeometry.successfulInput] using
        rootInputIso_matching R i
    · simp only [Iso.refl_hom,Category.id_comp,Category.comp_id,interpretedRules]
    · simp [v]
    · simp
  have he := validator_unique (RootGeometry.successfulInput (interpretedRules R) i)
    ((interpretedRules R).conclusion i) v (targetRootValidator R i) hv
      (targetRootValidator_isPullback R i)
  have hh := congrArg (fun k => (rootInputIso R i).hom ≫ k) he
  simpa only [v,← Category.assoc,Iso.hom_inv_id,Category.id_comp] using hh

def sourceValidatorStr :
    (SyntacticDerivation.PolynomialComparison.ordinary R).obj (OptionSyntax.obj F) ⟶ OptionSyntax.obj F :=
  (SuccessComparison.validator 𝗣𝗔 R).str

def targetValidatorStr :
    (SyntacticDerivation.PolynomialComparison.ordinary (interpretedRules R)).obj
      (OptionSyntax.obj (K.obj F)) ⟶ OptionSyntax.obj (K.obj F) :=
  (NumericalDerivation.validator (interpretedRules R)).str

/-- Constructor compatibility of the actual option validator for every
finite rule signature, with all premise coordinates retained. -/
theorem validator_constructor :
    (mappedOrdinaryAlgebra R (SuccessComparison.validator 𝗣𝗔 R)).str ≫ (optionIso F).hom =
      (SyntacticDerivation.PolynomialComparison.ordinary (interpretedRules R)).map
        (optionIso F).hom ≫ (NumericalDerivation.validator (interpretedRules R)).str := by
  change (ordinaryObjectIso R (OptionSyntax.obj F)).inv ≫ K.map (sourceValidatorStr R) ≫
      (optionIso F).hom =
    (SyntacticDerivation.PolynomialComparison.ordinary (interpretedRules R)).map (optionIso F).hom ≫
      targetValidatorStr R
  apply (cancel_epi (ordinaryObjectIso R (OptionSyntax.obj F)).hom).mp
  rw [Iso.hom_inv_id_assoc]
  apply ordinaryMap_hom_ext (fun i : Fin (N+1) => R.instances i ⨯ finitePower (OptionSyntax.obj F) i.val)
  intro i
  rw [← Functor.map_comp_assoc]
  simp only [sourceValidatorStr,SuccessComparison.validator,OptionAlgebra.validator,Sigma.ι_comp_desc]
  rw [ordinaryObjectIso_iota_assoc]
  simp only [SyntacticDerivation.PolynomialComparison.ordinary,Sigma.ι_map_assoc,
    targetValidatorStr,NumericalDerivation.validator,SuccessComparisonCore.validator,OptionAlgebra.validator,
    Sigma.ι_comp_desc]
  change K.map (sourceRootValidator R i) ≫ (optionIso F).hom =
    (ordinaryInputIso R (OptionSyntax.obj F) i).hom ≫
      prod.map (𝟙 _) (finitePowerMap (optionIso F).hom i.val) ≫ targetRootValidator R i
  exact rootValidator_comparison R i

def validatorAlgebraIso :
    mappedOrdinaryAlgebra R (SuccessComparison.validator 𝗣𝗔 R) ≅
      NumericalDerivation.validator (interpretedRules R) :=
  Endofunctor.Algebra.isoMk (optionIso F) (validator_constructor R).symm

/-- The source fold is mapped as a genuine algebra morphism and then
uses the proved validator algebra comparison. -/
def mappedValidatorFold :
    mappedOrdinaryAlgebra R (SyntacticDerivation.ordinaryTree 𝗣𝗔 R) ⟶
      NumericalDerivation.validator (interpretedRules R) :=
  mappedOrdinaryHom R (SyntacticDerivation.validatorFold 𝗣𝗔 R) ≫ (validatorAlgebraIso R).hom

theorem mappedValidatorFold_arrow :
    (mappedValidatorFold R).f = K.map (SyntacticDerivation.validatorFold 𝗣𝗔 R).f ≫ (optionIso F).hom := rfl

end CategoricalEssentialIncompleteness.V46.NumericalDerivationInterpretation
