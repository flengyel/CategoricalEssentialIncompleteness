/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ConcreteNamedComparisonResults
public import CategoricalEssentialIncompleteness.V46ConcreteNamedComparisonPlainOccurrences
public import CategoricalEssentialIncompleteness.V46NamedPostfixPlainComparison

/-! # Computed substitution states with the actual plain-syntax parameters -/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticLists
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax

namespace CategoricalEssentialIncompleteness.V46.ConcreteNamedComparison

def plainSyntaxCarrier (V : Carrier) (σ π : ℕ → Carrier) (d : ℕ) (formula : Bool) : Carrier :=
  Postfix.plainCarrier formula (SyntaxPolynomial.termExpression V σ d) (SyntaxPolynomial.formulaExpression V π d)

variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
variable (U V : PredicateCategory T) (σ π : ℕ → PredicateCategory T) (d : ℕ)

def syntaxPlainIso (formula : Bool) :
    CategoryTheory.Iso (C := PredicateCategory T) (syntaxCarrier V σ π d formula)
      (plainSyntaxCarrier V σ π d formula) :=
  Postfix.plainCarrierIso T formula (SyntaxPolynomial.termExpression V σ d) (SyntaxPolynomial.formulaExpression V π d)

def plainParameterIso :
    (U ⨯ (syntaxCarrier V σ π d false : PredicateCategory T)) ≅
      (U ⨯ (plainSyntaxCarrier V σ π d false : PredicateCategory T)) :=
  prod.mapIso (Iso.refl U) (syntaxPlainIso T V σ π d false)

/-- Both the replacement and the source word use their actual
constructor-preserving parser comparison. The parameter objects are
not identified merely because their coordinates have the same values. -/
def plainInputIso (formula : Bool) :
    ((U ⨯ (syntaxCarrier V σ π d false : PredicateCategory T)) ⨯
      (syntaxCarrier V σ π d formula : PredicateCategory T)) ≅
      ((U ⨯ (plainSyntaxCarrier V σ π d false : PredicateCategory T)) ⨯
        (plainSyntaxCarrier V σ π d formula : PredicateCategory T)) :=
  prod.mapIso (plainParameterIso T U V σ π d) (syntaxPlainIso T V σ π d formula)

def computedPlainOriginal (formula : Bool) :
    @Quiver.Hom (PredicateCategory T) inferInstance
      ((U ⨯ (plainSyntaxCarrier V σ π d false : PredicateCategory T)) ⨯
        (plainSyntaxCarrier V σ π d formula : PredicateCategory T)) (plainSyntaxCarrier V σ π d formula) :=
  (plainInputIso T U V σ π d formula).inv ≫
    payloadProjectionArrow T U V σ π d .original formula ≫ (syntaxPlainIso T V σ π d formula).hom

def computedPlainTermResult :
    @Quiver.Hom (PredicateCategory T) inferInstance
      ((U ⨯ (plainSyntaxCarrier V σ π d false : PredicateCategory T)) ⨯
        (plainSyntaxCarrier V σ π d false : PredicateCategory T)) (plainSyntaxCarrier V σ π d false) :=
  (plainInputIso T U V σ π d false).inv ≫ computedTermResult T U V σ π d ≫
    (syntaxPlainIso T V σ π d false).hom

def computedPlainFormulaResult :
    @Quiver.Hom (PredicateCategory T) inferInstance
      ((U ⨯ (plainSyntaxCarrier V σ π d false : PredicateCategory T)) ⨯
        (plainSyntaxCarrier V σ π d true : PredicateCategory T))
      (OptionSyntax.obj (plainSyntaxCarrier V σ π d true : PredicateCategory T)) :=
  (plainInputIso T U V σ π d true).inv ≫ computedFormulaResult T U V σ π d ≫
    OptionSyntax.map (syntaxPlainIso T V σ π d true).hom

def computedPlainTermState :
    constantFamily (U ⨯ (plainSyntaxCarrier V σ π d false : PredicateCategory T))
      (plainSyntaxCarrier V σ π d false : PredicateCategory T) ⟶
    constantFamily (U ⨯ (plainSyntaxCarrier V σ π d false : PredicateCategory T))
      ((plainSyntaxCarrier V σ π d false : PredicateCategory T) ⨯
        (plainSyntaxCarrier V σ π d false : PredicateCategory T)) :=
  Over.homMk (prod.lift prod.fst (prod.lift (computedPlainOriginal T U V σ π d false)
    (computedPlainTermResult T U V σ π d))) (prod.lift_fst _ _)

def computedPlainFormulaState :
    constantFamily (U ⨯ (plainSyntaxCarrier V σ π d false : PredicateCategory T))
      (plainSyntaxCarrier V σ π d true : PredicateCategory T) ⟶
    constantFamily (U ⨯ (plainSyntaxCarrier V σ π d false : PredicateCategory T))
      ((plainSyntaxCarrier V σ π d true : PredicateCategory T) ⨯
        OptionSyntax.obj (plainSyntaxCarrier V σ π d true : PredicateCategory T)) :=
  Over.homMk (prod.lift prod.fst (prod.lift (computedPlainOriginal T U V σ π d true)
    (computedPlainFormulaResult T U V σ π d))) (prod.lift_fst _ _)

section Models
variable (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T]

theorem plainInputIso_inv_coordinates (formula : Bool)
    (q : Obj T M ((U ⨯ (plainSyntaxCarrier V σ π d false : PredicateCategory T)) ⨯
      (plainSyntaxCarrier V σ π d formula : PredicateCategory T))) :
    let z := (F T M).map (plainInputIso T U V σ π d formula).inv q
    ((F T M).map (prod.fst : U ⨯ (syntaxCarrier V σ π d false : PredicateCategory T) ⟶ U)
        ((F T M).map prod.fst z)).val =
      ((F T M).map (prod.fst : U ⨯ (plainSyntaxCarrier V σ π d false : PredicateCategory T) ⟶ U)
        ((F T M).map prod.fst q)).val ∧
    ((F T M).map (prod.snd : U ⨯ (syntaxCarrier V σ π d false : PredicateCategory T) ⟶ _)
        ((F T M).map prod.fst z)).val =
      ((F T M).map (prod.snd : U ⨯ (plainSyntaxCarrier V σ π d false : PredicateCategory T) ⟶ _)
        ((F T M).map prod.fst q)).val ∧
    ((F T M).map prod.snd z).val = ((F T M).map prod.snd q).val := by
  dsimp only
  have hp := model_map_fst T M (plainParameterIso T U V σ π d).inv
    (syntaxPlainIso T V σ π d formula).inv q
  have hw := model_map_snd T M (plainParameterIso T U V σ π d).inv
    (syntaxPlainIso T V σ π d formula).inv q
  refine ⟨?_,?_,?_⟩
  · have hx := congrArg (fun z : Obj T M (U ⨯ (syntaxCarrier V σ π d false : PredicateCategory T)) =>
      (F T M).map (prod.fst : U ⨯ (syntaxCarrier V σ π d false : PredicateCategory T) ⟶ U) z) hp
    erw [model_map_fst T M (𝟙 U) (syntaxPlainIso T V σ π d false).inv,
      Functor.map_id_apply] at hx
    exact congrArg Subtype.val hx
  · have ht := congrArg (fun z : Obj T M (U ⨯ (syntaxCarrier V σ π d false : PredicateCategory T)) =>
      ((F T M).map (prod.snd : U ⨯ (syntaxCarrier V σ π d false : PredicateCategory T) ⟶ _) z).val) hp
    erw [model_map_snd T M (𝟙 U) (syntaxPlainIso T V σ π d false).inv,
      plainCarrierIso_inv_value T M false (SyntaxPolynomial.termExpression V σ d)
        (SyntaxPolynomial.formulaExpression V π d)] at ht
    exact ht
  · exact (congrArg Subtype.val hw).trans (plainCarrierIso_inv_value T M formula
      (SyntaxPolynomial.termExpression V σ d) (SyntaxPolynomial.formulaExpression V π d) _)

variable [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

theorem computedPlainTermResult_value
    (q : Obj T M ((U ⨯ (plainSyntaxCarrier V σ π d false : PredicateCategory T)) ⨯
      (plainSyntaxCarrier V σ π d false : PredicateCategory T))) :
    ((F T M).map (computedPlainTermResult T U V σ π d) q).val =
      ConcreteNamedSubstitution.substitutionResult V σ π d
        ((F T M).map (prod.fst : U ⨯ (plainSyntaxCarrier V σ π d false : PredicateCategory T) ⟶ U)
          ((F T M).map prod.fst q)).val
        ((F T M).map (prod.snd : U ⨯ (plainSyntaxCarrier V σ π d false : PredicateCategory T) ⟶ _)
          ((F T M).map prod.fst q)).val
        ((F T M).map prod.snd q).val := by
  let z := (F T M).map (plainInputIso T U V σ π d false).inv q
  change ((F T M).map ((plainInputIso T U V σ π d false).inv ≫
    computedTermResult T U V σ π d ≫ (syntaxPlainIso T V σ π d false).hom) q).val = _
  rw [Functor.map_comp_apply,Functor.map_comp_apply]
  erw [NamedPostfixPlainComparison.plainCarrierIso_value T M false
    (SyntaxPolynomial.termExpression V σ d) (SyntaxPolynomial.formulaExpression V π d)]
  have hv := rawResultArrow_value T U V σ π d M false z
  have hc := plainInputIso_inv_coordinates T U V σ π d M false q
  have h₁ := congrArg₂ (fun x t => ConcreteNamedSubstitution.substitutionResult V σ π d x t
    ((F T M).map prod.snd z).val) hc.1 hc.2.1
  have h₂ := congrArg (ConcreteNamedSubstitution.substitutionResult V σ π d
    ((F T M).map (prod.fst : U ⨯ (plainSyntaxCarrier V σ π d false : PredicateCategory T) ⟶ U)
      ((F T M).map prod.fst q)).val
    ((F T M).map (prod.snd : U ⨯ (plainSyntaxCarrier V σ π d false : PredicateCategory T) ⟶ _)
      ((F T M).map prod.fst q)).val) hc.2.2
  exact hv.trans (h₁.trans h₂)

theorem computedPlainFormulaResult_value
    (q : Obj T M ((U ⨯ (plainSyntaxCarrier V σ π d false : PredicateCategory T)) ⨯
      (plainSyntaxCarrier V σ π d true : PredicateCategory T))) :
    optionCode T M (plainSyntaxCarrier V σ π d true)
      ((F T M).map (computedPlainFormulaResult T U V σ π d) q) =
      ConcreteNamedSubstitution.substitutionResult V σ π d
        ((F T M).map (prod.fst : U ⨯ (plainSyntaxCarrier V σ π d false : PredicateCategory T) ⟶ U)
          ((F T M).map prod.fst q)).val
        ((F T M).map (prod.snd : U ⨯ (plainSyntaxCarrier V σ π d false : PredicateCategory T) ⟶ _)
          ((F T M).map prod.fst q)).val
        ((F T M).map prod.snd q).val := by
  let z := (F T M).map (plainInputIso T U V σ π d true).inv q
  change optionCode T M (plainSyntaxCarrier V σ π d true)
    ((F T M).map ((plainInputIso T U V σ π d true).inv ≫
      computedFormulaResult T U V σ π d ≫ OptionSyntax.map (syntaxPlainIso T V σ π d true).hom) q) = _
  rw [Functor.map_comp_apply,Functor.map_comp_apply]
  erw [optionCode_map_identity T M (syntaxPlainIso T V σ π d true).hom
    (fun word => NamedPostfixPlainComparison.plainCarrierIso_value T M true
      (SyntaxPolynomial.termExpression V σ d) (SyntaxPolynomial.formulaExpression V π d) word)]
  rw [computedFormulaResult_code]
  have hv := rawResultArrow_value T U V σ π d M true z
  have hc := plainInputIso_inv_coordinates T U V σ π d M true q
  have h₁ := congrArg₂ (fun x t => ConcreteNamedSubstitution.substitutionResult V σ π d x t
    ((F T M).map prod.snd z).val) hc.1 hc.2.1
  have h₂ := congrArg (ConcreteNamedSubstitution.substitutionResult V σ π d
    ((F T M).map (prod.fst : U ⨯ (plainSyntaxCarrier V σ π d false : PredicateCategory T) ⟶ U)
      ((F T M).map prod.fst q)).val
    ((F T M).map (prod.snd : U ⨯ (plainSyntaxCarrier V σ π d false : PredicateCategory T) ⟶ _)
      ((F T M).map prod.fst q)).val) hc.2.2
  exact hv.trans (h₁.trans h₂)

end Models
end CategoricalEssentialIncompleteness.V46.ConcreteNamedComparison
