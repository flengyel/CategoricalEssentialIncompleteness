/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SyntacticDerivationSuccessComparisonCore
public import CategoricalEssentialIncompleteness.V46SyntacticDerivationSuccessTransport
public import CategoricalEssentialIncompleteness.V46SyntacticDerivationAlgebraAdjunction
public import CategoricalEssentialIncompleteness.V46SyntacticSyntaxOneSortTotal
public import CategoricalEssentialIncompleteness.V46ConcreteDecidableVariables

/-! Lemma 6.8 in the total split program category, for arbitrary rule data. -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
namespace CategoricalEssentialIncompleteness.V46.SyntacticDerivation
variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] {F : TotalSplit T} {N : ℕ}
  (R : RulePresentation F N)

abbrev totalInterpretation := (predicateEquivalence T).inverse ⋙ PredicateInterpretation.allModels T

def totalRuleEquality (_R : RulePresentation F N) (i : Fin (N + 1)) : DecidableVariables (finitePower F i.val) :=
  ConcreteDecidableVariables.total T _

abbrev totalValidator : Endofunctor.Algebra (PolynomialComparison.ordinary R) :=
  SuccessComparisonCore.validator R (totalRuleEquality T R)

def totalOrdinaryTree : Endofunctor.Algebra (PolynomialComparison.ordinary R) :=
  PolynomialComparison.mappedAlgebra R
    (SyntacticSyntax.totalOneSortAlgebra T (PolynomialComparison.coefficients R) N)

def totalOrdinaryTreeInitial : IsInitial (totalOrdinaryTree T R) :=
  PolynomialComparison.mappedInitial R _
    (SyntacticSyntax.totalOneSortInitial T (PolynomialComparison.coefficients R) N)

def totalValidatorFold : totalOrdinaryTree T R ⟶ totalValidator T R :=
  (totalOrdinaryTreeInitial T R).to _

def totalValidatedSlice : Endofunctor.Algebra
    (SliceInitial.functor (PolynomialComparison.ordinary R) (totalValidator T R)) :=
  SliceInitial.algebra _ _ (totalOrdinaryTree T R) (totalOrdinaryTreeInitial T R)

def totalSuccessComparison :
    SliceInitial.functor (PolynomialComparison.ordinary R) (totalValidator T R) ⋙
        Over.pullback (coprod.inr : F ⟶ OptionSyntax.obj F) ≅
      Over.pullback (coprod.inr : F ⟶ OptionSyntax.obj F) ⋙ R.inference :=
  SuccessComparisonCore.comparison (totalInterpretation T) R (totalRuleEquality T R)

def totalChosenAlgebra : Endofunctor.Algebra R.inference :=
  AlgebraAdjunction.leftAlgebra (totalSuccessComparison T R) (totalValidatedSlice T R)

def totalChosenInitial : IsInitial (totalChosenAlgebra T R) :=
  AlgebraAdjunction.initial (SuccessAdjunction.adjunction F)
    (totalSuccessComparison T R) (totalValidatedSlice T R)
    (SliceInitial.initial _ _ (totalOrdinaryTree T R) (totalOrdinaryTreeInitial T R))

/-- The carrier is presented by the explicit successful-word Sigma-one predicate,
transported by the predicate/program equivalence. -/
def totalDerivationCarrier : Carrier :=
  SuccessTransport.carrier T (totalValidatorFold T R).f

def totalDerivationConclusionGraph : GraphMorphism T (totalDerivationCarrier T R)
    ((predicateEquivalence T).inverse.obj F) :=
  SuccessCarrier.conclusion (SuccessTransport.predicateValidator T (totalValidatorFold T R).f)

def totalDerivationConclusion : (predicateEquivalence T).functor.obj (totalDerivationCarrier T R) ⟶ F :=
  SuccessTransport.conclusion T (totalValidatorFold T R).f

def totalDerivationAlgebra : Endofunctor.Algebra R.inference :=
  SuccessTransport.algebra T (totalValidatorFold T R).f R.inference (totalChosenAlgebra T R).str

def totalDerivationInitial : IsInitial (totalDerivationAlgebra T R) :=
  SuccessTransport.initial T (totalValidatorFold T R).f R.inference (totalChosenAlgebra T R).str
    (totalChosenInitial T R)

def totalDerivationCodeIso : totalDerivationAlgebra T R ≅ totalChosenAlgebra T R :=
  SuccessTransport.algebraIso T (totalValidatorFold T R).f R.inference (totalChosenAlgebra T R).str

theorem totalDerivation_carrier : (totalDerivationAlgebra T R).a.left =
    (predicateEquivalence T).functor.obj (totalDerivationCarrier T R) := rfl

theorem totalDerivation_conclusion :
    (totalDerivationAlgebra T R).a = Over.mk (totalDerivationConclusion T R) := rfl

/-- The inclusion remembers the original rule-labelled postfix word. -/
def totalTreeInclusion : (totalDerivationAlgebra T R).a.left ⟶ (totalOrdinaryTree T R).a :=
  SuccessTransport.inclusion T (totalValidatorFold T R).f

/-- The program-category constructor retains the original rule label and the ordered child
codes. The validation output remains existential. -/
theorem totalDerivationConstructor_tree :
    (totalDerivationAlgebra T R).str.left ≫ totalTreeInclusion T R =
      InputGeometry.forget R (totalDerivationAlgebra T R).a ≫
        (PolynomialComparison.ordinary R).map (totalTreeInclusion T R) ≫
          (totalOrdinaryTree T R).str := by
  let v : @Quiver.Hom (TotalSplit T) inferInstance (totalOrdinaryTree T R).a
      (OptionSyntax.obj F) := (totalValidatorFold T R).f
  let j := pullback.fst v (coprod.inr : F ⟶ OptionSyntax.obj F)
  let e := SuccessTransport.overIso T v
  have hc : (totalChosenAlgebra T R).str.left ≫ j =
      SuccessComparisonCore.input R (Over.mk v) ≫ (totalOrdinaryTree T R).str := by
    have hp : ((SuccessComparisonCore.success (F := F)).map (totalValidatedSlice T R).str).left ≫ j =
        pullback.fst ((SliceInitial.functor (PolynomialComparison.ordinary R)
          (SuccessComparisonCore.validator R (totalRuleEquality T R))).obj (Over.mk v)).hom
          (coprod.inr : F ⟶ OptionSyntax.obj F) ≫ (totalOrdinaryTree T R).str := by
      simp [j, v, Over.pullback, totalValidatedSlice, SliceInitial.algebra, totalValidatorFold]
    change (((SuccessComparisonCore.comparison (totalInterpretation T) R
      (totalRuleEquality T R)).inv.app (Over.mk v)).left ≫
      ((SuccessComparisonCore.success (F := F)).map (totalValidatedSlice T R).str).left) ≫ j = _
    rw [SuccessComparisonCore.comparison_inv_app, Category.assoc, hp,
      ← Category.assoc, SuccessComparisonCore.componentIso_input]
  change (SuccessTransport.algebra T v R.inference (totalChosenAlgebra T R).str).str.left ≫
    SuccessTransport.inclusion T v = _
  rw [SuccessTransport.algebra_tree, hc, SuccessComparisonCore.input_eq_forget]
  have hf : (PolynomialComparison.ordinary R).map e.hom.left ≫
      (PolynomialComparison.ordinary R).map j ≫ (totalOrdinaryTree T R).str =
      (PolynomialComparison.ordinary R).map (totalTreeInclusion T R) ≫
        (totalOrdinaryTree T R).str := by
    rw [← Category.assoc, ← Functor.map_comp]
    have hi : e.hom.left ≫ j = totalTreeInclusion T R := SuccessTransport.overIso_tree T v
    rw [hi]
  have he := congrArg (fun k => k ≫ (PolynomialComparison.ordinary R).map j ≫
      (totalOrdinaryTree T R).str) (InputGeometry.forget_natural R e.hom)
  simp only [Category.assoc]
  change (R.inference.map e.hom).left ≫
      InputGeometry.forget R ((Over.pullback (coprod.inr : F ⟶ OptionSyntax.obj F)).obj (Over.mk v)) ≫
      (PolynomialComparison.ordinary R).map j ≫ (totalOrdinaryTree T R).str =
    InputGeometry.forget R (Over.mk (SuccessTransport.conclusion T v)) ≫
      (PolynomialComparison.ordinary R).map (totalTreeInclusion T R) ≫
        (totalOrdinaryTree T R).str
  simpa only [Category.assoc, hf] using he

def totalDerivationFold (B : Endofunctor.Algebra R.inference) : totalDerivationAlgebra T R ⟶ B :=
  (totalDerivationInitial T R).to B

theorem totalDerivationFold_conclusion (B : Endofunctor.Algebra R.inference) :
    (totalDerivationFold T R B).f.left ≫ B.a.hom = totalDerivationConclusion T R :=
  Over.w (totalDerivationFold T R B).f

theorem totalDerivationFold_constructor (B : Endofunctor.Algebra R.inference) :
    (totalDerivationAlgebra T R).str ≫ (totalDerivationFold T R B).f =
      R.inference.map (totalDerivationFold T R B).f ≫ B.str :=
  (totalDerivationFold T R B).h.symm

theorem totalDerivationFold_unique (B : Endofunctor.Algebra R.inference)
    (f : totalDerivationAlgebra T R ⟶ B) : f = totalDerivationFold T R B :=
  (totalDerivationInitial T R).hom_ext f _

def totalDerivationConstructor (i : Fin (N + 1)) :
    R.ruleObject (totalDerivationAlgebra T R).a i ⟶ (totalDerivationAlgebra T R).a.left :=
  Sigma.ι (R.ruleObject (totalDerivationAlgebra T R).a) i ≫ (totalDerivationAlgebra T R).str.left

@[simp, reassoc] theorem totalDerivationConstructor_conclusion (i : Fin (N + 1)) :
    totalDerivationConstructor T R i ≫ (totalDerivationAlgebra T R).a.hom =
      R.ruleConclusion (totalDerivationAlgebra T R).a i := by
  unfold totalDerivationConstructor
  rw [Category.assoc, Over.w (totalDerivationAlgebra T R).str]
  exact Sigma.ι_comp_desc _ i

def totalNullaryDerivation : R.instances 0 ⟶ (totalDerivationAlgebra T R).a.left :=
  R.nullaryRule (totalDerivationAlgebra T R).a ≫ totalDerivationConstructor T R 0

@[simp, reassoc] theorem totalNullaryDerivation_conclusion :
    totalNullaryDerivation T R ≫ (totalDerivationAlgebra T R).a.hom = R.conclusion 0 := by
  rw [totalNullaryDerivation, Category.assoc, totalDerivationConstructor_conclusion]
  have he := congrArg (fun k => k ≫ R.conclusion 0)
    (R.nullaryRule_fst (totalDerivationAlgebra T R).a)
  simpa only [Category.assoc, Category.id_comp, RulePresentation.ruleConclusion] using he

end CategoricalEssentialIncompleteness.V46.SyntacticDerivation
