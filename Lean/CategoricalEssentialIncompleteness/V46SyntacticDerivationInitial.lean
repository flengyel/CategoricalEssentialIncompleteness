/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SyntacticDerivationSuccessComparison
public import CategoricalEssentialIncompleteness.V46SyntacticDerivationSuccessCarrier
public import CategoricalEssentialIncompleteness.V46SyntacticDerivationAlgebraAdjunction
public import CategoricalEssentialIncompleteness.V46SyntacticDerivationSliceInitial
public import CategoricalEssentialIncompleteness.V46SyntacticSyntaxOneSortInitial

/-! The actual finite-inference derivation initial algebra, for arbitrary rule data. -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
namespace CategoricalEssentialIncompleteness.V46.SyntacticDerivation
variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] {F : PredicateCategory T} {N : ℕ}
  (R : RulePresentation F N)

def ordinaryTree : Endofunctor.Algebra (PolynomialComparison.ordinary R) :=
  PolynomialComparison.mappedAlgebra R
    (SyntacticSyntax.oneSortAlgebra T (PolynomialComparison.coefficients R) N)

def ordinaryTreeInitial : IsInitial (ordinaryTree T R) :=
  PolynomialComparison.mappedInitial R _
    (SyntacticSyntax.oneSortInitial T (PolynomialComparison.coefficients R) N)

def validatorFold : ordinaryTree T R ⟶ SuccessComparison.validator T R :=
  (ordinaryTreeInitial T R).to _

def validatedSlice : Endofunctor.Algebra
    (SliceInitial.functor (PolynomialComparison.ordinary R) (SuccessComparison.validator T R)) :=
  SliceInitial.algebra _ _ (ordinaryTree T R) (ordinaryTreeInitial T R)

def chosenAlgebra : Endofunctor.Algebra R.inference :=
  AlgebraAdjunction.leftAlgebra (SuccessComparison.comparison T R) (validatedSlice T R)

def chosenInitial : IsInitial (chosenAlgebra T R) :=
  AlgebraAdjunction.initial (SuccessAdjunction.adjunction F)
    (SuccessComparison.comparison T R) (validatedSlice T R)
    (SliceInitial.initial _ _ (ordinaryTree T R) (ordinaryTreeInitial T R))

/-- The derivation code is the original rule-labelled tree code alone.
Validation and conclusion values are existential in the carrier predicate. -/
def derivationCarrier : Carrier := SuccessCarrier.carrier (validatorFold T R).f

def derivationConclusion : GraphMorphism T (derivationCarrier T R) F :=
  SuccessCarrier.conclusion (validatorFold T R).f

def derivationAlgebra : Endofunctor.Algebra R.inference :=
  SuccessCarrier.rawAlgebra (validatorFold T R).f R.inference (chosenAlgebra T R).str

/-- Lemma 5.8 for every finite rule presentation, without a given
evaluator, an assumed recursive solution, or a restriction on its nullary rules. -/
def derivationInitial : IsInitial (derivationAlgebra T R) :=
  SuccessCarrier.rawInitial (validatorFold T R).f R.inference (chosenAlgebra T R).str
    (chosenInitial T R)

theorem derivationAlgebra_carrier :
    (derivationAlgebra T R).a = Over.mk (representedArrow T (derivationConclusion T R)) := rfl

def treeInclusion : (derivationAlgebra T R).a.left ⟶ (ordinaryTree T R).a :=
  representedArrow T (SuccessCarrier.inclusion (validatorFold T R).f)

/-- The actual typed constructor keeps the original rule label and
ordered child tree codes. Validation never adds a node label or value. -/
theorem derivationConstructor_tree :
    (derivationAlgebra T R).str.left ≫ treeInclusion T R =
      InputGeometry.forget R (derivationAlgebra T R).a ≫
        (PolynomialComparison.ordinary R).map (treeInclusion T R) ≫ (ordinaryTree T R).str := by
  let v : @Quiver.Hom (PredicateCategory T) inferInstance (ordinaryTree T R).a
      (OptionSyntax.obj F) := (validatorFold T R).f
  let j := pullback.fst v (coprod.inr : F ⟶ OptionSyntax.obj F)
  let e := SuccessCarrier.overIso v
  have hc : (chosenAlgebra T R).str.left ≫ j =
      SuccessComparison.input T R (Over.mk v) ≫ (ordinaryTree T R).str := by
    have hp : ((SuccessComparison.success T).map (validatedSlice T R).str).left ≫ j =
        pullback.fst ((SliceInitial.functor (PolynomialComparison.ordinary R)
          (SuccessComparison.validator T R)).obj (Over.mk v)).hom
          (coprod.inr : F ⟶ OptionSyntax.obj F) ≫ (ordinaryTree T R).str := by
      simp [j, v, Over.pullback, validatedSlice, SliceInitial.algebra, validatorFold]
    change (((SuccessComparison.comparison T R).inv.app (Over.mk v)).left ≫
      ((SuccessComparison.success T).map (validatedSlice T R).str).left) ≫ j = _
    rw [SuccessComparison.comparison_inv_app, Category.assoc, hp,
      ← Category.assoc, SuccessComparison.componentIso_input]
  change (SuccessCarrier.rawAlgebra v R.inference (chosenAlgebra T R).str).str.left ≫
    representedArrow T (SuccessCarrier.inclusion v) = _
  rw [SuccessCarrier.rawAlgebra_tree, hc, SuccessComparison.input_eq_forget]
  have hf : (PolynomialComparison.ordinary R).map e.hom.left ≫
      (PolynomialComparison.ordinary R).map j ≫ (ordinaryTree T R).str =
      (PolynomialComparison.ordinary R).map (treeInclusion T R) ≫ (ordinaryTree T R).str := by
    rw [← Category.assoc, ← Functor.map_comp]
    have hi : e.hom.left ≫ j = treeInclusion T R := SuccessCarrier.overIso_tree v
    rw [hi]
  have he := congrArg (fun k => k ≫ (PolynomialComparison.ordinary R).map j ≫ (ordinaryTree T R).str)
    (InputGeometry.forget_natural R e.hom)
  simp only [Category.assoc]
  change (R.inference.map e.hom).left ≫
      InputGeometry.forget R ((Over.pullback (coprod.inr : F ⟶ OptionSyntax.obj F)).obj (Over.mk v)) ≫
      (PolynomialComparison.ordinary R).map j ≫ (ordinaryTree T R).str =
    InputGeometry.forget R (Over.mk (representedArrow T (SuccessCarrier.conclusion v))) ≫
      (PolynomialComparison.ordinary R).map (treeInclusion T R) ≫ (ordinaryTree T R).str
  simpa only [Category.assoc, hf] using he

def derivationFold (B : Endofunctor.Algebra R.inference) : derivationAlgebra T R ⟶ B :=
  (derivationInitial T R).to B

theorem derivationFold_conclusion (B : Endofunctor.Algebra R.inference) :
    (derivationFold T R B).f.left ≫ B.a.hom = representedArrow T (derivationConclusion T R) :=
  Over.w (derivationFold T R B).f

theorem derivationFold_constructor (B : Endofunctor.Algebra R.inference) :
    (derivationAlgebra T R).str ≫ (derivationFold T R B).f =
      R.inference.map (derivationFold T R B).f ≫ B.str :=
  (derivationFold T R B).h.symm

theorem derivationFold_unique (B : Endofunctor.Algebra R.inference)
    (f : derivationAlgebra T R ⟶ B) : f = derivationFold T R B :=
  (derivationInitial T R).hom_ext f _

def derivationConstructor (i : Fin (N + 1)) :
    R.ruleObject (derivationAlgebra T R).a i ⟶ (derivationAlgebra T R).a.left :=
  Sigma.ι (R.ruleObject (derivationAlgebra T R).a) i ≫ (derivationAlgebra T R).str.left

@[simp, reassoc] theorem derivationConstructor_conclusion (i : Fin (N + 1)) :
    derivationConstructor T R i ≫ (derivationAlgebra T R).a.hom =
      R.ruleConclusion (derivationAlgebra T R).a i := by
  unfold derivationConstructor
  rw [Category.assoc, Over.w (derivationAlgebra T R).str]
  exact Sigma.ι_comp_desc _ i

/-- Every nullary rule instance is a derivation constructor, independently
of whether the judgement or any premise carrier has a global element. -/
def nullaryDerivation : R.instances 0 ⟶ (derivationAlgebra T R).a.left :=
  R.nullaryRule (derivationAlgebra T R).a ≫ derivationConstructor T R 0

@[simp, reassoc] theorem nullaryDerivation_conclusion :
    nullaryDerivation T R ≫ (derivationAlgebra T R).a.hom = R.conclusion 0 := by
  rw [nullaryDerivation, Category.assoc, derivationConstructor_conclusion]
  have he := congrArg (fun k => k ≫ R.conclusion 0)
    (R.nullaryRule_fst (derivationAlgebra T R).a)
  simpa only [Category.assoc, Category.id_comp, RulePresentation.ruleConclusion] using he

end CategoricalEssentialIncompleteness.V46.SyntacticDerivation
