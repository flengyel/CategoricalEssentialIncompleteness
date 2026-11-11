/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerDerivationTrees
public import CategoricalEssentialIncompleteness.V46MillerSyntaxUniformInitial
public import CategoricalEssentialIncompleteness.V46SyntacticDerivationAlgebraAdjunction

/-! # Arbitrary finite-rule initiality for actual uniform carriers

The literal ordinary-tree algebra is initial by the proved uniform word
construction. The successful pullback uses the original ordered premise
matching, and the existing success adjunction proves its universal
property. Neither initiality nor successful-tree comparison is supplied
as a hypothesis.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.RestrictionCategory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness.V46.Miller.Derivation
open SyntacticDerivation
variable {P : Uniform.Family} {F : Total.TotalCategory P} {N : ℕ} (R : RulePresentation F N)

/-- The one-sort universal property is derived from the complete two-sort
uniform-word universal property, including arbitrary target operations. -/
def ordinaryTreeInitial : IsInitial (ordinaryTree R) :=
  PolynomialComparison.mappedInitial R (oneSortTree R)
    (SyntacticSyntax.projectedConstructorInitial (PolynomialComparison.coefficients R) N
      (treePair R) (Syntax.Raw.wordInitial (treePolynomial R) .unit))

def validatorFold : ordinaryTree R ⟶ validator R := (ordinaryTreeInitial R).to _

def validatedSlice : Endofunctor.Algebra
    (SliceInitial.functor (PolynomialComparison.ordinary R) (validator R)) :=
  SliceInitial.algebra _ _ (ordinaryTree R) (ordinaryTreeInitial R)

/-- The source carrier is exactly the successful pullback of the
constructed ordinary-tree validator. -/
def derivationAlgebra : Endofunctor.Algebra R.inference :=
  AlgebraAdjunction.leftAlgebra (successComparison R) (validatedSlice R)

def derivationInitial : IsInitial (derivationAlgebra R) :=
  AlgebraAdjunction.initial (SuccessAdjunction.adjunction F)
    (successComparison R) (validatedSlice R)
    (SliceInitial.initial _ _ (ordinaryTree R) (ordinaryTreeInitial R))

def conclusion : (derivationAlgebra R).a.left ⟶ F := (derivationAlgebra R).a.hom

def treeInclusion : (derivationAlgebra R).a.left ⟶ (ordinaryTree R).a :=
  pullback.fst (validatorFold R).f (coprod.inr : F ⟶ OptionSyntax.obj F)

@[simp] theorem derivation_carrier : (derivationAlgebra R).a =
    Over.mk (pullback.snd (validatorFold R).f (coprod.inr : F ⟶ OptionSyntax.obj F)) := rfl

theorem successful_pullback :
    IsPullback (treeInclusion R) (conclusion R) (validatorFold R).f
      (coprod.inr : F ⟶ OptionSyntax.obj F) :=
  IsPullback.of_hasPullback _ _

/-- Successful constructors retain the original rule label and ordered
children. The validation result is not an additional tree label. -/
theorem constructor_tree :
    (derivationAlgebra R).str.left ≫ treeInclusion R =
      InputGeometry.forget R (derivationAlgebra R).a ≫
        (PolynomialComparison.ordinary R).map (treeInclusion R) ≫ (ordinaryTree R).str := by
  let v := (validatorFold R).f
  let j := pullback.fst v (coprod.inr : F ⟶ OptionSyntax.obj F)
  have hp : ((SuccessComparisonCore.success (F := F)).map (validatedSlice R).str).left ≫ j =
      pullback.fst ((SliceInitial.functor (PolynomialComparison.ordinary R) (validator R)).obj
        (Over.mk v)).hom (coprod.inr : F ⟶ OptionSyntax.obj F) ≫ (ordinaryTree R).str := by
    simp [j,v,Over.pullback,validatedSlice,SliceInitial.algebra,validatorFold]
  change (((SuccessComparisonCore.comparison (interpretation (P := P)) R (ruleEquality R)).inv.app
      (Over.mk v)).left ≫ ((SuccessComparisonCore.success (F := F)).map (validatedSlice R).str).left) ≫ j = _
  rw [SuccessComparisonCore.comparison_inv_app,Category.assoc,hp,
    ← Category.assoc,SuccessComparisonCore.componentIso_input]
  simpa only [Category.assoc, treeInclusion, derivationAlgebra, AlgebraAdjunction.leftAlgebra,
    validatedSlice, SliceInitial.algebra, validatorFold, v, Functor.comp_obj,
    SuccessComparisonCore.success, Over.mk_hom] using
    congrArg (fun k => k ≫ (ordinaryTree R).str)
      (SuccessComparisonCore.input_eq_forget R (Over.mk v))

def derivationFold (B : Endofunctor.Algebra R.inference) : derivationAlgebra R ⟶ B :=
  (derivationInitial R).to B

theorem fold_conclusion (B : Endofunctor.Algebra R.inference) :
    (derivationFold R B).f.left ≫ B.a.hom = conclusion R := Over.w (derivationFold R B).f

theorem fold_constructor (B : Endofunctor.Algebra R.inference) :
    (derivationAlgebra R).str ≫ (derivationFold R B).f = R.inference.map (derivationFold R B).f ≫ B.str :=
  (derivationFold R B).h.symm

theorem fold_unique (B : Endofunctor.Algebra R.inference) (f : derivationAlgebra R ⟶ B) :
    f = derivationFold R B := (derivationInitial R).hom_ext f _

/-- Uniqueness applies to every carrier morphism satisfying the original
slice and constructor equations. -/
theorem fold_underlying_unique (B : Endofunctor.Algebra R.inference)
    (f : (derivationAlgebra R).a.left ⟶ B.a.left) (hf : f ≫ B.a.hom = conclusion R)
    (hc : R.inference.map (Over.homMk f hf) ≫ B.str =
      (derivationAlgebra R).str ≫ Over.homMk f hf) : f = (derivationFold R B).f.left := by
  exact congrArg (fun h : derivationAlgebra R ⟶ B => h.f.left)
    ((derivationInitial R).hom_ext (⟨Over.homMk f hf,hc⟩ : derivationAlgebra R ⟶ B) (derivationFold R B))

def constructor (i : Fin (N + 1)) : R.ruleObject (derivationAlgebra R).a i ⟶
    (derivationAlgebra R).a.left :=
  Sigma.ι (R.ruleObject (derivationAlgebra R).a) i ≫ (derivationAlgebra R).str.left

@[simp,reassoc] theorem constructor_conclusion (i : Fin (N + 1)) :
    constructor R i ≫ conclusion R = R.ruleConclusion (derivationAlgebra R).a i := by
  change (Sigma.ι (R.ruleObject (derivationAlgebra R).a) i ≫
      (derivationAlgebra R).str.left) ≫ (derivationAlgebra R).a.hom = _
  rw [Category.assoc,Over.w (derivationAlgebra R).str]
  exact Sigma.ι_comp_desc _ i

def nullary : R.instances 0 ⟶ (derivationAlgebra R).a.left :=
  R.nullaryRule (derivationAlgebra R).a ≫ constructor R 0

@[simp,reassoc] theorem nullary_conclusion : nullary R ≫ conclusion R = R.conclusion 0 := by
  rw [nullary,Category.assoc,constructor_conclusion]
  have h := congrArg (fun k => k ≫ R.conclusion 0) (R.nullaryRule_fst (derivationAlgebra R).a)
  simpa only [Category.assoc,Category.id_comp,RulePresentation.ruleConclusion] using h

end CategoricalEssentialIncompleteness.V46.Miller.Derivation
