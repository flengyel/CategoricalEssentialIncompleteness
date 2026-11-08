/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46MillerSyntaxTotal
import CategoricalEssentialIncompleteness.V46MillerDerivationValidation
import CategoricalEssentialIncompleteness.V46SyntacticSyntaxOneSort
import CategoricalEssentialIncompleteness.V46SyntacticDerivationAlgebraAdjunction

/-! # Actual arbitrary-rule derivations in Tot(Split(E_z))

Every coefficient object, every formula object and every target algebra
belong to the actual total splitting. The ordinary trees are constructed
through the proved polynomial comparison of the actual equivalence.
The conservative singleton interpretation then proves the successful
input comparison; it is not supplied as a hypothesis.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.RestrictionCategory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness.V46.Miller.Derivation.Canonical
open SyntacticDerivation
variable (z : Point)

abbrev interpretation := (Total.pointPresentation z).inverse ⋙
  Miller.Derivation.interpretation (P := Uniform.Family.ofPoint z)

instance interpretation_reflectsIsomorphisms : (interpretation z).ReflectsIsomorphisms := by
  dsimp only [interpretation]
  infer_instance

instance interpretation_preservesPullbacks :
    PreservesLimitsOfShape WalkingCospan (interpretation z) := by
  dsimp only [interpretation]
  infer_instance

instance interpretation_preservesBinaryCoproducts :
    PreservesColimitsOfShape (Discrete WalkingPair) (interpretation z) := by
  dsimp only [interpretation]
  infer_instance

variable {F : Total.CanonicalTotal z} {N : ℕ} (R : RulePresentation F N)

def ruleEquality (_R : RulePresentation F N) (i : Fin (N+1)) :
    DecidableVariables (finitePower F i.val) :=
  DecidableVariables.Transport.mapped (Total.pointPresentation z)
    (Miller.Derivation.equality ((Total.pointPresentation z).inverse.obj (finitePower F i.val)))
    (finitePower F i.val) ((Total.pointPresentation z).counitIso.app (finitePower F i.val))

abbrev validator : Endofunctor.Algebra (PolynomialComparison.ordinary R) :=
  SuccessComparisonCore.validator R (ruleEquality z R)

def treePair : Endofunctor.Algebra (SyntaxPolynomial.jointFunctor
    (SyntaxPolynomial.constructors (PolynomialComparison.coefficients R) N) .unit) :=
  (Syntax.mappedWordData (Total.pointPresentation z)
    (SyntaxPolynomial.constructors (PolynomialComparison.coefficients R) N) .unit).1

def oneSortTree : Endofunctor.Algebra
    (SyntacticSyntax.constructorFunctor (PolynomialComparison.coefficients R) N) :=
  SyntacticSyntax.projectedConstructorAlgebra (PolynomialComparison.coefficients R) N (treePair z R)

def ordinaryTree : Endofunctor.Algebra (PolynomialComparison.ordinary R) :=
  PolynomialComparison.mappedAlgebra R (oneSortTree z R)

def ordinaryTreeInitial : IsInitial (ordinaryTree z R) :=
  PolynomialComparison.mappedInitial R (oneSortTree z R)
    (SyntacticSyntax.projectedConstructorInitial (PolynomialComparison.coefficients R) N
      (treePair z R) (Syntax.mappedWordData (Total.pointPresentation z)
        (SyntaxPolynomial.constructors (PolynomialComparison.coefficients R) N) .unit).2.1)

def validatorFold : ordinaryTree z R ⟶ validator z R := (ordinaryTreeInitial z R).to _

def validatedSlice : Endofunctor.Algebra
    (SliceInitial.functor (PolynomialComparison.ordinary R) (validator z R)) :=
  SliceInitial.algebra _ _ (ordinaryTree z R) (ordinaryTreeInitial z R)

/-- The comparison uses the proved conservative, pullback- and
coproduct-preserving model family, not a supplied validation equation. -/
def successComparison :
    SliceInitial.functor (PolynomialComparison.ordinary R) (validator z R) ⋙
        Over.pullback (coprod.inr : F ⟶ OptionSyntax.obj F) ≅
      Over.pullback (coprod.inr : F ⟶ OptionSyntax.obj F) ⋙ R.inference :=
  SuccessComparisonCore.comparison (interpretation z) R (ruleEquality z R)

/-- The source carrier is exactly the successful pullback of the
constructed ordinary-tree validator. -/
def derivationAlgebra : Endofunctor.Algebra R.inference :=
  AlgebraAdjunction.leftAlgebra (successComparison z R) (validatedSlice z R)

def derivationInitial : IsInitial (derivationAlgebra z R) :=
  AlgebraAdjunction.initial (SuccessAdjunction.adjunction F)
    (successComparison z R) (validatedSlice z R)
    (SliceInitial.initial _ _ (ordinaryTree z R) (ordinaryTreeInitial z R))

def conclusion : (derivationAlgebra z R).a.left ⟶ F := (derivationAlgebra z R).a.hom

def treeInclusion : (derivationAlgebra z R).a.left ⟶ (ordinaryTree z R).a :=
  pullback.fst (validatorFold z R).f (coprod.inr : F ⟶ OptionSyntax.obj F)

@[simp] theorem derivation_carrier : (derivationAlgebra z R).a =
    Over.mk (pullback.snd (validatorFold z R).f (coprod.inr : F ⟶ OptionSyntax.obj F)) := rfl

theorem successful_pullback :
    IsPullback (treeInclusion z R) (conclusion z R) (validatorFold z R).f
      (coprod.inr : F ⟶ OptionSyntax.obj F) :=
  IsPullback.of_hasPullback _ _

/-- Successful constructors retain the original rule label and ordered
children. The validation result is not an additional tree label. -/
theorem constructor_tree :
    (derivationAlgebra z R).str.left ≫ treeInclusion z R =
      InputGeometry.forget R (derivationAlgebra z R).a ≫
        (PolynomialComparison.ordinary R).map (treeInclusion z R) ≫ (ordinaryTree z R).str := by
  let v := (validatorFold z R).f
  let j := pullback.fst v (coprod.inr : F ⟶ OptionSyntax.obj F)
  have hp : ((SuccessComparisonCore.success (F := F)).map (validatedSlice z R).str).left ≫ j =
      pullback.fst ((SliceInitial.functor (PolynomialComparison.ordinary R) (validator z R)).obj
        (Over.mk v)).hom (coprod.inr : F ⟶ OptionSyntax.obj F) ≫ (ordinaryTree z R).str := by
    simp [j,v,Over.pullback,validatedSlice,SliceInitial.algebra,validatorFold]
  change (((SuccessComparisonCore.comparison (interpretation z) R (ruleEquality z R)).inv.app
      (Over.mk v)).left ≫ ((SuccessComparisonCore.success (F := F)).map (validatedSlice z R).str).left) ≫ j = _
  rw [SuccessComparisonCore.comparison_inv_app,Category.assoc,hp,
    ← Category.assoc,SuccessComparisonCore.componentIso_input]
  simpa only [Category.assoc, treeInclusion, derivationAlgebra, AlgebraAdjunction.leftAlgebra,
    validatedSlice, SliceInitial.algebra, validatorFold, v, Functor.comp_obj,
    SuccessComparisonCore.success, Over.mk_hom] using
    congrArg (fun k => k ≫ (ordinaryTree z R).str)
      (SuccessComparisonCore.input_eq_forget R (Over.mk v))

def derivationFold (B : Endofunctor.Algebra R.inference) : derivationAlgebra z R ⟶ B :=
  (derivationInitial z R).to B

theorem fold_conclusion (B : Endofunctor.Algebra R.inference) :
    (derivationFold z R B).f.left ≫ B.a.hom = conclusion z R := Over.w (derivationFold z R B).f

theorem fold_constructor (B : Endofunctor.Algebra R.inference) :
    (derivationAlgebra z R).str ≫ (derivationFold z R B).f = R.inference.map (derivationFold z R B).f ≫ B.str :=
  (derivationFold z R B).h.symm

theorem fold_unique (B : Endofunctor.Algebra R.inference) (f : derivationAlgebra z R ⟶ B) :
    f = derivationFold z R B := (derivationInitial z R).hom_ext f _

/-- Uniqueness applies to every carrier morphism satisfying the original
slice and constructor equations. -/
theorem fold_underlying_unique (B : Endofunctor.Algebra R.inference)
    (f : (derivationAlgebra z R).a.left ⟶ B.a.left) (hf : f ≫ B.a.hom = conclusion z R)
    (hc : R.inference.map (Over.homMk f hf) ≫ B.str =
      (derivationAlgebra z R).str ≫ Over.homMk f hf) : f = (derivationFold z R B).f.left := by
  exact congrArg (fun h : derivationAlgebra z R ⟶ B => h.f.left)
    ((derivationInitial z R).hom_ext (⟨Over.homMk f hf,hc⟩ : derivationAlgebra z R ⟶ B) (derivationFold z R B))

def constructor (i : Fin (N + 1)) : R.ruleObject (derivationAlgebra z R).a i ⟶
    (derivationAlgebra z R).a.left :=
  Sigma.ι (R.ruleObject (derivationAlgebra z R).a) i ≫ (derivationAlgebra z R).str.left

@[simp,reassoc] theorem constructor_conclusion (i : Fin (N + 1)) :
    constructor z R i ≫ conclusion z R = R.ruleConclusion (derivationAlgebra z R).a i := by
  change (Sigma.ι (R.ruleObject (derivationAlgebra z R).a) i ≫
      (derivationAlgebra z R).str.left) ≫ (derivationAlgebra z R).a.hom = _
  rw [Category.assoc,Over.w (derivationAlgebra z R).str]
  exact Sigma.ι_comp_desc _ i

def nullary : R.instances 0 ⟶ (derivationAlgebra z R).a.left :=
  R.nullaryRule (derivationAlgebra z R).a ≫ constructor z R 0

@[simp,reassoc] theorem nullary_conclusion : nullary z R ≫ conclusion z R = R.conclusion 0 := by
  rw [nullary,Category.assoc,constructor_conclusion]
  have h := congrArg (fun k => k ≫ R.conclusion 0) (R.nullaryRule_fst (derivationAlgebra z R).a)
  simpa only [Category.assoc,Category.id_comp,RulePresentation.ruleConclusion] using h

end CategoricalEssentialIncompleteness.V46.Miller.Derivation.Canonical
