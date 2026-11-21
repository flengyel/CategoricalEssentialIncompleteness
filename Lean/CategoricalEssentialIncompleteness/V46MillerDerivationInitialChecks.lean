/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerDerivationInitial


/-! # Arbitrary finite-rule initiality for uniform carriers -/

@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46
open CategoricalEssentialIncompleteness.V46.Miller
open SyntacticDerivation
variable {P : Uniform.Family} {F : Total.TotalCategory P} {N : ℕ} (R : RulePresentation F N)
example : IsInitial (Derivation.derivationAlgebra R) := Derivation.derivationInitial R
example (Q : Over F) (i : Fin (N+1)) : R.ruleObject Q i=
    pullback (R.premises i) (finitePowerMap Q.hom i.val) := rfl
example : (Derivation.derivationAlgebra R).a=
    Over.mk (pullback.snd (Derivation.validatorFold R).f (coprod.inr : F ⟶ OptionSyntax.obj F)) := rfl
example : IsPullback (Derivation.treeInclusion R) (Derivation.conclusion R)
    (Derivation.validatorFold R).f (coprod.inr : F ⟶ OptionSyntax.obj F) :=
  Derivation.successful_pullback R
example (B : Endofunctor.Algebra R.inference) :
    (Derivation.derivationFold R B).f.left ≫ B.a.hom=Derivation.conclusion R := Derivation.fold_conclusion R B
example (B : Endofunctor.Algebra R.inference) :
    (Derivation.derivationAlgebra R).str ≫ (Derivation.derivationFold R B).f=
      R.inference.map (Derivation.derivationFold R B).f ≫ B.str := Derivation.fold_constructor R B
example (B : Endofunctor.Algebra R.inference) (f : Derivation.derivationAlgebra R ⟶ B) :
    f=Derivation.derivationFold R B := Derivation.fold_unique R B f
example (B : Endofunctor.Algebra R.inference)
    (f : (Derivation.derivationAlgebra R).a.left ⟶ B.a.left)
    (hf : f ≫ B.a.hom=Derivation.conclusion R)
    (hc : R.inference.map (Over.homMk f hf) ≫ B.str=
      (Derivation.derivationAlgebra R).str ≫ Over.homMk f hf) :
    f=(Derivation.derivationFold R B).f.left := Derivation.fold_underlying_unique R B f hf hc
example (i : Fin (N+1)) : Derivation.constructor R i ≫ Derivation.conclusion R=
    pullback.fst (R.premises i) (finitePowerMap (Derivation.derivationAlgebra R).a.hom i.val) ≫ R.conclusion i :=
  Derivation.constructor_conclusion R i
example : Derivation.nullary R ≫ Derivation.conclusion R=R.conclusion 0 := Derivation.nullary_conclusion R
example : (Derivation.derivationAlgebra R).str.left ≫ Derivation.treeInclusion R=
    InputGeometry.forget R (Derivation.derivationAlgebra R).a ≫
      (PolynomialComparison.ordinary R).map (Derivation.treeInclusion R) ≫ (Derivation.ordinaryTree R).str :=
  Derivation.constructor_tree R
