/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NumericalDerivationInterpretationCoherence


/-! # Statement checks in `V46NumericalDerivationInterpretationCoherenceChecks` -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
namespace CategoricalEssentialIncompleteness.V46.NumericalDerivationInterpretation.CoherenceChecks
open SyntacticSyntax SyntacticDerivation Coherence Projection

example (X : PredicateCategory 𝗣𝗔) (n : ℕ) :
    K.map (PolynomialComparison.powerIso X n).hom ≫ (powerInputIso X n).hom =
      (finitePowerIso X n).hom ≫ (PolynomialComparison.powerIso (K.obj X) n).hom :=
  power_square X n

example (σ : ℕ → PredicateCategory 𝗣𝗔) (N : ℕ) (X : PredicateCategory 𝗣𝗔)
    (i : Fin (N+1)) :
    K.map (PolynomialComparison.injection σ X N i) ≫ (oneSortInputIso σ N X).hom =
      (summandInputIso σ X i.val).hom ≫
        PolynomialComparison.injection (fun n => K.obj (σ n)) (K.obj X) N i :=
  injection_square σ N X i

example (σ : ℕ → PredicateCategory 𝗣𝗔) (N : ℕ) (X : PredicateCategory 𝗣𝗔) :
    K.map (PolynomialComparison.component σ N X).hom ≫ (finiteSumIso σ N X).hom =
      (oneSortInputIso σ N X).hom ≫
        (PolynomialComparison.component (fun n => K.obj (σ n)) N (K.obj X)).hom :=
  component_square σ N X

example {F : PredicateCategory 𝗣𝗔} {N : ℕ} (R : RulePresentation F N)
    (X : PredicateCategory 𝗣𝗔) :
    K.map ((PolynomialComparison.comparison R).hom.app X) ≫ (ordinaryObjectIso R X).hom =
      (oneSortInputIso (PolynomialComparison.coefficients R) N X).hom ≫
        (targetComparison R).hom.app (K.obj X) := comparison_square R X

example {F : PredicateCategory 𝗣𝗔} {N : ℕ} (R : RulePresentation F N)
    (B : Endofunctor.Algebra (PolynomialComparison.nested (PolynomialComparison.coefficients R) N)) :
    mappedOrdinaryAlgebra R (PolynomialComparison.mappedAlgebra R B) ≅
      targetMappedAlgebra R B := mappedAlgebraIso R B

example {F : PredicateCategory 𝗣𝗔} {N : ℕ} (R : RulePresentation F N)
    (B : Endofunctor.Algebra (PolynomialComparison.nested (PolynomialComparison.coefficients R) N)) :
    (mappedAlgebraIso R B).hom.f = 𝟙 (K.obj B.a) := rfl

example {F : PredicateCategory 𝗣𝗔} {N : ℕ} (R : RulePresentation F N)
    (X : NumericalTuples.Object) (i : Fin (N+1)) :
    PolynomialComparison.injection (fun n => K.obj (PolynomialComparison.coefficients R n)) X N i ≫
        (targetComparison R).hom.app X =
      prod.map (K.map (eqToHom (PolynomialComparison.coefficients_fin R i)))
          (𝟙 (finitePower X i.val)) ≫
        Sigma.ι (fun j : Fin (N+1) => K.obj (R.instances j) ⨯ finitePower X j.val) i :=
  targetComparison_injection R X i

example {C D : PredicateCategory 𝗣𝗔} (h : C = D) (x : NumericalTuples.Point (K.obj C)) :
    ((K.map (eqToHom h)).toFun x).val = x.val := coefficient_eq_value h x

end CategoricalEssentialIncompleteness.V46.NumericalDerivationInterpretation.CoherenceChecks
