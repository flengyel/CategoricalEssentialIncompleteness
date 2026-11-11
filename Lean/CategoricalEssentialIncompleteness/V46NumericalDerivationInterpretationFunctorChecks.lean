/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NumericalDerivationInterpretationFunctor


/-! # Statement checks in `V46NumericalDerivationInterpretationFunctorChecks` -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.V46
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
namespace CategoricalEssentialIncompleteness.V46.NumericalDerivationInterpretation
example : PreservesFiniteCoproducts K := inferInstance
variable {F : PredicateCategory 𝗣𝗔} {N : ℕ} (R : RulePresentation F N)
example (Q : Over F) : K.obj (∐ R.ruleObject Q) ≅
    ∐ (interpretedRules R).ruleObject ((overFunctor R).obj Q) := sumIso R Q
example (Q : Over F) (i : Fin (N+1)) :
    K.map (Sigma.ι (R.ruleObject Q) i) ≫ (sumIso R Q).hom =
      (inputIso R Q i).hom ≫ Sigma.ι ((interpretedRules R).ruleObject ((overFunctor R).obj Q)) i :=
  sumIso_iota R Q i
example (Q : Over F) :
    (overFunctor R).obj (R.inference.obj Q) ≅
      (interpretedRules R).inference.obj ((overFunctor R).obj Q) := overIso R Q
example {Q Q' : Over F} (f : Q ⟶ Q') :
    (overFunctor R).map (R.inference.map f) ≫ (overIso R Q').hom =
      (overIso R Q).hom ≫ (interpretedRules R).inference.map ((overFunctor R).map f) := overIso_natural R f
example : R.inference ⋙ overFunctor R ≅ overFunctor R ⋙ (interpretedRules R).inference := comparison R
example (A : Endofunctor.Algebra R.inference) :
    (mappedAlgebra R A).a.hom = K.map A.a.hom := mappedAlgebra_conclusion R A
example (X : PredicateCategory 𝗣𝗔) (i : Fin (N+1)) :
    (ordinaryInputIso R X i).hom ≫ prod.fst = K.map prod.fst := ordinaryInputIso_fst R X i
example (X : PredicateCategory 𝗣𝗔) (i : Fin (N+1)) :
    (ordinaryInputIso R X i).hom ≫ prod.snd = K.map prod.snd ≫ (finitePowerIso X i.val).hom :=
  ordinaryInputIso_snd R X i
example {X Y : PredicateCategory 𝗣𝗔} (f : X ⟶ Y) :
    K.map ((SyntacticDerivation.PolynomialComparison.ordinary R).map f) ≫
      (ordinaryObjectIso R Y).hom =
      (ordinaryObjectIso R X).hom ≫
        (SyntacticDerivation.PolynomialComparison.ordinary (interpretedRules R)).map (K.map f) :=
  ordinaryObjectIso_natural R f
example : SyntacticDerivation.PolynomialComparison.ordinary R ⋙ K ≅
    K ⋙ SyntacticDerivation.PolynomialComparison.ordinary (interpretedRules R) := ordinaryComparison R
example {A B : Endofunctor.Algebra (SyntacticDerivation.PolynomialComparison.ordinary R)}
    (f : A ⟶ B) : (mappedOrdinaryHom R f).f = K.map f.f := rfl
example (Q : Over F) :
    K.map (SyntacticDerivation.InputGeometry.forget R Q) ≫ (ordinaryObjectIso R Q.left).hom =
      (sumIso R Q).hom ≫ SyntacticDerivation.InputGeometry.forget (interpretedRules R)
        ((overFunctor R).obj Q) := forget_comparison R Q
end CategoricalEssentialIncompleteness.V46.NumericalDerivationInterpretation
