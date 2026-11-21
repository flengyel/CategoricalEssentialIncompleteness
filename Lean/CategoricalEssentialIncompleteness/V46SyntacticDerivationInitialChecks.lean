/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SyntacticDerivationInitial

/-! Lemma 6.8 for arbitrary rule objects, ordered premise maps and conclusions. -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticDerivation
variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] {F : PredicateCategory T} {N : ℕ}
  (R : RulePresentation F N)
example : Endofunctor.Algebra R.inference := derivationAlgebra T R
example : IsInitial (derivationAlgebra T R) := derivationInitial T R
example : GraphMorphism T (derivationCarrier T R) F := derivationConclusion T R
example : (derivationAlgebra T R).a = Over.mk (representedArrow T (derivationConclusion T R)) :=
  derivationAlgebra_carrier T R
example (i : Fin (N + 1)) : R.ruleObject (derivationAlgebra T R).a i =
    pullback (R.premises i) (finitePowerMap (derivationAlgebra T R).a.hom i.val) := rfl
example : R.instances 0 ⟶ (derivationAlgebra T R).a.left := nullaryDerivation T R
example : nullaryDerivation T R ≫ (derivationAlgebra T R).a.hom = R.conclusion 0 :=
  nullaryDerivation_conclusion T R
example (B : Endofunctor.Algebra R.inference) (f : derivationAlgebra T R ⟶ B) :
    f = derivationFold T R B := derivationFold_unique T R B f
example (B : Endofunctor.Algebra R.inference) :
    (derivationFold T R B).f.left ≫ B.a.hom = representedArrow T (derivationConclusion T R) :=
  derivationFold_conclusion T R B
example (B : Endofunctor.Algebra R.inference) :
    (derivationAlgebra T R).str ≫ (derivationFold T R B).f =
      R.inference.map (derivationFold T R B).f ≫ B.str := derivationFold_constructor T R B
