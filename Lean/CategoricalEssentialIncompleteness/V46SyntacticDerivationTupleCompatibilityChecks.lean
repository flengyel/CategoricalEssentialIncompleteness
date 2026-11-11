/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SyntacticDerivationTupleCompatibility

/-! Exact compatibility of original inference powers with literal premise tuples. -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticDerivation
variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] {F G : PredicateCategory T}
variable (f : GraphMorphism T F G) (n : ℕ)
example : premisePowerFunctor T n = Functor.diag (PredicateCategory T) ⋙
    (SyntaxPolynomial.power .term n).eval := premisePowerFunctor_eq T n
example : finitePowerMap (representedArrow T f) n ≫
      representedArrow T (finitePowerEncoder T G n) =
    representedArrow T (finitePowerEncoder T F n) ≫
      representedArrow T (tupleMorphism f n) := tupleMorphism_compatibility T f n
