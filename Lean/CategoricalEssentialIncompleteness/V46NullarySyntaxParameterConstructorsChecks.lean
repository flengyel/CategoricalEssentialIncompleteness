/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NullarySyntaxParameterConstructors

/-! # Statement checks for NullarySyntaxParameterConstructors -/

@[expose] public section

noncomputable section

universe v u
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness CategoricalEssentialIncompleteness.V46

variable {D : Type u} [Category.{v} D] [Regular D] [FinitaryExtensive D]
variable {V X : D}
variable (S : CategoricalSyntax V (fun _ => ⊥_ D) (fun _ => X) 0) (P : D)
open NullaryInterpretation

example : NullarySyntaxAlgebra.variableConstructor (parameterAlgebra S P) =
    (constantFamilyFunctor P).map S.variableConstructor := NullaryInterpretation.parameter_variable S P

#print axioms CategoricalEssentialIncompleteness.V46.NullaryInterpretation.parameter_variable

example : NullarySyntaxAlgebra.equalityConstructor (parameterAlgebra S P) =
    constantProductComparison P S.algebra.a.1 S.algebra.a.1 ≫
      (constantFamilyFunctor P).map S.equalityConstructor := NullaryInterpretation.parameter_equality S P

#print axioms CategoricalEssentialIncompleteness.V46.NullaryInterpretation.parameter_equality

example : NullarySyntaxAlgebra.atomConstructor (parameterAlgebra S P) =
    (constantFamilyFunctor P).map (atomFormula S) := NullaryInterpretation.parameter_atom S P

#print axioms CategoricalEssentialIncompleteness.V46.NullaryInterpretation.parameter_atom

example : NullarySyntaxAlgebra.negationConstructor (parameterAlgebra S P) =
    (constantFamilyFunctor P).map S.negationConstructor := NullaryInterpretation.parameter_negation S P

#print axioms CategoricalEssentialIncompleteness.V46.NullaryInterpretation.parameter_negation

example :
    NullarySyntaxAlgebra.implicationConstructor (parameterAlgebra S P) =
      constantProductComparison P S.algebra.a.2 S.algebra.a.2 ≫
        (constantFamilyFunctor P).map S.implicationConstructor := NullaryInterpretation.parameter_implication S P

#print axioms CategoricalEssentialIncompleteness.V46.NullaryInterpretation.parameter_implication

example :
    NullarySyntaxAlgebra.quantifierConstructor (parameterAlgebra S P) =
      constantProductComparison P V S.algebra.a.2 ≫
        (constantFamilyFunctor P).map S.quantifierConstructor := NullaryInterpretation.parameter_quantifier S P

#print axioms CategoricalEssentialIncompleteness.V46.NullaryInterpretation.parameter_quantifier
