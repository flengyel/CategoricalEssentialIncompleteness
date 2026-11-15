/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ParameterizedBooleanLogical

/-! # Independent statements for parameter-dependent Boolean formula values -/

@[expose] public section
noncomputable section
universe v u
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness CategoricalEssentialIncompleteness.V46

section AlgebraMorphisms
variable {D : Type u} [Category.{v} D] [HasFiniteLimits D] [HasFiniteCoproducts D]
variable {E V X : D} {A B : NullarySyntaxAlgebra.AlgebraWithEmpty E V X} (f : A ⟶ B)

example : NullarySyntaxAlgebra.variableConstructor A ≫ f.f.1 =
    NullarySyntaxAlgebra.variableConstructor B := NullarySyntaxAlgebra.hom_variable f
example : NullarySyntaxAlgebra.equalityConstructor A ≫ f.f.2 =
    prod.map f.f.1 f.f.1 ≫ NullarySyntaxAlgebra.equalityConstructor B :=
  NullarySyntaxAlgebra.hom_equality f
example : NullarySyntaxAlgebra.atomConstructor A ≫ f.f.2 =
    NullarySyntaxAlgebra.atomConstructor B := NullarySyntaxAlgebra.hom_atom f
example : NullarySyntaxAlgebra.negationConstructor A ≫ f.f.2 =
    f.f.2 ≫ NullarySyntaxAlgebra.negationConstructor B := NullarySyntaxAlgebra.hom_negation f
example : NullarySyntaxAlgebra.implicationConstructor A ≫ f.f.2 =
    prod.map f.f.2 f.f.2 ≫ NullarySyntaxAlgebra.implicationConstructor B :=
  NullarySyntaxAlgebra.hom_implication f
example : NullarySyntaxAlgebra.quantifierConstructor A ≫ f.f.2 =
    prod.map (𝟙 V) f.f.2 ≫ NullarySyntaxAlgebra.quantifierConstructor B :=
  NullarySyntaxAlgebra.hom_quantifier f
end AlgebraMorphisms

section ParameterFamilies
variable {D : Type u} [Category.{v} D] [Regular D] [FinitaryExtensive D]
variable {V X W : D}
variable (S : CategoricalSyntax V (fun _ => ⊥_ D) (fun _ => X) 0) (P : D)
variable (d : constantFamily P X ⟶ constantFamily P (Two D))
open ParameterizedBooleanValuation

example : P ⨯ S.algebra.a.2 ⟶ Two D := value S P d
example : (constantFamilyFunctor P).map (NullaryInterpretation.atomFormula S) ≫
    valuation S P d = d := atom_value S P d
example : constantProductComparison P S.algebra.a.1 S.algebra.a.1 ≫
    (constantFamilyFunctor P).map S.equalityConstructor ≫ valuation S P d =
      constant P _ true := equality_value S P d
example : (constantFamilyFunctor P).map S.negationConstructor ≫ valuation S P d =
    valuation S P d ≫ (constantFamilyFunctor P).map (Two.unary Bool.not (𝟙 (Two D))) :=
  negation_value S P d
example : constantProductComparison P S.algebra.a.2 S.algebra.a.2 ≫
    (constantFamilyFunctor P).map S.implicationConstructor ≫ valuation S P d =
      prod.map (valuation S P d) (valuation S P d) ≫
        constantProductComparison P (Two D) (Two D) ≫
          (constantFamilyFunctor P).map (Two.binaryArrow NullaryBooleanValuation.implies) :=
  implication_value S P d
example : constantProductComparison P V S.algebra.a.2 ≫
    (constantFamilyFunctor P).map S.quantifierConstructor ≫ valuation S P d =
      prod.snd ≫ valuation S P d := quantifier_value S P d

variable (p : W ⟶ P)
example (a b : W ⟶ S.algebra.a.1) :
    evaluate S P d p (prod.lift a b ≫ S.equalityConstructor) = Two.constant W true :=
  evaluate_equality S P d p a b
example (a : W ⟶ X) : evaluate S P d p (a ≫ NullaryInterpretation.atomFormula S) =
    prod.lift p a ≫ d.left ≫ prod.snd := evaluate_atom S P d p a
example (a : W ⟶ S.algebra.a.2) : evaluate S P d p (a ≫ S.negationConstructor) =
    Two.unary Bool.not (evaluate S P d p a) := evaluate_negation S P d p a
example (a b : W ⟶ S.algebra.a.2) :
    evaluate S P d p (prod.lift a b ≫ S.implicationConstructor) =
      Two.binary NullaryBooleanValuation.implies (evaluate S P d p a) (evaluate S P d p b) :=
  evaluate_implication S P d p a b
example (v : W ⟶ V) (a : W ⟶ S.algebra.a.2) :
    evaluate S P d p (prod.lift v a ≫ S.quantifierConstructor) = evaluate S P d p a :=
  evaluate_quantifier S P d p v a

example (a : W ⟶ S.algebra.a.2 ⨯ S.algebra.a.2) :
    evaluate S P d p (a ≫ S.hilbertOne) = Two.constant W true := hilbert_one_value S P d p a
example (a : W ⟶ (S.algebra.a.2 ⨯ S.algebra.a.2) ⨯ S.algebra.a.2) :
    evaluate S P d p (a ≫ S.hilbertTwo) = Two.constant W true := hilbert_two_value S P d p a
example (a : W ⟶ S.algebra.a.2 ⨯ S.algebra.a.2) :
    evaluate S P d p (a ≫ S.hilbertThree) = Two.constant W true := hilbert_three_value S P d p a
example (a : W ⟶ S.distributionParameters) :
    evaluate S P d p (a ≫ S.hilbertDistribution) = Two.constant W true :=
  hilbert_distribution_value S P d p a
example (a : W ⟶ S.algebra.a.1) :
    evaluate S P d p (a ≫ S.hilbertReflexivity) = Two.constant W true :=
  hilbert_reflexivity_value S P d p a
example (f g : W ⟶ S.algebra.a.2)
    (hf : evaluate S P d p f = Two.constant W true)
    (hi : evaluate S P d p (prod.lift f g ≫ S.implicationConstructor) =
      Two.constant W true) : evaluate S P d p g = Two.constant W true :=
  modus_ponens_truth S P d p f g hf hi
example (v : W ⟶ V) (f : W ⟶ S.algebra.a.2)
    (hf : evaluate S P d p f = Two.constant W true) :
    evaluate S P d p (prod.lift v f ≫ S.quantifierConstructor) = Two.constant W true :=
  generalization_truth S P d p v f hf

end ParameterFamilies

#print axioms NullarySyntaxAlgebra.hom_variable
#print axioms NullarySyntaxAlgebra.hom_equality
#print axioms NullarySyntaxAlgebra.hom_atom
#print axioms NullarySyntaxAlgebra.hom_negation
#print axioms NullarySyntaxAlgebra.hom_implication
#print axioms NullarySyntaxAlgebra.hom_quantifier
#print axioms ParameterizedBooleanValuation.algebra
#print axioms ParameterizedBooleanValuation.valuation
#print axioms ParameterizedBooleanValuation.value
#print axioms ParameterizedBooleanValuation.equality_value
#print axioms ParameterizedBooleanValuation.atom_value
#print axioms ParameterizedBooleanValuation.negation_value
#print axioms ParameterizedBooleanValuation.implication_value
#print axioms ParameterizedBooleanValuation.quantifier_value
#print axioms ParameterizedBooleanValuation.evaluate_equality
#print axioms ParameterizedBooleanValuation.evaluate_atom
#print axioms ParameterizedBooleanValuation.evaluate_negation
#print axioms ParameterizedBooleanValuation.evaluate_implication
#print axioms ParameterizedBooleanValuation.evaluate_quantifier
#print axioms ParameterizedBooleanValuation.evaluate_implication_input
#print axioms ParameterizedBooleanValuation.evaluate_quantifier_input
#print axioms ParameterizedBooleanValuation.hilbert_one_value
#print axioms ParameterizedBooleanValuation.hilbert_two_value
#print axioms ParameterizedBooleanValuation.hilbert_three_value
#print axioms ParameterizedBooleanValuation.hilbert_distribution_value
#print axioms ParameterizedBooleanValuation.hilbert_reflexivity_value

#print axioms ParameterizedBooleanValuation.modus_ponens_truth
#print axioms ParameterizedBooleanValuation.generalization_truth
