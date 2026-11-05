/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46NamedPostfixPlainComparison
import CategoricalEssentialIncompleteness.V46ConcreteNamedComparisonPolynomial

/-! # Literal word values of the actual plain syntax constructors -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticLists
namespace CategoricalEssentialIncompleteness.V46.NamedPlainConstructorModels
open SyntacticSyntax
variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
variable (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T]

private theorem fromPlain_value (sort : Bool) (a b : RawPolynomial)
    (word : Obj T M (Postfix.plainCarrier sort a b)) :
    ((F T M).map (Postfix.plainCarrierIso T sort a b).inv word).val = word.val := by
  let out := (F T M).map (Postfix.plainCarrierIso T sort a b).inv word
  have hg := (PredicateInterpretation.map_class_eq_iff T M
    (Postfix.fromPlainMorphism T sort a b) word out).mp rfl
  exact ((GraphMorphism.identityGraph_eval _ _ _).mp hg).2

variable [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

/-- The constructor-preserving parser comparison does not change the
word at a plain term constructor, including nonstandard inputs. -/
theorem plainTerm_value (a b : SyntaxPolynomial (PredicateCategory T)) (u : M)
    (z : Obj T M (a.eval.obj (plainPostfixAlgebra T a b).a))
    (h : (baseRepresentation T (Postfix.plainCarrier false a b)
      (Postfix.plainCarrier true a b) a).val.Evalb ![u,z.val]) :
    ((F T M).map (plainPostfixAlgebra T a b).str.1 z).val = Coding.constructor false a u := by
  let f := (Postfix.plainCarrierIso T false a b).inv
  let g := (Postfix.plainCarrierIso T true a b).inv
  let input := (F T M).map (a.eval.map ((f,g) : (plainPostfixAlgebra T a b).a ⟶ (postfixAlgebra T a b).a)) z
  have hr := ConcreteNamedComparison.representation_map T M f g id id
    (fromPlain_value T M false a b) (fromPlain_value T M true a b) a u z h
  have hu := (baseRepresentation_support T M (Postfix.plainCarrier false a b)
    (Postfix.plainCarrier true a b) a u z.val h).1
  rw [ConcreteNamedSubstitution.mapChildren_id a u hu] at hr
  have hv := postfixTerm_value T M a b u input hr
  change ((F T M).map (a.eval.map ((f,g) : (plainPostfixAlgebra T a b).a ⟶
    (postfixAlgebra T a b).a) ≫ (postfixAlgebra T a b).str.1 ≫
      (Postfix.plainCarrierIso T false a b).hom) z).val = _
  rw [Functor.map_comp_apply,Functor.map_comp_apply]
  exact (NamedPostfixPlainComparison.plainCarrierIso_value T M false a b
    ((F T M).map (postfixAlgebra T a b).str.1 input)).trans hv

/-- The same actual comparison preserves every plain formula constructor;
no inverse of an arbitrary polynomial encoder is assumed. -/
theorem plainFormula_value (a b : SyntaxPolynomial (PredicateCategory T)) (u : M)
    (z : Obj T M (b.eval.obj (plainPostfixAlgebra T a b).a))
    (h : (baseRepresentation T (Postfix.plainCarrier false a b)
      (Postfix.plainCarrier true a b) b).val.Evalb ![u,z.val]) :
    ((F T M).map (plainPostfixAlgebra T a b).str.2 z).val = Coding.constructor true b u := by
  let f := (Postfix.plainCarrierIso T false a b).inv
  let g := (Postfix.plainCarrierIso T true a b).inv
  let input := (F T M).map (b.eval.map ((f,g) : (plainPostfixAlgebra T a b).a ⟶ (postfixAlgebra T a b).a)) z
  have hr := ConcreteNamedComparison.representation_map T M f g id id
    (fromPlain_value T M false a b) (fromPlain_value T M true a b) b u z h
  have hu := (baseRepresentation_support T M (Postfix.plainCarrier false a b)
    (Postfix.plainCarrier true a b) b u z.val h).1
  rw [ConcreteNamedSubstitution.mapChildren_id b u hu] at hr
  have hv := postfixFormula_value T M a b u input hr
  change ((F T M).map (b.eval.map ((f,g) : (plainPostfixAlgebra T a b).a ⟶
    (postfixAlgebra T a b).a) ≫ (postfixAlgebra T a b).str.2 ≫
      (Postfix.plainCarrierIso T true a b).hom) z).val = _
  rw [Functor.map_comp_apply,Functor.map_comp_apply]
  exact (NamedPostfixPlainComparison.plainCarrierIso_value T M true a b
    ((F T M).map (postfixAlgebra T a b).str.2 input)).trans hv

end CategoricalEssentialIncompleteness.V46.NamedPlainConstructorModels
