/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SignedFiniteFormulaValuation
public import CategoricalEssentialIncompleteness.V46SyntacticSyntaxPlain
public import CategoricalEssentialIncompleteness.V46PrintedObjectCoding

/-! # Independent checks of finite-support formula and signed-atom values -/

@[expose] public section
noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness CategoricalEssentialIncompleteness.V46
open SyntacticPredicates SyntacticLists SignedFiniteFormulaValuation

section UniformValuation
variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
variable {V X : PredicateCategory T}
variable (S : CategoricalSyntax V (fun _ => ⊥_ (PredicateCategory T)) (fun _ => X) 0)

example : Limits.prod (C := PredicateCategory T) (listObject T X) S.algebra.a.2 ⟶
    Two (PredicateCategory T) := valuation T S

example : ((constantFamilyFunctor (listObject T X)).map
    (NullaryInterpretation.atomFormula S)).left ≫ valuation T S =
      (prod.braiding (C := PredicateCategory T) (listObject T X) X).hom ≫
        ConcreteNamedComparison.membershipArrow T X := atom_value T S

example : ((constantFamilyFunctor (listObject T X)).map
    (NullaryInterpretation.atomFormula S ≫ S.negationConstructor)).left ≫ valuation T S =
      Two.unary Bool.not
        ((prod.braiding (C := PredicateCategory T) (listObject T X) X).hom ≫
          ConcreteNamedComparison.membershipArrow T X) := negative_atom_value T S

variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

example (q : Obj T M (atomInputs T X)) (b : Bool)
    (hb : ConcreteNamedSubstitution.member
      ((F T M).map (prod.snd : atomInputs T X ⟶ X) q).val
      ((F T M).map (prod.fst : atomInputs T X ⟶ listObject T X) q).val =
        if b then 1 else 0) :
    (F T M).map (valuation T S)
        ((F T M).map ((constantFamilyFunctor (listObject T X)).map
          (NullaryInterpretation.atomFormula S)).left q) =
      (F T M).map (Two.constant (atomInputs T X) b) q := atom_point T S q b hb

example (q : Obj T M (atomInputs T X)) (b : Bool)
    (hb : ConcreteNamedSubstitution.member
      ((F T M).map (prod.snd : atomInputs T X ⟶ X) q).val
      ((F T M).map (prod.fst : atomInputs T X ⟶ listObject T X) q).val =
        if b then 1 else 0) :
    (F T M).map (valuation T S)
        ((F T M).map ((constantFamilyFunctor (listObject T X)).map
          (NullaryInterpretation.atomFormula S ≫ S.negationConstructor)).left q) =
      (F T M).map (Two.constant (atomInputs T X) (!b)) q := negative_point T S q b hb

example (q : Obj T M (atomInputs T X))
    (hq : MemVec ((F T M).map (prod.snd : atomInputs T X ⟶ X) q).val
      ((F T M).map (prod.fst : atomInputs T X ⟶ listObject T X) q).val) :
    (F T M).map (valuation T S)
        ((F T M).map ((constantFamilyFunctor (listObject T X)).map
          (NullaryInterpretation.atomFormula S)).left q) =
      (F T M).map (Two.constant (atomInputs T X) true) q := positive_atom T S q hq

example (q : Obj T M (atomInputs T X))
    (hq : ¬ MemVec ((F T M).map (prod.snd : atomInputs T X ⟶ X) q).val
      ((F T M).map (prod.fst : atomInputs T X ⟶ listObject T X) q).val) :
    (F T M).map (valuation T S)
        ((F T M).map ((constantFamilyFunctor (listObject T X)).map
          (NullaryInterpretation.atomFormula S)).left q) =
      (F T M).map (Two.constant (atomInputs T X) false) q := absent_atom T S q hq

example (q : Obj T M (atomInputs T X))
    (hq : ¬ MemVec ((F T M).map (prod.snd : atomInputs T X ⟶ X) q).val
      ((F T M).map (prod.fst : atomInputs T X ⟶ listObject T X) q).val) :
    (F T M).map (valuation T S)
        ((F T M).map ((constantFamilyFunctor (listObject T X)).map
          (NullaryInterpretation.atomFormula S ≫ S.negationConstructor)).left q) =
      (F T M).map (Two.constant (atomInputs T X) true) q := negative_axiom T S q hq

example (q : Obj T M (atomInputs T X))
    (hs : (FiniteSigmaOne.allEntriesCondition ArithmeticDiagonalCodes.alpha).Evalb
      ![((F T M).map (prod.fst : atomInputs T X ⟶ listObject T X) q).val])
    (hn : ArithmeticDiagonalCodes.beta.val.Evalb
      ![((F T M).map (prod.snd : atomInputs T X ⟶ X) q).val]) :
    (F T M).map (valuation T S)
        ((F T M).map ((constantFamilyFunctor (listObject T X)).map
          (NullaryInterpretation.atomFormula S ≫ S.negationConstructor)).left q) =
      (F T M).map (Two.constant (atomInputs T X) true) q := diagonal_negative_axiom T S q hs hn
end UniformValuation

/-- The construction gives the syntax with propositional atoms and no function symbols,
together with its parameterized valuation. -/
example :
    let X : PredicateCategory 𝗣𝗔 := PrintedObjectCoding.Number
    let S := SyntacticSyntax.plainCategoricalSyntax 𝗣𝗔 X
      (fun _ => ⊥_ (PredicateCategory 𝗣𝗔)) (fun _ => X) 0
    Limits.prod (C := PredicateCategory 𝗣𝗔) (listObject 𝗣𝗔 X) S.algebra.a.2 ⟶
      Two (PredicateCategory 𝗣𝗔) := by
  exact valuation 𝗣𝗔 _

#print axioms SignedFiniteFormulaValuation.atomAssignment
#print axioms SignedFiniteFormulaValuation.valuation
#print axioms SignedFiniteFormulaValuation.atom_value
#print axioms SignedFiniteFormulaValuation.negative_atom_value
#print axioms SignedFiniteFormulaValuation.atom_point
#print axioms SignedFiniteFormulaValuation.negative_point
#print axioms SignedFiniteFormulaValuation.positive_atom
#print axioms SignedFiniteFormulaValuation.absent_atom
#print axioms SignedFiniteFormulaValuation.negative_axiom
#print axioms SignedFiniteFormulaValuation.diagonal_negative_axiom
