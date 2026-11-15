/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ParameterizedBooleanLogicalSoundness
public import CategoricalEssentialIncompleteness.V46SignedFiniteFormulaValuation

/-! # Independent full statements of parameterized Boolean substitution soundness -/

@[expose] public section
noncomputable section
universe v u
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness CategoricalEssentialIncompleteness.V46

section General
variable {D : Type u} [Category.{v} D] [Regular D] [FinitaryExtensive D]
variable {V X W : D}
variable (S : CategoricalSyntax V (fun _ => ⊥_ D) (fun _ => X) 0) (P : D)
variable (d : constantFamily P X ⟶ constantFamily P (Two D))
variable (p : W ⟶ P)
open ParameterizedBooleanValuation

example (q : W ⟶ S.substitutionParameters) (f : W ⟶ S.algebra.a.2) :
    ParameterizedOption.map (value S P d) p (prod.lift f q ≫ S.formulaSubstitutionOption) =
      OptionSyntax.mask (prod.lift p f ≫ value S P d)
        (prod.lift f q ≫ S.formulaSubstitutionOption) := substitution_option_value S P d p q f

example (i : W ⟶ S.admissibleSubstitution) :
    prod.lift p (i ≫ S.formulaSubstitution) ≫ value S P d =
      prod.lift p (i ≫ S.admissibleInclusion ≫ prod.fst) ≫ value S P d :=
  substitution_value S P d p i

example (a : W ⟶ S.instantiationParameters) :
    prod.lift p (a ≫ S.hilbertInstantiation) ≫ value S P d = Two.constant W true :=
  hilbert_instantiation_value S P d p a

example (a : W ⟶ S.equalitySchemeParameters) :
    prod.lift p (a ≫ S.hilbertEquality) ≫ value S P d = Two.constant W true :=
  hilbert_equality_value S P d p a

example (a : W ⟶ S.logicalParameters) :
    prod.lift p (a ≫ S.logicalAxioms) ≫ value S P d = Two.constant W true :=
  logical_axioms_value S P d p a

example {R : D} (s : R ⟶ P) (r : R ⟶ S.substitutionParameters) :
    ParameterizedSubstitution.fold S r ≫ invariantResult S P d s r =
      ParameterizedSubstitution.fold S r ≫ invariantMask S P d s r :=
  fold_invariant S P d s r

example (q : W ⟶ S.substitutionParameters) (v : W ⟶ V)
    (a : W ⟶ S.substitutionCarriers.2) (ha : PairGood S P d p a) :
    PairGood S P d p (prod.lift q (prod.lift v a) ≫ S.quantifierSubstitutionPair) :=
  quantifier_pair_good S P d p q v a ha
end General

section FiniteSupport
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open SyntacticPredicates SyntacticLists
variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
variable {V X W : PredicateCategory T}
variable (S : CategoricalSyntax V (fun _ => ⊥_ (PredicateCategory T)) (fun _ => X) 0)
variable (p : W ⟶ listObject T X)

/-- The actual constructed finite-support assignment needs no additional
valuation or substitution-invariance hypothesis. -/
example (i : W ⟶ S.admissibleSubstitution) :
    ParameterizedBooleanValuation.evaluate S (listObject T X)
        (SignedFiniteFormulaValuation.atomAssignment T X) p (i ≫ S.formulaSubstitution) =
      ParameterizedBooleanValuation.evaluate S (listObject T X)
        (SignedFiniteFormulaValuation.atomAssignment T X) p
          (i ≫ S.admissibleInclusion ≫ prod.fst) :=
  ParameterizedBooleanValuation.substitution_value S (listObject T X)
    (SignedFiniteFormulaValuation.atomAssignment T X) p i

example (a : W ⟶ S.logicalParameters) :
    ParameterizedBooleanValuation.evaluate S (listObject T X)
      (SignedFiniteFormulaValuation.atomAssignment T X) p (a ≫ S.logicalAxioms) =
        Two.constant W true :=
  ParameterizedBooleanValuation.logical_axioms_value S (listObject T X)
    (SignedFiniteFormulaValuation.atomAssignment T X) p a
end FiniteSupport

#print axioms ParameterizedBooleanValuation.evaluate_precomp
#print axioms ParameterizedBooleanValuation.option_negation_value
#print axioms ParameterizedBooleanValuation.option_implication_value
#print axioms ParameterizedBooleanValuation.option_quantifier_value
#print axioms ParameterizedBooleanValuation.PairGood
#print axioms ParameterizedBooleanValuation.pairGood_precomp
#print axioms ParameterizedBooleanValuation.equality_pair_good
#print axioms ParameterizedBooleanValuation.relation_pair_good
#print axioms ParameterizedBooleanValuation.negation_pair_good
#print axioms ParameterizedBooleanValuation.implication_pair_good
#print axioms ParameterizedBooleanValuation.quantifier_pair_good
#print axioms ParameterizedBooleanValuation.invariant_equation
#print axioms ParameterizedBooleanValuation.invariant_precomp
#print axioms ParameterizedBooleanValuation.equality_closed
#print axioms ParameterizedBooleanValuation.relation_closed
#print axioms ParameterizedBooleanValuation.negation_closed
#print axioms ParameterizedBooleanValuation.implication_closed
#print axioms ParameterizedBooleanValuation.quantifier_closed
#print axioms ParameterizedBooleanValuation.constructor_closed
#print axioms ParameterizedBooleanValuation.fold_invariant
#print axioms ParameterizedBooleanValuation.substitution_pair_good
#print axioms ParameterizedBooleanValuation.substitution_option_value
#print axioms ParameterizedBooleanValuation.substitution_value
#print axioms ParameterizedBooleanValuation.evaluate_equality_input
#print axioms ParameterizedBooleanValuation.substitution_input_value
#print axioms ParameterizedBooleanValuation.hilbert_instantiation_value
#print axioms ParameterizedBooleanValuation.hilbert_equality_value
#print axioms ParameterizedBooleanValuation.logical_axioms_value
