/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NullaryInterpretedSubstitution

/-! # Statement checks for NullaryInterpretedSubstitution -/

@[expose] public section

noncomputable section

universe v u
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness CategoricalEssentialIncompleteness.V46

variable {D : Type u} [Category.{v} D] [Regular D] [FinitaryExtensive D]
variable {V X : D}
variable (S : CategoricalSyntax V (fun _ => ⊥_ D) (fun _ => X) 0)
variable {σ π : ℕ → D} {d : ℕ} (Q : CategoricalSyntax V σ π d)
variable (f : X ⟶ Q.sentenceObject)
open NullaryInterpretation

example {W : D} (p : W ⟶ S.substitutionParameters) (y : W ⟶ V) :
    prod.lift p (y ≫ S.variableConstructor) ≫ interpretedTermPair S Q f =
      prod.lift p y ≫ targetVariablePair S Q f := NullaryInterpretation.interpreted_variable S Q f p y

#print axioms CategoricalEssentialIncompleteness.V46.NullaryInterpretation.interpreted_variable

example {W : D} (p : W ⟶ S.substitutionParameters)
    (a b : W ⟶ S.algebra.a.1) :
    prod.lift p (prod.lift a b ≫ S.equalityConstructor) ≫ interpretedFormulaPair S Q f =
      prod.lift (prod.lift p a ≫ interpretedTermPair S Q f)
        (prod.lift p b ≫ interpretedTermPair S Q f) ≫ Q.equalitySubstitutionPair := NullaryInterpretation.interpreted_equality S Q f p a b

#print axioms CategoricalEssentialIncompleteness.V46.NullaryInterpretation.interpreted_equality

example {W : D} (p : W ⟶ S.substitutionParameters)
    (a : W ⟶ S.algebra.a.2) :
    prod.lift p (a ≫ S.negationConstructor) ≫ interpretedFormulaPair S Q f =
      prod.lift p a ≫ interpretedFormulaPair S Q f ≫ Q.negationSubstitutionPair := NullaryInterpretation.interpreted_negation S Q f p a

#print axioms CategoricalEssentialIncompleteness.V46.NullaryInterpretation.interpreted_negation

example {W : D} (p : W ⟶ S.substitutionParameters)
    (a b : W ⟶ S.algebra.a.2) :
    prod.lift p (prod.lift a b ≫ S.implicationConstructor) ≫ interpretedFormulaPair S Q f =
      prod.lift (prod.lift p a ≫ interpretedFormulaPair S Q f)
        (prod.lift p b ≫ interpretedFormulaPair S Q f) ≫ Q.implicationSubstitutionPair := NullaryInterpretation.interpreted_implication S Q f p a b

#print axioms CategoricalEssentialIncompleteness.V46.NullaryInterpretation.interpreted_implication

example {W : D} (p : W ⟶ S.substitutionParameters)
    (y : W ⟶ V) (a : W ⟶ S.algebra.a.2) :
    prod.lift p (prod.lift y a ≫ S.quantifierConstructor) ≫ interpretedFormulaPair S Q f =
      prod.lift p (prod.lift y (prod.lift p a ≫ interpretedFormulaPair S Q f)) ≫
        targetQuantifierPair S Q f := NullaryInterpretation.interpreted_quantifier S Q f p y a

#print axioms CategoricalEssentialIncompleteness.V46.NullaryInterpretation.interpreted_quantifier

example {W : D} (p : W ⟶ S.substitutionParameters) (a : W ⟶ X) :
    prod.lift p (a ≫ atomFormula S) ≫ interpretedFormulaPair S Q f =
      a ≫ targetAtomPair Q f := NullaryInterpretation.interpreted_atom S Q f p a

#print axioms CategoricalEssentialIncompleteness.V46.NullaryInterpretation.interpreted_atom
