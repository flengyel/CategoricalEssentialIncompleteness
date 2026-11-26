/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NullarySubstitutionHom
public import CategoricalEssentialIncompleteness.V46CategoricalSubstitutionValues
public import CategoricalEssentialIncompleteness.V46NullarySyntaxParameterConstructors

/-! # Substitution after interpreting propositional atoms by sentences -/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u
open CategoryTheory CategoryTheory.Limits

namespace CategoricalEssentialIncompleteness.V46.NullaryInterpretation

variable {D : Type u} [Category.{v} D] [Regular D] [FinitaryExtensive D]
variable {V X : D}
variable (S : CategoricalSyntax V (fun _ => ⊥_ D) (fun _ => X) 0)
variable {σ π : ℕ → D} {d : ℕ} (Q : CategoricalSyntax V σ π d)
variable (f : X ⟶ Q.sentenceObject)

def interpretedTermPair : S.substitutionParameters ⨯ S.algebra.a.1 ⟶ Q.substitutionCarriers.1 :=
  prod.lift (prod.fst ≫ substitutionParameterMap S Q f) (prod.snd ≫ (interpretation S Q f).1) ≫
    Q.substitutionFold.1.left ≫ prod.snd

def interpretedFormulaPair : S.substitutionParameters ⨯ S.algebra.a.2 ⟶
    Q.substitutionCarriers.2 :=
  prod.lift (prod.fst ≫ substitutionParameterMap S Q f) (prod.snd ≫ (interpretation S Q f).2) ≫
    Q.substitutionFold.2.left ≫ prod.snd

@[simp, reassoc] theorem interpretedTermPair_value {W : D}
    (p : W ⟶ S.substitutionParameters) (a : W ⟶ S.algebra.a.1) :
    prod.lift p a ≫ interpretedTermPair S Q f =
      prod.lift (p ≫ substitutionParameterMap S Q f) (a ≫ (interpretation S Q f).1) ≫
        Q.substitutionFold.1.left ≫ prod.snd := by
  simp [interpretedTermPair]

@[simp, reassoc] theorem interpretedFormulaPair_value {W : D}
    (p : W ⟶ S.substitutionParameters) (a : W ⟶ S.algebra.a.2) :
    prod.lift p a ≫ interpretedFormulaPair S Q f =
      prod.lift (p ≫ substitutionParameterMap S Q f) (a ≫ (interpretation S Q f).2) ≫
        Q.substitutionFold.2.left ≫ prod.snd := by
  simp [interpretedFormulaPair]

@[reassoc] theorem interpretedTermPair_family {W : Over S.substitutionParameters}
    (g : W ⟶ constantFamily S.substitutionParameters S.algebra.a.1) :
    g.left ≫ interpretedTermPair S Q f =
      prod.lift (W.hom ≫ substitutionParameterMap S Q f)
        (g.left ≫ prod.snd ≫ (interpretation S Q f).1) ≫
          Q.substitutionFold.1.left ≫ prod.snd := by
  have hp := congrArg (fun k => k ≫ substitutionParameterMap S Q f) (Over.w g)
  change (g.left ≫ prod.fst) ≫ substitutionParameterMap S Q f =
    W.hom ≫ substitutionParameterMap S Q f at hp
  simpa only [interpretedTermPair, prod.comp_lift_assoc, Category.assoc] using
    congrArg (fun k => prod.lift k (g.left ≫ prod.snd ≫ (interpretation S Q f).1) ≫
      Q.substitutionFold.1.left ≫ prod.snd) hp

@[reassoc] theorem interpretedFormulaPair_family {W : Over S.substitutionParameters}
    (g : W ⟶ constantFamily S.substitutionParameters S.algebra.a.2) :
    g.left ≫ interpretedFormulaPair S Q f =
      prod.lift (W.hom ≫ substitutionParameterMap S Q f)
        (g.left ≫ prod.snd ≫ (interpretation S Q f).2) ≫
          Q.substitutionFold.2.left ≫ prod.snd := by
  have hp := congrArg (fun k => k ≫ substitutionParameterMap S Q f) (Over.w g)
  change (g.left ≫ prod.fst) ≫ substitutionParameterMap S Q f =
    W.hom ≫ substitutionParameterMap S Q f at hp
  simpa only [interpretedFormulaPair, prod.comp_lift_assoc, Category.assoc] using
    congrArg (fun k => prod.lift k (g.left ≫ prod.snd ≫ (interpretation S Q f).2) ≫
      Q.substitutionFold.2.left ≫ prod.snd) hp

theorem interpreted_variable {W : D} (p : W ⟶ S.substitutionParameters) (y : W ⟶ V) :
    prod.lift p (y ≫ S.variableConstructor) ≫ interpretedTermPair S Q f =
      prod.lift p y ≫ targetVariablePair S Q f := by
  rw [interpretedTermPair_value, Category.assoc, variable_law S Q f]
  have h := congrArg (fun k => prod.lift (p ≫ substitutionParameterMap S Q f) y ≫ k)
    Q.variable_fold_value
  simpa [targetVariablePair, Category.assoc, prod.lift_map_assoc] using h

theorem interpreted_equality {W : D} (p : W ⟶ S.substitutionParameters)
    (a b : W ⟶ S.algebra.a.1) :
    prod.lift p (prod.lift a b ≫ S.equalityConstructor) ≫ interpretedFormulaPair S Q f =
      prod.lift (prod.lift p a ≫ interpretedTermPair S Q f)
        (prod.lift p b ≫ interpretedTermPair S Q f) ≫ Q.equalitySubstitutionPair := by
  simpa [Category.assoc, equality S Q f, prod.lift_map_assoc] using
    Q.equality_fold_value (p ≫ substitutionParameterMap S Q f)
      (a ≫ (interpretation S Q f).1) (b ≫ (interpretation S Q f).1)

theorem interpreted_negation {W : D} (p : W ⟶ S.substitutionParameters)
    (a : W ⟶ S.algebra.a.2) :
    prod.lift p (a ≫ S.negationConstructor) ≫ interpretedFormulaPair S Q f =
      prod.lift p a ≫ interpretedFormulaPair S Q f ≫ Q.negationSubstitutionPair := by
  simpa [Category.assoc, negation S Q f, interpretedFormulaPair_value_assoc] using
    Q.negation_fold_value (p ≫ substitutionParameterMap S Q f) (a ≫ (interpretation S Q f).2)

theorem interpreted_implication {W : D} (p : W ⟶ S.substitutionParameters)
    (a b : W ⟶ S.algebra.a.2) :
    prod.lift p (prod.lift a b ≫ S.implicationConstructor) ≫ interpretedFormulaPair S Q f =
      prod.lift (prod.lift p a ≫ interpretedFormulaPair S Q f)
        (prod.lift p b ≫ interpretedFormulaPair S Q f) ≫ Q.implicationSubstitutionPair := by
  simpa [Category.assoc, implication S Q f, prod.lift_map_assoc] using
    Q.implication_fold_value (p ≫ substitutionParameterMap S Q f)
      (a ≫ (interpretation S Q f).2) (b ≫ (interpretation S Q f).2)

theorem interpreted_quantifier {W : D} (p : W ⟶ S.substitutionParameters)
    (y : W ⟶ V) (a : W ⟶ S.algebra.a.2) :
    prod.lift p (prod.lift y a ≫ S.quantifierConstructor) ≫ interpretedFormulaPair S Q f =
      prod.lift p (prod.lift y (prod.lift p a ≫ interpretedFormulaPair S Q f)) ≫
        targetQuantifierPair S Q f := by
  simpa [Category.assoc, quantifier S Q f, targetQuantifierPair, prod.lift_map_assoc] using
    Q.quantifier_fold_value (p ≫ substitutionParameterMap S Q f) y (a ≫ (interpretation S Q f).2)

theorem interpreted_atom {W : D} (p : W ⟶ S.substitutionParameters) (a : W ⟶ X) :
    prod.lift p (a ≫ atomFormula S) ≫ interpretedFormulaPair S Q f =
      a ≫ targetAtomPair Q f := by
  have ha : a ≫ f ≫ Q.sentenceInclusion ≫ Q.formulaOccurrences =
      terminal.from W ≫ Q.lists.algebra.nil := by
    rw [sentence_occurrences Q]
    simp
  simpa [Category.assoc, atom S Q f, targetAtomPair, prod.comp_lift_assoc] using
    Q.closed_formula_fold_value (p ≫ substitutionParameterMap S Q f)
      (a ≫ f ≫ Q.sentenceInclusion) (by simpa only [Category.assoc] using ha)

end CategoricalEssentialIncompleteness.V46.NullaryInterpretation
