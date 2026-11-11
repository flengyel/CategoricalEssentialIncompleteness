/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46CategoricalSubstitutionValues

/-! # Statement checks for CategoricalSubstitutionValues -/

@[expose] public section

noncomputable section

universe v u
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness CategoricalEssentialIncompleteness.V46

variable {D : Type u} [Category.{v} D] [Regular D] [FinitaryExtensive D]
variable {V : D} {σ π : ℕ → D} {d : ℕ} (S : CategoricalSyntax V σ π d)
open CategoricalSyntax

example {W : D} (p : W ⟶ S.substitutionParameters)
    (a : W ⟶ S.algebra.a.1) :
    prod.lift p a ≫ S.substitutionFold.1.left ≫ prod.snd ≫ prod.fst = a := CategoricalSyntax.term_fold_original_value S p a

#print axioms CategoricalEssentialIncompleteness.V46.CategoricalSyntax.term_fold_original_value

example {W : D} (p : W ⟶ S.substitutionParameters)
    (a : W ⟶ S.algebra.a.2) :
    prod.lift p a ≫ S.substitutionFold.2.left ≫ prod.snd ≫ prod.fst = a := CategoricalSyntax.formula_fold_original_value S p a

#print axioms CategoricalEssentialIncompleteness.V46.CategoricalSyntax.formula_fold_original_value

example {W : D} (p : W ⟶ S.substitutionParameters)
    (a b : W ⟶ S.algebra.a.1) :
    prod.lift p (prod.lift a b ≫ S.equalityConstructor) ≫
        S.substitutionFold.2.left ≫ prod.snd =
      prod.lift (prod.lift p a ≫ S.substitutionFold.1.left ≫ prod.snd)
        (prod.lift p b ≫ S.substitutionFold.1.left ≫ prod.snd) ≫
          S.equalitySubstitutionPair := CategoricalSyntax.equality_fold_value S p a b

#print axioms CategoricalEssentialIncompleteness.V46.CategoricalSyntax.equality_fold_value

example {W : D} (p : W ⟶ S.substitutionParameters)
    (a b : W ⟶ S.algebra.a.2) :
    prod.lift p (prod.lift a b ≫ S.implicationConstructor) ≫
        S.substitutionFold.2.left ≫ prod.snd =
      prod.lift (prod.lift p a ≫ S.substitutionFold.2.left ≫ prod.snd)
        (prod.lift p b ≫ S.substitutionFold.2.left ≫ prod.snd) ≫
          S.implicationSubstitutionPair := CategoricalSyntax.implication_fold_value S p a b

#print axioms CategoricalEssentialIncompleteness.V46.CategoricalSyntax.implication_fold_value

example {W : D} (p : W ⟶ S.substitutionParameters)
    (y : W ⟶ V) (a : W ⟶ S.algebra.a.2) :
    prod.lift p (prod.lift y a ≫ S.quantifierConstructor) ≫
        S.substitutionFold.2.left ≫ prod.snd =
      prod.lift p (prod.lift y (prod.lift p a ≫ S.substitutionFold.2.left ≫ prod.snd)) ≫
        S.quantifierSubstitutionPair := CategoricalSyntax.quantifier_fold_value S p y a

#print axioms CategoricalEssentialIncompleteness.V46.CategoricalSyntax.quantifier_fold_value

example {W : D} (p : W ⟶ S.substitutionParameters)
    (a : W ⟶ S.algebra.a.2)
    (ha : a ≫ S.formulaOccurrences = terminal.from W ≫ S.lists.algebra.nil) :
    prod.lift p a ≫ S.substitutionFold.2.left ≫ prod.snd = prod.lift a (a ≫ coprod.inr) := CategoricalSyntax.closed_formula_fold_value S p a ha

#print axioms CategoricalEssentialIncompleteness.V46.CategoricalSyntax.closed_formula_fold_value
