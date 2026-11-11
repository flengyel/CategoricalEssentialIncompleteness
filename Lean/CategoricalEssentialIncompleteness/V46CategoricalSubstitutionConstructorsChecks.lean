/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46CategoricalSubstitutionConstructors

/-! # Statement checks for CategoricalSubstitutionConstructors -/

@[expose] public section

noncomputable section

universe v u
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness CategoricalEssentialIncompleteness.V46

variable {D : Type u} [Category.{v} D] [Regular D] [FinitaryExtensive D]
variable {V : D} {σ π : ℕ → D} {d : ℕ} (S : CategoricalSyntax V σ π d)
open CategoricalSyntax

example :
    constantProductComparison S.substitutionParameters S.algebra.a.1 S.algebra.a.1 ≫
        (constantFamilyFunctor S.substitutionParameters).map S.equalityConstructor ≫
        S.substitutionFold.2 =
      prod.map S.substitutionFold.1 S.substitutionFold.1 ≫
        constantProductComparison S.substitutionParameters
          S.substitutionCarriers.1 S.substitutionCarriers.1 ≫
        (constantFamilyFunctor S.substitutionParameters).map S.equalitySubstitutionPair := CategoricalSyntax.equality_fold_in_slice S

#print axioms CategoricalEssentialIncompleteness.V46.CategoricalSyntax.equality_fold_in_slice

example :
    (constantFamilyFunctor S.substitutionParameters).map S.negationConstructor ≫
        S.substitutionFold.2 =
      S.substitutionFold.2 ≫
        (constantFamilyFunctor S.substitutionParameters).map S.negationSubstitutionPair := CategoricalSyntax.negation_fold_in_slice S

#print axioms CategoricalEssentialIncompleteness.V46.CategoricalSyntax.negation_fold_in_slice

example :
    constantProductComparison S.substitutionParameters S.algebra.a.2 S.algebra.a.2 ≫
        (constantFamilyFunctor S.substitutionParameters).map S.implicationConstructor ≫
        S.substitutionFold.2 =
      prod.map S.substitutionFold.2 S.substitutionFold.2 ≫
        constantProductComparison S.substitutionParameters
          S.substitutionCarriers.2 S.substitutionCarriers.2 ≫
        (constantFamilyFunctor S.substitutionParameters).map S.implicationSubstitutionPair := CategoricalSyntax.implication_fold_in_slice S

#print axioms CategoricalEssentialIncompleteness.V46.CategoricalSyntax.implication_fold_in_slice
