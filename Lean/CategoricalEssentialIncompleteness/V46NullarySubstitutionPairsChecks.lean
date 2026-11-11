/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NullarySubstitutionPairs

/-! # Statement checks for NullarySubstitutionPairs -/

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

example :
    S.variableSubstitutionPair ≫ (substitutionCarrierMap S Q f).1 = targetVariablePair S Q f := NullaryInterpretation.variable_pair_comparison S Q f

#print axioms CategoricalEssentialIncompleteness.V46.NullaryInterpretation.variable_pair_comparison

example :
    S.equalitySubstitutionPair ≫ (substitutionCarrierMap S Q f).2 =
      prod.map (substitutionCarrierMap S Q f).1 (substitutionCarrierMap S Q f).1 ≫
        Q.equalitySubstitutionPair := NullaryInterpretation.equality_pair_comparison S Q f

#print axioms CategoricalEssentialIncompleteness.V46.NullaryInterpretation.equality_pair_comparison

example :
    S.negationSubstitutionPair ≫ (substitutionCarrierMap S Q f).2 =
      (substitutionCarrierMap S Q f).2 ≫ Q.negationSubstitutionPair := NullaryInterpretation.negation_pair_comparison S Q f

#print axioms CategoricalEssentialIncompleteness.V46.NullaryInterpretation.negation_pair_comparison

example :
    S.implicationSubstitutionPair ≫ (substitutionCarrierMap S Q f).2 =
      prod.map (substitutionCarrierMap S Q f).2 (substitutionCarrierMap S Q f).2 ≫
        Q.implicationSubstitutionPair := NullaryInterpretation.implication_pair_comparison S Q f

#print axioms CategoricalEssentialIncompleteness.V46.NullaryInterpretation.implication_pair_comparison
