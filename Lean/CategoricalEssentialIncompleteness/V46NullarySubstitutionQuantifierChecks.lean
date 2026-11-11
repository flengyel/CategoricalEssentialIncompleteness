/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NullarySubstitutionQuantifier

/-! # Statement checks for NullarySubstitutionQuantifier -/

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
    S.quantifierSubstitutionResult ≫ OptionSyntax.map (interpretation S Q f).2 =
      quantifierInputMap S Q f ≫ Q.quantifierSubstitutionResult := NullaryInterpretation.quantifier_result_comparison S Q f

#print axioms CategoricalEssentialIncompleteness.V46.NullaryInterpretation.quantifier_result_comparison

example :
    S.quantifierSubstitutionPair ≫ (substitutionCarrierMap S Q f).2 =
      quantifierInputMap S Q f ≫ Q.quantifierSubstitutionPair := NullaryInterpretation.quantifier_pair_comparison S Q f

#print axioms CategoricalEssentialIncompleteness.V46.NullaryInterpretation.quantifier_pair_comparison
