/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NullarySubstitutionCapture

/-! # The quantified-formula substitution comparison -/

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

theorem quantifier_result_comparison :
    S.quantifierSubstitutionResult ≫ OptionSyntax.map (interpretation S Q f).2 =
      quantifierInputMap S Q f ≫ Q.quantifierSubstitutionResult := by
  have ho : S.quantifierOriginal ≫ (interpretation S Q f).2 ≫
      (coprod.inr : Q.algebra.a.2 ⟶ OptionSyntax.obj Q.algebra.a.2) =
      quantifierInputMap S Q f ≫ Q.quantifierOriginal ≫ coprod.inr := by
    simpa only [Category.assoc] using congrArg (fun k => k ≫ coprod.inr)
      (quantifier_original_comparison S Q f)
  have hc := OptionSyntax.coefficient_natural S.quantifierConstructor Q.quantifierConstructor
    (interpretation S Q f).2 (interpretation S Q f).2 (quantifier S Q f)
  simp only [CategoricalSyntax.quantifierSubstitutionResult,
    StableListAlgebra.Comparison.branch_postcomp, branch_natural,
    quantifier_equality_comparison, capture_comparison, Category.assoc,
    OptionSyntax.fail_map, OptionSyntax.map_ok, ho, hc]
  congr 1
  · congr 1
    · simp [OptionSyntax.fail]
    · simp [quantifierInputMap, substitutionCarrierMap, prod.comp_lift_assoc,
        prod.lift_map_assoc]

theorem quantifier_pair_comparison :
    S.quantifierSubstitutionPair ≫ (substitutionCarrierMap S Q f).2 =
      quantifierInputMap S Q f ≫ Q.quantifierSubstitutionPair := by
  apply prod.hom_ext
  · simpa only [CategoricalSyntax.quantifierSubstitutionPair, substitutionCarrierMap,
      Category.assoc, prod.map_fst, prod.lift_fst, prod.lift_fst_assoc] using
      quantifier_original_comparison S Q f
  · simpa only [CategoricalSyntax.quantifierSubstitutionPair, substitutionCarrierMap,
      Category.assoc, prod.map_snd, prod.lift_snd, prod.lift_snd_assoc] using
      quantifier_result_comparison S Q f

end CategoricalEssentialIncompleteness.V46.NullaryInterpretation
