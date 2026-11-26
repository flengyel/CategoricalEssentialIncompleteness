/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NullarySubstitutionPairs

/-! # Capture tests under interpretation of propositional atoms -/

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

theorem formula_membership {W : D} (x : W ⟶ V) (a : W ⟶ S.algebra.a.2) :
    prod.lift x (a ≫ (interpretation S Q f).2 ≫ Q.formulaOccurrences) ≫
        Q.lists.membership Q.decidableVariables =
      prod.lift x (a ≫ S.formulaOccurrences) ≫ S.lists.membership S.decidableVariables := by
  rw [formula_occurrences]
  have hE := S.decidableVariables.unique Q.decidableVariables
  have h := congrArg (fun k => prod.lift x (a ≫ S.formulaOccurrences) ≫ k)
    (StableListAlgebra.Comparison.membership S.lists Q.lists Q.decidableVariables)
  simpa only [Category.assoc, prod.lift_map_assoc, Category.comp_id, hE] using h

theorem term_membership {W : D} (x : W ⟶ V) (a : W ⟶ S.algebra.a.1) :
    prod.lift x (a ≫ (interpretation S Q f).1 ≫ Q.termOccurrences) ≫
        Q.lists.membership Q.decidableVariables =
      prod.lift x (a ≫ S.termOccurrences) ≫ S.lists.membership S.decidableVariables := by
  rw [term_occurrences]
  have hE := S.decidableVariables.unique Q.decidableVariables
  have h := congrArg (fun k => prod.lift x (a ≫ S.termOccurrences) ≫ k)
    (StableListAlgebra.Comparison.membership S.lists Q.lists Q.decidableVariables)
  simpa only [Category.assoc, prod.lift_map_assoc, Category.comp_id, hE] using h

def quantifierInputMap : S.substitutionParameters ⨯ (V ⨯ S.substitutionCarriers.2) ⟶
    Q.substitutionParameters ⨯ (V ⨯ Q.substitutionCarriers.2) :=
  prod.map (substitutionParameterMap S Q f)
    (prod.map (𝟙 V) (substitutionCarrierMap S Q f).2)

theorem quantifier_equality_comparison :
    quantifierInputMap S Q f ≫ Q.quantifierEquality = S.quantifierEquality := by
  have hE := S.decidableVariables.unique Q.decidableVariables
  simp [quantifierInputMap, CategoricalSyntax.quantifierEquality,
    prod.comp_lift_assoc, hE]

theorem capture_comparison : quantifierInputMap S Q f ≫ Q.captureAllowed = S.captureAllowed := by
  let W := S.substitutionParameters ⨯ (V ⨯ S.substitutionCarriers.2)
  have hF := formula_membership S Q f
    ((prod.fst : W ⟶ S.substitutionParameters) ≫ prod.fst)
    (prod.snd ≫ prod.snd ≫ prod.fst)
  have hT := term_membership S Q f
    ((prod.snd : W ⟶ V ⨯ S.substitutionCarriers.2) ≫ prod.fst)
    (prod.fst ≫ prod.snd)
  simp only [Category.assoc, prod.lift_fst_comp_snd_comp] at hF hT
  simp [quantifierInputMap, CategoricalSyntax.captureAllowed, substitutionCarrierMap,
    Two.comp_binary, Two.comp_unary, prod.comp_lift_assoc,
    prod.map_fst_assoc, prod.map_snd_assoc, hF, hT]

theorem quantifier_original_comparison :
    S.quantifierOriginal ≫ (interpretation S Q f).2 =
      quantifierInputMap S Q f ≫ Q.quantifierOriginal := by
  simp [quantifierInputMap, CategoricalSyntax.quantifierOriginal, substitutionCarrierMap,
    Category.assoc, quantifier S Q f, prod.comp_lift_assoc, prod.lift_map_assoc]

end CategoricalEssentialIncompleteness.V46.NullaryInterpretation
