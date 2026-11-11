/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NullarySubstitutionAlgebra
public import CategoricalEssentialIncompleteness.V46OptionSyntaxNaturality

/-! # Constructor equations for the substitution comparison -/

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

theorem variable_pair_comparison :
    S.variableSubstitutionPair ≫ (substitutionCarrierMap S Q f).1 = targetVariablePair S Q f := by
  have hE := S.decidableVariables.unique Q.decidableVariables
  apply prod.hom_ext
  · simp [substitutionCarrierMap, CategoricalSyntax.variableSubstitutionPair,
      targetVariablePair, Category.assoc, variable_law S Q f]
  · simp [substitutionCarrierMap, CategoricalSyntax.variableSubstitutionPair,
      targetVariablePair, substitutionParameterMap, Category.assoc,
      StableListAlgebra.Comparison.branch_postcomp, branch_natural, hE,
      prod.comp_lift_assoc, prod.map_fst_assoc, prod.map_snd_assoc,
      variable_law S Q f]

theorem equality_pair_comparison :
    S.equalitySubstitutionPair ≫ (substitutionCarrierMap S Q f).2 =
      prod.map (substitutionCarrierMap S Q f).1 (substitutionCarrierMap S Q f).1 ≫
        Q.equalitySubstitutionPair := by
  have heq : S.equalityConstructor ≫ (interpretation S Q f).2 ≫
      (coprod.inr : Q.algebra.a.2 ⟶ OptionSyntax.obj Q.algebra.a.2) =
      prod.map (interpretation S Q f).1 (interpretation S Q f).1 ≫
        Q.equalityConstructor ≫ coprod.inr := by
    simpa only [Category.assoc] using
      congrArg (fun k => k ≫ coprod.inr) (equality S Q f)
  apply prod.hom_ext <;>
    simp [substitutionCarrierMap, CategoricalSyntax.equalitySubstitutionPair,
      CategoricalSyntax.originalProjection, CategoricalSyntax.termResultProjection,
      SyntaxPolynomial.power, SyntaxPolynomial.eval, SyntaxPolynomial.productFunctor,
      OptionSyntax.map, Category.assoc, equality S Q f, heq]

theorem negation_pair_comparison :
    S.negationSubstitutionPair ≫ (substitutionCarrierMap S Q f).2 =
      (substitutionCarrierMap S Q f).2 ≫ Q.negationSubstitutionPair := by
  apply prod.hom_ext <;>
    simp [substitutionCarrierMap, CategoricalSyntax.negationSubstitutionPair,
      OptionSyntax.map, negation S Q f, coprod.map_map]

theorem implication_pair_comparison :
    S.implicationSubstitutionPair ≫ (substitutionCarrierMap S Q f).2 =
      prod.map (substitutionCarrierMap S Q f).2 (substitutionCarrierMap S Q f).2 ≫
        Q.implicationSubstitutionPair := by
  have ho := OptionSyntax.binary_natural S.implicationConstructor Q.implicationConstructor
    (interpretation S Q f).2 (interpretation S Q f).2 (implication S Q f)
  apply prod.hom_ext <;>
    simp [substitutionCarrierMap, CategoricalSyntax.implicationSubstitutionPair,
      SyntaxPolynomial.power, SyntaxPolynomial.eval, SyntaxPolynomial.productFunctor,
      Category.assoc, implication S Q f, ho]

end CategoricalEssentialIncompleteness.V46.NullaryInterpretation
