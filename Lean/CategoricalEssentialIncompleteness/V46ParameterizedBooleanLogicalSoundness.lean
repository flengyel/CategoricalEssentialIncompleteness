/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ParameterizedBooleanSubstitution
public import CategoricalEssentialIncompleteness.V46ParameterizedBooleanLogical

/-! # All seven logical schemes at a varying internal support -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v u
open CategoryTheory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness.V46.ParameterizedBooleanValuation
variable {D : Type u} [Category.{v} D] [Regular D] [FinitaryExtensive D]
variable {V X : D}
variable (S : CategoricalSyntax V (fun _ => ⊥_ D) (fun _ => X) 0) (P : D)
variable (d : constantFamily P X ⟶ constantFamily P (Two D))
variable {W : D} (p : W ⟶ P)

theorem evaluate_equality_input (a : W ⟶ S.algebra.a.1 ⨯ S.algebra.a.1) :
    evaluate S P d p (a ≫ S.equalityConstructor) = Two.constant W true := by
  simpa only [parameterPair_eta] using
    evaluate_equality S P d p (a ≫ prod.fst) (a ≫ prod.snd)

theorem substitution_input_value (i : W ⟶ S.admissibleSubstitution)
    (a : W ⟶ S.algebra.a.2 ⨯ S.substitutionParameters) (ha : a = i ≫ S.admissibleInclusion) :
    evaluate S P d p (i ≫ S.formulaSubstitution) = evaluate S P d p (a ≫ prod.fst) := by
  have h := substitution_value S P d p i
  rw [← Category.assoc, ← ha] at h
  exact h

theorem hilbert_instantiation_value (a : W ⟶ S.instantiationParameters) :
    evaluate S P d p (a ≫ S.hilbertInstantiation) = Two.constant W true := by
  have hs := substitution_input_value S P d p (a ≫ S.instantiationAdmissible)
    (a ≫ S.instantiationInclusion ≫ S.instantiationInput)
    (by simpa only [Category.assoc] using
      congrArg (fun k => a ≫ k) S.instantiation_admissible)
  simp only [CategoricalSyntax.instantiationInput, ← Category.assoc,
    prod.comp_lift, prod.lift_fst] at hs
  simp only [CategoricalSyntax.hilbertInstantiation, ← Category.assoc, prod.comp_lift,
    evaluate_implication_input, evaluate_quantifier_input, prod.lift_fst, prod.lift_snd, hs]
  exact NullaryBooleanValuation.implication_self (D := D) _

theorem hilbert_equality_value (a : W ⟶ S.equalitySchemeParameters) :
    evaluate S P d p (a ≫ S.hilbertEquality) = Two.constant W true := by
  have h₁ := substitution_input_value S P d p (a ≫ S.equalityFirstAdmissible)
    (a ≫ S.equalitySchemeInclusion ≫ S.equalityFirstInput)
    (by simpa only [Category.assoc] using
      congrArg (fun k => a ≫ k) S.equality_first_admissible)
  have h₂ := substitution_input_value S P d p (a ≫ S.equalitySecondAdmissible)
    (a ≫ S.equalitySchemeInclusion ≫ S.equalitySecondInput)
    (by simpa only [Category.assoc] using
      congrArg (fun k => a ≫ k) S.equality_second_admissible)
  simp only [CategoricalSyntax.equalityFirstInput, CategoricalSyntax.equalitySecondInput,
    ← Category.assoc, prod.comp_lift, prod.lift_fst] at h₁ h₂
  simp only [CategoricalSyntax.hilbertEquality, ← Category.assoc, prod.comp_lift,
    evaluate_implication_input, evaluate_equality_input, prod.lift_fst, prod.lift_snd,
    h₁, h₂, NullaryBooleanValuation.implication_self]

private theorem coprod_scheme_true {A B : D} (f : A ⟶ S.algebra.a.2) (g : B ⟶ S.algebra.a.2)
    (hf : ∀ {U : D} (p : U ⟶ P) (a : U ⟶ A),
      evaluate S P d p (a ≫ f) = Two.constant U true)
    (hg : ∀ {U : D} (p : U ⟶ P) (b : U ⟶ B),
      evaluate S P d p (b ≫ g) = Two.constant U true)
    (p : W ⟶ P) (a : W ⟶ A ⨿ B) :
    evaluate S P d p (a ≫ coprod.desc f g) = Two.constant W true := by
  apply BinaryCofan.IsColimit.hom_ext (SumFibers.isColimit a)
  · change pullback.fst a coprod.inl ≫ evaluate S P d p (a ≫ coprod.desc f g) =
      pullback.fst a coprod.inl ≫ Two.constant W true
    rw [evaluate_precomp, Two.comp_constant]
    have hk : pullback.fst a coprod.inl ≫ a = pullback.snd a coprod.inl ≫ coprod.inl :=
      pullback.condition
    have hl : pullback.fst a coprod.inl ≫ (a ≫ coprod.desc f g) =
        pullback.snd a coprod.inl ≫ f := by
      rw [← Category.assoc, hk, Category.assoc, coprod.inl_desc]
    rw [hl]
    exact hf _ _
  · change pullback.fst a coprod.inr ≫ evaluate S P d p (a ≫ coprod.desc f g) =
      pullback.fst a coprod.inr ≫ Two.constant W true
    rw [evaluate_precomp, Two.comp_constant]
    have hk : pullback.fst a coprod.inr ≫ a = pullback.snd a coprod.inr ≫ coprod.inr :=
      pullback.condition
    have hl : pullback.fst a coprod.inr ≫ (a ≫ coprod.desc f g) =
        pullback.snd a coprod.inr ≫ g := by
      rw [← Category.assoc, hk, Category.assoc, coprod.inr_desc]
    rw [hl]
    exact hg _ _

/-- The finite coproduct of the seven scheme objects is true at every shared parameter,
including on arbitrary input families. -/
theorem logical_axioms_value (a : W ⟶ S.logicalParameters) :
    evaluate S P d p (a ≫ S.logicalAxioms) = Two.constant W true := by
  unfold CategoricalSyntax.logicalAxioms
  apply coprod_scheme_true S P d _ _ ?_ ?_ p a
  · intro U p a
    apply coprod_scheme_true S P d _ _ ?_ ?_ p a
    · intro U p a
      apply coprod_scheme_true S P d _ _ ?_ ?_ p a
      · intro U p a
        apply coprod_scheme_true S P d _ _ ?_ ?_ p a
        · intro U p a
          apply coprod_scheme_true S P d _ _ ?_ ?_ p a
          · intro U p a
            apply coprod_scheme_true S P d _ _ ?_ ?_ p a
            · intro U p a
              exact hilbert_one_value S P d p a
            · intro U p a
              exact hilbert_two_value S P d p a
          · intro U p a
            exact hilbert_three_value S P d p a
        · intro U p a
          exact hilbert_instantiation_value S P d p a
      · intro U p a
        exact hilbert_distribution_value S P d p a
    · intro U p a
      exact hilbert_reflexivity_value S P d p a
  · intro U p a
    exact hilbert_equality_value S P d p a

end CategoricalEssentialIncompleteness.V46.ParameterizedBooleanValuation
