/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46DerivationConclusionInduction
import CategoricalEssentialIncompleteness.V46FirstOrderInference

/-! # Standard conclusion induction for the original first-order rules -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticLists
namespace CategoricalEssentialIncompleteness.V46.SyntacticDerivation.StandardInduction
variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]

section Models
variable (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T]

/-- The actual model functor preserves the chosen binary coproduct;
every point therefore comes from one of its two actual injections. -/
theorem model_coprod_cases (A B : PredicateCategory T) (z : Obj T M (A ⨿ B)) :
    (∃ a : Obj T M A, (F T M).map (coprod.inl : A ⟶ A ⨿ B) a = z) ∨
      (∃ b : Obj T M B, (F T M).map (coprod.inr : B ⟶ A ⨿ B) b = z) := by
  have h := isColimitOfHasBinaryCoproductOfPreservesColimit (F T M) A B
  have hc := (Types.binaryCofan_isColimit_iff _).mp ⟨h⟩
  exact (Set.eq_univ_iff_forall.mp hc.2.2.sup_eq_top) z

theorem model_copair_predicate {A B Y : PredicateCategory T} (f : A ⟶ Y) (g : B ⟶ Y)
    (P : Obj T M Y → Prop)
    (hf : ∀ a : Obj T M A, P ((F T M).map f a))
    (hg : ∀ b : Obj T M B, P ((F T M).map g b))
    (z : Obj T M (A ⨿ B)) : P ((F T M).map (coprod.desc f g) z) := by
  rcases model_coprod_cases T M A B z with ⟨a,rfl⟩ | ⟨b,rfl⟩
  · rw [← Functor.map_comp_apply,coprod.inl_desc]
    exact hf a
  · rw [← Functor.map_comp_apply,coprod.inr_desc]
    exact hg b

end Models

section Standard
variable [ℕ↓[ℒₒᵣ] ⊧* T]
variable {V Fm L Sent A : PredicateCategory T}
variable (logical : L ⟶ Fm) (sentence : Sent ⟶ Fm) (axioms : A ⟶ Sent)
variable (all : V ⨯ Fm ⟶ Fm) (imp : Fm ⨯ Fm ⟶ Fm)

/-- The constructed first-order derivations satisfy any formula
predicate containing the actual axiom conclusions and closed under
generalization and ordered modus ponens. Each premise is read through
the original rule pullback. -/
theorem firstOrder_conclusion_induction (P : Obj T ℕ Fm → Prop)
    (hlogical : ∀ l : Obj T ℕ L, P ((F T ℕ).map logical l))
    (haxioms : ∀ a : Obj T ℕ A, P ((F T ℕ).map (axioms ≫ sentence) a))
    (hgeneralization : ∀ z : Obj T ℕ (V ⨯ Fm),
      P ((F T ℕ).map (prod.snd : V ⨯ Fm ⟶ Fm) z) → P ((F T ℕ).map all z))
    (hmodusPonens : ∀ z : Obj T ℕ (Fm ⨯ Fm),
      P ((F T ℕ).map (prod.fst : Fm ⨯ Fm ⟶ Fm) z) →
      P ((F T ℕ).map imp z) → P ((F T ℕ).map (prod.snd : Fm ⨯ Fm ⟶ Fm) z)) :
    ∀ d : Obj T ℕ (derivationAlgebra T (firstOrderRules logical sentence axioms all imp)).a.left,
      P ((F T ℕ).map (derivationAlgebra T
        (firstOrderRules logical sentence axioms all imp)).a.hom d) := by
  let R := firstOrderRules logical sentence axioms all imp
  apply conclusion_induction T R P
  intro i r ih
  fin_cases i
  · change P ((F T ℕ).map (pullback.fst _ _ ≫ coprod.desc logical (axioms ≫ sentence)) r)
    rw [Functor.map_comp_apply]
    exact model_copair_predicate T ℕ logical (axioms ≫ sentence) P hlogical haxioms _
  · change P ((F T ℕ).map (pullback.fst _ _ ≫ all) r)
    rw [Functor.map_comp_apply]
    apply hgeneralization
    have h := ih (0 : Fin 1)
    change P ((F T ℕ).map (pullback.fst _ _ ≫ prod.snd ≫ finiteChild T Fm 1 0) r) at h
    erw [finiteChild_one,Category.comp_id,Functor.map_comp_apply] at h
    exact h
  · change P ((F T ℕ).map (pullback.fst _ _ ≫ prod.snd) r)
    rw [Functor.map_comp_apply]
    apply hmodusPonens
    · have h := ih (0 : Fin 2)
      change P ((F T ℕ).map
        (pullback.fst _ _ ≫ prod.lift prod.fst imp ≫ finiteChild T Fm 2 0) r) at h
      erw [finiteChild_two_zero,prod.lift_fst,Functor.map_comp_apply] at h
      exact h
    · have h := ih (1 : Fin 2)
      change P ((F T ℕ).map
        (pullback.fst _ _ ≫ prod.lift prod.fst imp ≫ finiteChild T Fm 2 1) r) at h
      erw [finiteChild_two_one,prod.lift_snd,Functor.map_comp_apply] at h
      exact h

end Standard
end CategoricalEssentialIncompleteness.V46.SyntacticDerivation.StandardInduction
