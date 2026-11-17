/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46PropositionalProofCombinators

/-! # Closure tested on parameterized rule instances -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v u
open CategoryTheory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness.V46.RuleClosureFactors
variable {C : Type u} [Category.{v} C] [Regular C]
variable {F : C} {N : ℕ}

/-- A rule input consists of a label and a matching tuple of ordered premises. -/
theorem closed_iff [HasFiniteCoproducts C] (R : RulePresentation F N) (T : Subobject F) :
    ClosedUnder R.inference T.arrow ↔
      ∀ (i : Fin (N+1)) {W : C} (l : W ⟶ R.instances i)
        (p : W ⟶ finitePower (T : C) i.val),
        l ≫ R.premises i = p ≫ finitePowerMap T.arrow i.val →
          T.Factors (l ≫ R.conclusion i) := by
  constructor
  · rintro ⟨s⟩ i W l p h
    have hs : s.left ≫ T.arrow = Sigma.desc (R.ruleConclusion (Over.mk T.arrow)) := Over.w s
    apply (Subobject.factors_iff _ _).mpr
    refine ⟨pullback.lift l p h ≫ Sigma.ι (R.ruleObject (Over.mk T.arrow)) i ≫ s.left, ?_⟩
    rw [Category.assoc, Category.assoc]
    erw [hs, Sigma.ι_comp_desc]
    exact pullback.lift_fst_assoc _ _ _ _
  · intro h
    have hi (i : Fin (N+1)) : T.Factors (R.ruleConclusion (Over.mk T.arrow) i) :=
      h i (pullback.fst _ _) (pullback.snd _ _) pullback.condition
    refine ⟨Over.homMk (Sigma.desc (fun i => T.factorThru _ (hi i))) ?_⟩
    change Sigma.desc _ ≫ T.arrow = Sigma.desc _
    apply Sigma.hom_ext
    intro i
    simp

/-- The nullary coproduct, generalization and ordered modus ponens suffice
for closure under the full finite first-order inference endofunctor. -/
theorem firstOrder_closed [HasFiniteCoproducts C] {L S A V : C}
    (logical : L ⟶ F) (sentence : S ⟶ F) (ax : A ⟶ S)
    (all : V ⨯ F ⟶ F) (imp : F ⨯ F ⟶ F) (T : Subobject F)
    (hn : T.Factors (coprod.desc logical (ax ≫ sentence)))
    (hg : ∀ {W : C} (z : W ⟶ V ⨯ F), T.Factors (z ≫ prod.snd) → T.Factors (z ≫ all))
    (hm : ∀ {W : C} (z : W ⟶ F ⨯ F), T.Factors (z ≫ prod.fst) →
      T.Factors (z ≫ imp) → T.Factors (z ≫ prod.snd)) :
    ClosedUnder (firstOrderRules logical sentence ax all imp).inference T.arrow := by
  apply (closed_iff _ _).mpr
  intro i
  fin_cases i <;> intro W l p h
  · exact Subobject.factors_of_factors_right l hn
  · apply hg l
    change l ≫ prod.snd = p ≫ T.arrow at h
    rw [h]
    exact Subobject.factors_comp_arrow _
  · change l ≫ prod.lift prod.fst imp = p ≫ prod.map T.arrow T.arrow at h
    apply hm l
    all_goals apply (Subobject.factors_iff _ _).mpr
    · exact ⟨p ≫ prod.fst, by simpa using (h =≫ prod.fst).symm⟩
    · exact ⟨p ≫ prod.snd, by simpa using (h =≫ prod.snd).symm⟩

/-- Both children may be any morphisms into the theorem subobject on
the common parameter object. No choice of proof representatives is needed. -/
theorem propositional_mp [FinitaryExtensive C] {Ax : C} (ax : Ax ⟶ F)
    (imp : F ⨯ F ⟶ F) (T : Subobject F)
    (hc : ClosedUnder (ForkInference.rules ax imp).inference T.arrow)
    {W : C} (z : W ⟶ F ⨯ F) (hp : T.Factors (z ≫ prod.fst))
    (hq : T.Factors (z ≫ imp)) : T.Factors (z ≫ prod.snd) := by
  apply (closed_iff _ _).mp hc 2 z
    (prod.lift (T.factorThru _ hp) (T.factorThru _ hq))
  change z ≫ prod.lift prod.fst imp = _ ≫ prod.map T.arrow T.arrow
  apply prod.hom_ext <;> simp

end CategoricalEssentialIncompleteness.V46.RuleClosureFactors
