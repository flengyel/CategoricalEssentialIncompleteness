/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerDerivationValidation


/-! # Ordered-premise validation in the uniform carrier category -/

@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46
open CategoricalEssentialIncompleteness.V46.Miller
variable {P : Uniform.Family} {F : Total.TotalCategory P} {N : ℕ} (R : RulePresentation F N)
example : (Derivation.interpretation (P := P)).ReflectsIsomorphisms := inferInstance
example : PreservesLimitsOfShape WalkingCospan (Derivation.interpretation (P := P)) := inferInstance
example : PreservesColimitsOfShape (Discrete WalkingPair) (Derivation.interpretation (P := P)) := inferInstance
example :
    SyntacticDerivation.SliceInitial.functor (SyntacticDerivation.PolynomialComparison.ordinary R) (Derivation.validator R) ⋙
      Derivation.success (F := F) ≅ Derivation.success (F := F) ⋙ R.inference := Derivation.successComparison R
example (Q : Over F) (i : Fin (N+1)) {Z : Total.TotalCategory P} (h : R.ruleObject Q i ⟶ Z) :
    IsPullback (SyntacticDerivation.CheckedRoot.matchingMap R Q i) h (Derivation.checkedOperation R Q i h) coprod.inr :=
  Derivation.checkedOperation_success R Q i h
example (Q : Over F) (i : Fin (N+1)) :
    R.ruleObject Q i=pullback (R.premises i) (finitePowerMap Q.hom i.val) := rfl
example (Q : Over F) : R.nullaryRule Q ≫ R.ruleConclusion Q 0=R.conclusion 0 := by
  have h := congrArg (fun k => k ≫ R.conclusion 0) (R.nullaryRule_fst Q)
  change (R.nullaryRule Q ≫ pullback.fst (R.premises 0) (finitePowerMap Q.hom 0)) ≫ R.conclusion 0=
    (𝟙 (R.instances 0)) ≫ R.conclusion 0 at h
  erw [Category.assoc,Category.id_comp] at h
  change R.nullaryRule Q ≫ pullback.fst (R.premises 0) (finitePowerMap Q.hom 0) ≫ R.conclusion 0=R.conclusion 0
  exact h
example (i : Fin (N+1)) :
    Derivation.booleanComponent R i ≫ prod.snd=prod.fst ≫ R.conclusion i :=
  Derivation.booleanComponent_conclusion R i
