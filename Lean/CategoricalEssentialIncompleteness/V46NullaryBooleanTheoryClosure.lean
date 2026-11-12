/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NullaryBooleanLogicalSoundness

/-! # The inference algebra on Boolean-true formulas -/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u
open CategoryTheory CategoryTheory.Limits

namespace CategoricalEssentialIncompleteness.V46.NullaryBooleanValuation

variable {D : Type u} [Category.{v} D] [Regular D] [FinitaryExtensive D]
variable {V X : D}
variable (S : CategoricalSyntax V (fun _ => ⊥_ D) (fun _ => X) 0) (d : X ⟶ Two D)

abbrev trueFormulas := Two.Fiber (valuation S d) true

abbrev trueInclusion : trueFormulas S d ⟶ S.algebra.a.2 :=
  Two.fiberι (valuation S d) true

theorem modus_ponens {W : D} (a b : W ⟶ S.algebra.a.2)
    (ha : a ≫ valuation S d = Two.constant W true)
    (hab : prod.lift a b ≫ S.implicationConstructor ≫ valuation S d = Two.constant W true) :
    b ≫ valuation S d = Two.constant W true := by
  simpa only [implication_value, Two.comp_binary, prod.lift_fst_assoc,
    prod.lift_snd_assoc, ha, implication_true_left] using hab

theorem rule_value {A : D} (a : A ⟶ S.sentenceObject)
    (ha : a ≫ S.sentenceInclusion ≫ valuation S d = Two.constant A true)
    (i : Fin 3) :
    (S.logicalRules a).ruleConclusion (Over.mk (trueInclusion S d)) i ≫ valuation S d =
      Two.constant _ true := by
  fin_cases i
  · change (pullback.fst _ _ ≫ coprod.desc S.logicalAxioms
      (a ≫ S.sentenceInclusion)) ≫ valuation S d = _
    have h : coprod.desc S.logicalAxioms (a ≫ S.sentenceInclusion) ≫ valuation S d =
        Two.constant (S.logicalParameters ⨿ A) true := by
      apply coprod.hom_ext
      · simp [Category.assoc, logical_axioms_value]
      · simpa only [coprod.inr_desc_assoc, Two.comp_constant, Category.assoc] using ha
    rw [Category.assoc, h, Two.comp_constant]
    rfl
  · change (pullback.fst (prod.snd : V ⨯ S.algebra.a.2 ⟶ S.algebra.a.2)
      (trueInclusion S d) ≫ S.quantifierConstructor) ≫ valuation S d = _
    rw [Category.assoc, quantifier_value, ← Category.assoc, pullback.condition,
      Category.assoc, Two.fiberι_comp, Two.comp_constant]
    rfl
  · let W := pullback (prod.lift (prod.fst : S.algebra.a.2 ⨯ S.algebra.a.2 ⟶ _)
        S.implicationConstructor) (prod.map (trueInclusion S d) (trueInclusion S d))
    let k : W ⟶ S.algebra.a.2 ⨯ S.algebra.a.2 := pullback.fst _ _
    have hp : k ≫ prod.lift prod.fst S.implicationConstructor =
        pullback.snd _ _ ≫ prod.map (trueInclusion S d) (trueInclusion S d) :=
      pullback.condition
    have h₁ := congrArg (fun f => f ≫ prod.fst ≫ valuation S d) hp
    have h₂ := congrArg (fun f => f ≫ prod.snd ≫ valuation S d) hp
    simp only [Category.assoc, prod.lift_fst_assoc, prod.map_fst_assoc,
      Two.fiberι_comp, Two.comp_constant] at h₁
    simp only [Category.assoc, prod.lift_snd_assoc, prod.map_snd_assoc,
      Two.fiberι_comp, Two.comp_constant] at h₂
    change (k ≫ prod.snd) ≫ valuation S d = Two.constant W true
    simpa only [Category.assoc] using modus_ponens S d
      (k ≫ prod.fst) (k ≫ prod.snd) (by simpa only [Category.assoc] using h₁) (by
        simpa only [← prod.comp_lift_assoc, prod.lift_fst_snd, Category.assoc,
          Category.id_comp] using h₂)

def truthAlgebra {A : D} (a : A ⟶ S.sentenceObject)
    (ha : a ≫ S.sentenceInclusion ≫ valuation S d = Two.constant A true) :
    Endofunctor.Algebra (S.logicalRules a).inference where
  a := Over.mk (trueInclusion S d)
  str := Over.homMk (Sigma.desc fun i => equalizer.lift
    ((S.logicalRules a).ruleConclusion (Over.mk (trueInclusion S d)) i)
    (by rw [rule_value S d a ha i, Two.comp_constant])) (by
      apply Sigma.hom_ext
      intro i
      simp [RulePresentation.inference])

theorem truth_closed {A : D} (a : A ⟶ S.sentenceObject)
    (ha : a ≫ S.sentenceInclusion ≫ valuation S d = Two.constant A true) :
    ClosedUnder (S.logicalRules a).inference (trueInclusion S d) :=
  ⟨(truthAlgebra S d a ha).str⟩

end CategoricalEssentialIncompleteness.V46.NullaryBooleanValuation
