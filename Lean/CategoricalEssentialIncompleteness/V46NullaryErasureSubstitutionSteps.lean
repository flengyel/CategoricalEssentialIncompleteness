/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NullaryPropositionalErasure
public import CategoricalEssentialIncompleteness.V46NullaryLogicalInterpretation
public import CategoricalEssentialIncompleteness.V46OptionMask

/-! # Erasure of the substitution constructors -/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u
open CategoryTheory CategoryTheory.Limits

namespace CategoricalEssentialIncompleteness.V46.NullaryPropositionalErasure

variable {D : Type u} [Category.{v} D] [Regular D] [FinitaryExtensive D]
variable {V X Y : D}
variable (S : CategoricalSyntax V (fun _ => ⊥_ D) (fun _ => X) 0) (d : X ⟶ Y)
variable (neg : Y ⟶ Y) (imp : Y ⨯ Y ⟶ Y) (truth : ⊤_ D ⟶ Y)

/-- A successful result has the erasure of its original formula. -/
def PairGood {W : D} (a : W ⟶ S.substitutionCarriers.2) : Prop :=
  a ≫ prod.snd ≫ OptionSyntax.map (erase S d neg imp truth) =
    OptionSyntax.mask (a ≫ prod.fst ≫ erase S d neg imp truth) (a ≫ prod.snd)

theorem pairGood_precomp {W U : D} (a : W ⟶ S.substitutionCarriers.2)
    (ha : PairGood S d neg imp truth a) (k : U ⟶ W) : PairGood S d neg imp truth (k ≫ a) := by
  simpa only [PairGood, Category.assoc, OptionSyntax.mask_precomp] using
    congrArg (fun h => k ≫ h) ha

theorem equality_pair_good {W : D} (a b : W ⟶ S.substitutionCarriers.1) :
    PairGood S d neg imp truth (prod.lift a b ≫ S.equalitySubstitutionPair) := by
  simp [PairGood, CategoricalSyntax.equalitySubstitutionPair,
    SyntaxPolynomial.power, SyntaxPolynomial.eval, SyntaxPolynomial.productFunctor,
    CategoricalSyntax.originalProjection, CategoricalSyntax.termResultProjection,
    Category.assoc, equality S d neg imp truth]
  simp only [← Category.assoc, OptionSyntax.mask_ok]
  simp only [Category.assoc, equality_assoc, terminal.comp_from_assoc]

theorem relation_pair_good {W : D}
    (a : W ⟶ (SyntaxPolynomial.constructors (fun _ => X) 0).eval.obj S.substitutionCarriers) :
    PairGood S d neg imp truth (a ≫ S.relationSubstitutionPair) := by
  simp [PairGood, CategoricalSyntax.relationSubstitutionPair,
    SyntaxPolynomial.constructors, SyntaxPolynomial.power, SyntaxPolynomial.eval,
    SyntaxPolynomial.productFunctor, Category.assoc]
  simpa only [Category.assoc] using (OptionSyntax.mask_ok
    (a ≫ S.relationConstructors ≫ erase S d neg imp truth) (a ≫ S.relationConstructors)).symm

theorem negation_pair_good {W : D} (a : W ⟶ S.substitutionCarriers.2)
    (ha : PairGood S d neg imp truth a) : PairGood S d neg imp truth (a ≫
      S.negationSubstitutionPair) := by
  have hn : OptionSyntax.map S.negationConstructor ≫ OptionSyntax.map (erase S d neg imp truth) =
      OptionSyntax.map (erase S d neg imp truth) ≫
        OptionSyntax.map neg := by
    simp [OptionSyntax.map, coprod.map_map, negation S d neg imp truth]
  dsimp only [PairGood] at ha ⊢
  simp only [CategoricalSyntax.negationSubstitutionPair, Category.assoc, prod.lift_snd,
    prod.lift_snd_assoc, prod.lift_fst_assoc, hn,
    negation S d neg imp truth]
  have hr := congrArg
    (fun h => h ≫ OptionSyntax.map neg) ha
  have hm := OptionSyntax.mask_map
    (a ≫ prod.fst ≫ (erase S d neg imp truth ≫ neg))
    (a ≫ prod.snd) S.negationConstructor
  rw [OptionSyntax.mask_postcomp] at hr
  simp only [Category.assoc] at hr hm ⊢
  exact hr.trans hm.symm

theorem implication_pair_good {W : D} (a b : W ⟶ S.substitutionCarriers.2)
    (ha : PairGood S d neg imp truth a) (hb : PairGood S d neg imp truth b) :
    PairGood S d neg imp truth (prod.lift a b ≫ S.implicationSubstitutionPair) := by
  have hi : S.implicationConstructor ≫ erase S d neg imp truth =
      prod.map (erase S d neg imp truth) (erase S d neg imp truth) ≫ imp :=
    implication S d neg imp truth
  have hn := OptionSyntax.binary_natural_value S.implicationConstructor
    imp (erase S d neg imp truth) (erase S d neg imp truth) hi
    (a ≫ prod.snd) (b ≫ prod.snd)
  dsimp only [PairGood] at ha hb ⊢
  simp only [CategoricalSyntax.implicationSubstitutionPair, Category.assoc,
    prod.lift_snd, prod.lift_snd_assoc, prod.lift_fst_assoc,
    prod.lift_map_assoc, hn]
  rw [ha, hb]
  rw [implication S d neg imp truth]
  simpa only [prod.lift_map_assoc, Category.assoc] using (OptionSyntax.mask_binary
    S.implicationConstructor
      imp (a ≫ prod.snd) (b ≫ prod.snd)
      (a ≫ prod.fst ≫ erase S d neg imp truth) (b ≫ prod.fst ≫ erase S d neg imp truth)).symm

theorem quantifier_pair_good {W : D} (p : W ⟶ S.substitutionParameters)
    (y : W ⟶ V) (a : W ⟶ S.substitutionCarriers.2) (ha : PairGood S d neg imp truth a) :
    PairGood S d neg imp truth (prod.lift p (prod.lift y a) ≫ S.quantifierSubstitutionPair) := by
  have hq : S.quantifierConstructor ≫ erase S d neg imp truth =
      prod.map (𝟙 V) (erase S d neg imp truth) ≫ (prod.snd : V ⨯ Y ⟶ Y) := by
    simpa only [prod.map_snd] using quantifier S d neg imp truth
  have hn := OptionSyntax.coefficient_natural S.quantifierConstructor
    (prod.snd : V ⨯ Y ⟶ Y) (erase S d neg imp truth) (erase S d neg imp truth) hq
  have hm := OptionSyntax.mask_coefficient S.quantifierConstructor
    (prod.snd : V ⨯ Y ⟶ Y) y (a ≫ prod.snd)
      (a ≫ prod.fst ≫ erase S d neg imp truth)
  dsimp only [PairGood] at ha ⊢
  simp only [CategoricalSyntax.quantifierSubstitutionPair, Category.assoc,
    prod.lift_snd, prod.lift_snd_assoc, prod.lift_fst_assoc]
  simp only [CategoricalSyntax.quantifierSubstitutionResult,
    StableListAlgebra.Comparison.branch_postcomp, branch_natural,
    OptionSyntax.mask_branch, OptionSyntax.fail_map, OptionSyntax.map_ok, hn,
    CategoricalSyntax.quantifierOriginal, Category.assoc, quantifier S d neg imp truth,
    prod.comp_lift_assoc, prod.lift_fst, prod.lift_snd_assoc, prod.lift_map_assoc,
    Category.comp_id]
  have ho : OptionSyntax.mask (a ≫ prod.fst ≫ erase S d neg imp truth)
      (prod.lift y (a ≫ prod.fst) ≫ S.quantifierConstructor ≫ coprod.inr) =
        a ≫ prod.fst ≫ erase S d neg imp truth ≫ coprod.inr := by
    simpa only [Category.assoc] using OptionSyntax.mask_ok
      (a ≫ prod.fst ≫ erase S d neg imp truth)
      (prod.lift y (a ≫ prod.fst) ≫ S.quantifierConstructor)
  simp only [OptionSyntax.comp_fail, OptionSyntax.mask_fail, ho, quantifier_assoc,
    prod.lift_snd_assoc]
  rw [ha]
  simpa only [prod.lift_snd, Category.assoc] using congrArg
    (fun h => Two.branch
      (prod.lift p (prod.lift y a) ≫ S.quantifierEquality)
      (Two.branch (prod.lift p (prod.lift y a) ≫ S.captureAllowed)
        OptionSyntax.fail h)
      (a ≫ prod.fst ≫ erase S d neg imp truth ≫ coprod.inr)) hm.symm

end CategoricalEssentialIncompleteness.V46.NullaryPropositionalErasure
