/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NullaryBooleanValuation
public import CategoricalEssentialIncompleteness.V46OptionMask

/-! # Boolean values of the substitution constructors -/

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

/-- A successful result has the Boolean value of its original formula. -/
def PairGood {W : D} (a : W ⟶ S.substitutionCarriers.2) : Prop :=
  a ≫ prod.snd ≫ OptionSyntax.map (valuation S d) =
    OptionSyntax.mask (a ≫ prod.fst ≫ valuation S d) (a ≫ prod.snd)

theorem pairGood_precomp {W U : D} (a : W ⟶ S.substitutionCarriers.2)
    (ha : PairGood S d a) (k : U ⟶ W) : PairGood S d (k ≫ a) := by
  simpa only [PairGood, Category.assoc, OptionSyntax.mask_precomp] using
    congrArg (fun h => k ≫ h) ha

theorem equality_pair_good {W : D} (a b : W ⟶ S.substitutionCarriers.1) :
    PairGood S d (prod.lift a b ≫ S.equalitySubstitutionPair) := by
  simp [PairGood, CategoricalSyntax.equalitySubstitutionPair,
    SyntaxPolynomial.power, SyntaxPolynomial.eval, SyntaxPolynomial.productFunctor,
    CategoricalSyntax.originalProjection, CategoricalSyntax.termResultProjection,
    Category.assoc, equality_value S d, Two.comp_constant]
  simp only [← Category.assoc, OptionSyntax.mask_ok]
  simp only [Category.assoc, equality_value_assoc, Two.comp_constant_assoc]

theorem relation_pair_good {W : D}
    (a : W ⟶ (SyntaxPolynomial.constructors (fun _ => X) 0).eval.obj S.substitutionCarriers) :
    PairGood S d (a ≫ S.relationSubstitutionPair) := by
  simp [PairGood, CategoricalSyntax.relationSubstitutionPair,
    SyntaxPolynomial.constructors, SyntaxPolynomial.power, SyntaxPolynomial.eval,
    SyntaxPolynomial.productFunctor, Category.assoc]
  simpa only [Category.assoc] using (OptionSyntax.mask_ok
    (a ≫ S.relationConstructors ≫ valuation S d) (a ≫ S.relationConstructors)).symm

theorem negation_pair_good {W : D} (a : W ⟶ S.substitutionCarriers.2)
    (ha : PairGood S d a) : PairGood S d (a ≫ S.negationSubstitutionPair) := by
  have hn : OptionSyntax.map S.negationConstructor ≫ OptionSyntax.map (valuation S d) =
      OptionSyntax.map (valuation S d) ≫
        OptionSyntax.map (Two.unary Bool.not (𝟙 (Two D))) := by
    simp [OptionSyntax.map, coprod.map_map, negation_value S d, Two.unary]
  dsimp only [PairGood] at ha ⊢
  simp only [CategoricalSyntax.negationSubstitutionPair, Category.assoc, prod.lift_snd,
    prod.lift_snd_assoc, prod.lift_fst_assoc, hn,
    negation_value S d]
  have hr := congrArg
    (fun h => h ≫ OptionSyntax.map (Two.unary Bool.not (𝟙 (Two D)))) ha
  have hm := OptionSyntax.mask_map
    (a ≫ prod.fst ≫ Two.unary Bool.not (valuation S d))
    (a ≫ prod.snd) S.negationConstructor
  rw [OptionSyntax.mask_postcomp] at hr
  simp only [Category.assoc, Two.unary, Category.id_comp] at hr hm ⊢
  exact hr.trans hm.symm

theorem implication_pair_good {W : D} (a b : W ⟶ S.substitutionCarriers.2)
    (ha : PairGood S d a) (hb : PairGood S d b) :
    PairGood S d (prod.lift a b ≫ S.implicationSubstitutionPair) := by
  have hi : S.implicationConstructor ≫ valuation S d =
      prod.map (valuation S d) (valuation S d) ≫ Two.binaryArrow implies := by
    have he : prod.lift (prod.fst ≫ valuation S d) (prod.snd ≫ valuation S d) =
        prod.map (valuation S d) (valuation S d) := by
      apply prod.hom_ext <;> simp
    simpa only [Two.binary, he] using implication_value S d
  have hn := OptionSyntax.binary_natural_value S.implicationConstructor
    (Two.binaryArrow implies) (valuation S d) (valuation S d) hi
    (a ≫ prod.snd) (b ≫ prod.snd)
  dsimp only [PairGood] at ha hb ⊢
  simp only [CategoricalSyntax.implicationSubstitutionPair, Category.assoc,
    prod.lift_snd, prod.lift_snd_assoc, prod.lift_fst_assoc,
    prod.lift_map_assoc, hn]
  rw [ha, hb]
  rw [implication_value S d]
  simpa only [Two.binary, prod.comp_lift_assoc, prod.lift_fst_assoc,
    prod.lift_snd_assoc, Category.assoc] using (OptionSyntax.mask_binary S.implicationConstructor
      (Two.binaryArrow implies) (a ≫ prod.snd) (b ≫ prod.snd)
      (a ≫ prod.fst ≫ valuation S d) (b ≫ prod.fst ≫ valuation S d)).symm

theorem quantifier_pair_good {W : D} (p : W ⟶ S.substitutionParameters)
    (y : W ⟶ V) (a : W ⟶ S.substitutionCarriers.2) (ha : PairGood S d a) :
    PairGood S d (prod.lift p (prod.lift y a) ≫ S.quantifierSubstitutionPair) := by
  have hq : S.quantifierConstructor ≫ valuation S d =
      prod.map (𝟙 V) (valuation S d) ≫ (prod.snd : V ⨯ Two D ⟶ Two D) := by
    simpa only [prod.map_snd] using quantifier_value S d
  have hn := OptionSyntax.coefficient_natural S.quantifierConstructor
    (prod.snd : V ⨯ Two D ⟶ Two D) (valuation S d) (valuation S d) hq
  have hm := OptionSyntax.mask_coefficient S.quantifierConstructor
    (prod.snd : V ⨯ Two D ⟶ Two D) y (a ≫ prod.snd)
      (a ≫ prod.fst ≫ valuation S d)
  dsimp only [PairGood] at ha ⊢
  simp only [CategoricalSyntax.quantifierSubstitutionPair, Category.assoc,
    prod.lift_snd, prod.lift_snd_assoc, prod.lift_fst_assoc]
  simp only [CategoricalSyntax.quantifierSubstitutionResult,
    StableListAlgebra.Comparison.branch_postcomp, branch_natural,
    OptionSyntax.mask_branch, OptionSyntax.fail_map, OptionSyntax.map_ok, hn,
    CategoricalSyntax.quantifierOriginal, Category.assoc, quantifier_value S d,
    prod.comp_lift_assoc, prod.lift_fst, prod.lift_snd_assoc, prod.lift_map_assoc,
    Category.comp_id]
  have ho : OptionSyntax.mask (a ≫ prod.fst ≫ valuation S d)
      (prod.lift y (a ≫ prod.fst) ≫ S.quantifierConstructor ≫ coprod.inr) =
        a ≫ prod.fst ≫ valuation S d ≫ coprod.inr := by
    simpa only [Category.assoc] using OptionSyntax.mask_ok
      (a ≫ prod.fst ≫ valuation S d)
      (prod.lift y (a ≫ prod.fst) ≫ S.quantifierConstructor)
  simp only [OptionSyntax.comp_fail, OptionSyntax.mask_fail, ho, quantifier_value_assoc,
    prod.lift_snd_assoc]
  rw [ha]
  simpa only [prod.lift_snd, Category.assoc] using congrArg
    (fun h => Two.branch
      (prod.lift p (prod.lift y a) ≫ S.quantifierEquality)
      (Two.branch (prod.lift p (prod.lift y a) ≫ S.captureAllowed)
        OptionSyntax.fail h)
      (a ≫ prod.fst ≫ valuation S d ≫ coprod.inr)) hm.symm

end CategoricalEssentialIncompleteness.V46.NullaryBooleanValuation
