/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ParameterizedBooleanOption

/-! # The substitution-value invariant with a shared support parameter -/

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

/-- Success has the value of the original formula at the same parameter. -/
def PairGood {W : D} (p : W ⟶ P) (a : W ⟶ S.substitutionCarriers.2) : Prop :=
  ParameterizedOption.map (value S P d) p (a ≫ prod.snd) =
    OptionSyntax.mask (evaluate S P d p (a ≫ prod.fst)) (a ≫ prod.snd)

theorem pairGood_precomp {W U : D} (p : W ⟶ P) (a : W ⟶ S.substitutionCarriers.2)
    (ha : PairGood S P d p a) (k : U ⟶ W) : PairGood S P d (k ≫ p) (k ≫ a) := by
  have h := congrArg (fun f => k ≫ f) ha
  simpa only [PairGood, ParameterizedOption.map_precomp, OptionSyntax.mask_precomp,
    evaluate_precomp, Category.assoc] using h

theorem equality_pair_good {W : D} (p : W ⟶ P)
    (a b : W ⟶ S.substitutionCarriers.1) :
    PairGood S P d p (prod.lift a b ≫ S.equalitySubstitutionPair) := by
  simp only [PairGood, CategoricalSyntax.substitutionCarriers,
    CategoricalSyntax.equalitySubstitutionPair,
    SyntaxPolynomial.power, SyntaxPolynomial.eval, SyntaxPolynomial.productFunctor,
    CategoricalSyntax.originalProjection, CategoricalSyntax.termResultProjection,
    CategoryTheory.Prod.fst,
    Category.assoc, prod.lift_fst, prod.lift_snd, prod.lift_map_assoc]
  simp only [← Category.assoc, ParameterizedOption.map_ok, OptionSyntax.mask_ok]
  rw [evaluate_equality]
  simpa only [evaluate, Category.assoc] using congrArg (fun f => f ≫ coprod.inr)
    (evaluate_equality S P d p (a ≫ prod.snd) (b ≫ prod.snd))

theorem relation_pair_good {W : D} (p : W ⟶ P)
    (a : W ⟶ (SyntaxPolynomial.constructors (fun _ => X) 0).eval.obj S.substitutionCarriers) :
    PairGood S P d p (a ≫ S.relationSubstitutionPair) := by
  simp only [PairGood, CategoricalSyntax.substitutionCarriers,
    CategoricalSyntax.relationSubstitutionPair,
    SyntaxPolynomial.constructors, SyntaxPolynomial.power, SyntaxPolynomial.eval,
    SyntaxPolynomial.productFunctor, Category.assoc, prod.lift_fst, prod.lift_snd,
    Functor.const_obj_map]
  simp only [← Category.assoc, ParameterizedOption.map_ok, OptionSyntax.mask_ok]
  rfl

theorem negation_pair_good {W : D} (p : W ⟶ P) (a : W ⟶ S.substitutionCarriers.2)
    (ha : PairGood S P d p a) :
    PairGood S P d p (a ≫ S.negationSubstitutionPair) := by
  dsimp only [PairGood, CategoricalSyntax.substitutionCarriers] at ha ⊢
  simp only [CategoricalSyntax.negationSubstitutionPair, Category.assoc,
    prod.lift_fst, prod.lift_snd]
  simp only [← Category.assoc] at ⊢
  have h := congrArg (fun f => f ≫ OptionSyntax.map (Two.unary Bool.not (𝟙 (Two D)))) ha
  rw [OptionSyntax.mask_postcomp] at h
  rw [option_negation_value, h, evaluate_negation, OptionSyntax.mask_map]
  simp only [Two.comp_unary, Category.comp_id]

theorem implication_pair_good {W : D} (p : W ⟶ P)
    (a b : W ⟶ S.substitutionCarriers.2)
    (ha : PairGood S P d p a) (hb : PairGood S P d p b) :
    PairGood S P d p (prod.lift a b ≫ S.implicationSubstitutionPair) := by
  dsimp only [PairGood, CategoricalSyntax.substitutionCarriers] at ha hb ⊢
  simp only [CategoricalSyntax.implicationSubstitutionPair, Category.assoc,
    prod.lift_fst, prod.lift_snd, prod.lift_map_assoc]
  simp only [option_implication_value]
  rw [ha, hb, evaluate_implication]
  exact (OptionSyntax.mask_binary S.implicationConstructor
    (Two.binaryArrow NullaryBooleanValuation.implies)
    (a ≫ prod.snd) (b ≫ prod.snd)
    (evaluate S P d p (a ≫ prod.fst)) (evaluate S P d p (b ≫ prod.fst))).symm

theorem quantifier_pair_good {W : D} (p : W ⟶ P)
    (q : W ⟶ S.substitutionParameters) (y : W ⟶ V) (a : W ⟶ S.substitutionCarriers.2)
    (ha : PairGood S P d p a) :
    PairGood S P d p (prod.lift q (prod.lift y a) ≫ S.quantifierSubstitutionPair) := by
  dsimp only [PairGood, evaluate] at ha ⊢
  have hq {U : D} (p : U ⟶ P) (v : U ⟶ V) (f : U ⟶ S.algebra.a.2) :
      prod.lift p (prod.lift v f ≫ S.quantifierConstructor) ≫ value S P d =
        prod.lift p f ≫ value S P d := evaluate_quantifier S P d p v f
  simp [CategoricalSyntax.quantifierSubstitutionPair,
    CategoricalSyntax.quantifierSubstitutionResult, CategoricalSyntax.quantifierOriginal,
    branch_natural, ParameterizedOption.map_branch, ParameterizedOption.map_ok,
    ParameterizedOption.map_fail, OptionSyntax.mask_branch, OptionSyntax.mask_ok,
    OptionSyntax.mask_fail, option_quantifier_value, ParameterizedOption.mask_coefficient,
    ← Category.assoc, prod.comp_lift, hq, ha]

end CategoricalEssentialIncompleteness.V46.ParameterizedBooleanValuation
