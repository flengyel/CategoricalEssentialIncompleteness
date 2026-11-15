/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ParameterizedBooleanSubstitutionSteps
public import CategoricalEssentialIncompleteness.V46ParameterizedSubstitutionAlgebra

/-! # The substitution equalizer with both internal parameters retained -/

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
variable {R : D} (s : R ⟶ P) (r : R ⟶ S.substitutionParameters)

def invariantTarget (R : D) : Over R × Over R :=
  (constantFamily R (⊤_ D), constantFamily R (OptionSyntax.obj (Two D)))

def invariantMask : (ParameterizedSubstitution.algebra S r).a ⟶ invariantTarget (D := D) R :=
  ((constantFamilyFunctor R).map (terminal.from _),
    parameterHom (OptionSyntax.mask
      (evaluate S P d (prod.fst ≫ s) (prod.snd ≫ prod.fst)) (prod.snd ≫ prod.snd)))

def invariantResult : (ParameterizedSubstitution.algebra S r).a ⟶ invariantTarget (D := D) R :=
  ((constantFamilyFunctor R).map (terminal.from _),
    parameterHom (ParameterizedOption.map (value S P d) (prod.fst ≫ s) (prod.snd ≫ prod.snd)))

theorem invariant_equation {A : Over R}
    (m : A ⟶ (ParameterizedSubstitution.algebra S r).a.2) :
    m ≫ (invariantResult S P d s r).2 = m ≫ (invariantMask S P d s r).2 ↔
      PairGood S P d (A.hom ≫ s) (m.left ≫ prod.snd) := by
  have he (f g : A ⟶ constantFamily R (OptionSyntax.obj (Two D))) :
      f = g ↔ f.left ≫ prod.snd = g.left ≫ prod.snd :=
    ⟨fun h => congrArg (fun k => k.left ≫ prod.snd) h, constantFamily_hom_ext⟩
  have hp : m.left ≫ prod.fst = A.hom := Over.w m
  have hs : m.left ≫ prod.fst ≫ s = A.hom ≫ s := by rw [← Category.assoc, hp]
  rw [he]
  simp only [invariantMask, invariantResult, PairGood, Over.comp_left,
    parameterHom, Over.homMk_left, Category.assoc, prod.lift_snd,
    ParameterizedOption.map_precomp, OptionSyntax.mask_precomp,
    evaluate_precomp, hs]

theorem invariant_precomp {A B : Over R × Over R}
    (m : A ⟶ (ParameterizedSubstitution.algebra S r).a)
    (hm : m ≫ invariantResult S P d s r = m ≫ invariantMask S P d s r)
    (i : B.2 ⟶ A.2) :
    PairGood S P d (B.2.hom ≫ s) ((i ≫ m.2).left ≫ prod.snd) := by
  apply (invariant_equation S P d s r (i ≫ m.2)).mp
  have h := congrArg Prod.snd hm
  simpa only [Category.assoc, prod_comp] using congrArg (fun k => i ≫ k) h

theorem equality_closed {A : Over R × Over R}
    (m : A ⟶ (ParameterizedSubstitution.algebra S r).a) :
    (prod.map m.1 m.1 ≫ constantProductComparison R
      S.substitutionCarriers.1 S.substitutionCarriers.1 ≫
        (constantFamilyFunctor R).map S.equalitySubstitutionPair) ≫
          (invariantResult S P d s r).2 =
      (prod.map m.1 m.1 ≫ constantProductComparison R
        S.substitutionCarriers.1 S.substitutionCarriers.1 ≫
          (constantFamilyFunctor R).map S.equalitySubstitutionPair) ≫
            (invariantMask S P d s r).2 := by
  apply (invariant_equation S P d s r _).mpr
  rw [CategoricalSyntax.absence_product_step_value]
  exact equality_pair_good S P d _ _ _

theorem relation_closed {A : Over R × Over R}
    (m : A ⟶ (ParameterizedSubstitution.algebra S r).a) :
    (((SyntaxPolynomial.constructors (fun _ => X) 0).withParameters R).eval.map m ≫
      (SyntaxPolynomial.parameterComparison R S.substitutionCarriers
        (SyntaxPolynomial.constructors (fun _ => X) 0) ≫
          (constantFamilyFunctor R).map S.relationSubstitutionPair)) ≫
            (invariantResult S P d s r).2 =
      (((SyntaxPolynomial.constructors (fun _ => X) 0).withParameters R).eval.map m ≫
        (SyntaxPolynomial.parameterComparison R S.substitutionCarriers
          (SyntaxPolynomial.constructors (fun _ => X) 0) ≫
            (constantFamilyFunctor R).map S.relationSubstitutionPair)) ≫
              (invariantMask S P d s r).2 := by
  apply (invariant_equation S P d s r _).mpr
  let k := ((SyntaxPolynomial.constructors (fun _ => X) 0).withParameters R).eval.map m ≫
    SyntaxPolynomial.parameterComparison R S.substitutionCarriers
      (SyntaxPolynomial.constructors (fun _ => X) 0)
  simpa only [Over.comp_left, constantFamilyFunctor, Over.homMk_left,
    Category.assoc, prod.map_snd, k] using
      relation_pair_good S P d _ (k.left ≫ prod.snd)

theorem negation_closed {A : Over R × Over R}
    (m : A ⟶ (ParameterizedSubstitution.algebra S r).a)
    (hm : m ≫ invariantResult S P d s r = m ≫ invariantMask S P d s r) :
    (m.2 ≫ (constantFamilyFunctor R).map S.negationSubstitutionPair) ≫
        (invariantResult S P d s r).2 =
      (m.2 ≫ (constantFamilyFunctor R).map S.negationSubstitutionPair) ≫
        (invariantMask S P d s r).2 := by
  apply (invariant_equation S P d s r _).mpr
  simpa only [Over.comp_left, constantFamilyFunctor, Over.homMk_left,
    Category.assoc, prod.map_snd] using
      negation_pair_good S P d _ (m.2.left ≫ prod.snd)
        ((invariant_equation S P d s r m.2).mp (congrArg Prod.snd hm))

theorem implication_closed {A : Over R × Over R}
    (m : A ⟶ (ParameterizedSubstitution.algebra S r).a)
    (hm : m ≫ invariantResult S P d s r = m ≫ invariantMask S P d s r) :
    (prod.map m.2 m.2 ≫ constantProductComparison R
      S.substitutionCarriers.2 S.substitutionCarriers.2 ≫
        (constantFamilyFunctor R).map S.implicationSubstitutionPair) ≫
          (invariantResult S P d s r).2 =
      (prod.map m.2 m.2 ≫ constantProductComparison R
        S.substitutionCarriers.2 S.substitutionCarriers.2 ≫
          (constantFamilyFunctor R).map S.implicationSubstitutionPair) ≫
            (invariantMask S P d s r).2 := by
  apply (invariant_equation S P d s r _).mpr
  rw [CategoricalSyntax.absence_product_step_value]
  exact implication_pair_good S P d _ _ _
    (invariant_precomp S P d s r (B := (A.1, A.2 ⨯ A.2)) m hm prod.fst)
    (invariant_precomp S P d s r (B := (A.1, A.2 ⨯ A.2)) m hm prod.snd)

theorem quantifier_closed {A : Over R × Over R}
    (m : A ⟶ (ParameterizedSubstitution.algebra S r).a)
    (hm : m ≫ invariantResult S P d s r = m ≫ invariantMask S P d s r) :
    (prod.map (𝟙 (constantFamily R V)) m.2 ≫
      constantProductComparison R V S.substitutionCarriers.2 ≫
        parameterHom (prod.map r (𝟙 _) ≫ S.quantifierSubstitutionPair)) ≫
          (invariantResult S P d s r).2 =
      (prod.map (𝟙 (constantFamily R V)) m.2 ≫
        constantProductComparison R V S.substitutionCarriers.2 ≫
          parameterHom (prod.map r (𝟙 _) ≫ S.quantifierSubstitutionPair)) ≫
            (invariantMask S P d s r).2 := by
  apply (invariant_equation S P d s r _).mpr
  rw [CategoricalSyntax.absence_parameter_step_value]
  simpa only [prod.lift_map_assoc, Category.comp_id] using
    quantifier_pair_good S P d
      (((constantFamily R V) ⨯ A.2).hom ≫ s)
      (((constantFamily R V) ⨯ A.2).hom ≫ r)
      ((prod.fst : constantFamily R V ⨯ A.2 ⟶ _).left ≫ prod.snd)
      ((prod.snd ≫ m.2).left ≫ prod.snd)
      (invariant_precomp S P d s r
        (B := (A.1, constantFamily R V ⨯ A.2)) m hm prod.snd)

end CategoricalEssentialIncompleteness.V46.ParameterizedBooleanValuation
