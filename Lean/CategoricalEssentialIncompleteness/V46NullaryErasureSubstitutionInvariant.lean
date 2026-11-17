/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NullaryErasureSubstitutionSteps

/-! # The erasure equalizer for substitution -/

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

def invariantTarget : Over S.substitutionParameters × Over S.substitutionParameters :=
  (constantFamily S.substitutionParameters (⊤_ D),
    constantFamily S.substitutionParameters (OptionSyntax.obj (Y)))

def invariantMask : S.substitutionAlgebra.a ⟶ invariantTarget (Y := Y) S :=
  ((constantFamilyFunctor S.substitutionParameters).map (terminal.from _),
    parameterHom (OptionSyntax.mask (prod.snd ≫ prod.fst ≫ erase S d neg imp truth)
      (prod.snd ≫ prod.snd)))

def invariantResult : S.substitutionAlgebra.a ⟶ invariantTarget (Y := Y) S :=
  ((constantFamilyFunctor S.substitutionParameters).map (terminal.from _),
    (constantFamilyFunctor S.substitutionParameters).map
      (prod.snd ≫ OptionSyntax.map (erase S d neg imp truth)))

theorem invariant_equation {A : Over S.substitutionParameters}
    (m : A ⟶ S.substitutionAlgebra.a.2) :
    m ≫ (invariantMask S d neg imp truth).2 = m ≫ (invariantResult S d neg imp truth).2 ↔
      PairGood S d neg imp truth (m.left ≫ prod.snd) := by
  have he (f g : A ⟶ constantFamily S.substitutionParameters (OptionSyntax.obj (Y))) :
      f = g ↔ f.left ≫ prod.snd = g.left ≫ prod.snd :=
    ⟨fun h => congrArg (fun k => k.left ≫ prod.snd) h, constantFamily_hom_ext⟩
  rw [he]
  simp only [invariantMask, invariantResult, Over.comp_left, parameterHom,
    Over.homMk_left, constantFamilyFunctor, Category.assoc, prod.lift_snd,
    prod.map_snd, OptionSyntax.mask_precomp, PairGood]
  exact eq_comm

theorem invariant_precomp {A B : Over S.substitutionParameters × Over S.substitutionParameters}
    (m : A ⟶ S.substitutionAlgebra.a)
    (hm : m ≫ invariantMask S d neg imp truth = m ≫ invariantResult S d neg imp truth) (i : B.2 ⟶
      A.2) :
    PairGood S d neg imp truth ((i ≫ m.2).left ≫ prod.snd) := by
  apply (invariant_equation S d neg imp truth (i ≫ m.2)).mp
  have hh : m.2 ≫ (invariantMask S d neg imp truth).2 = m.2 ≫ (invariantResult S d neg imp
    truth).2 :=
    congrArg Prod.snd hm
  simpa only [Category.assoc] using
    congrArg (fun h => i ≫ h) hh

theorem equality_closed {A : Over S.substitutionParameters × Over S.substitutionParameters}
    (m : A ⟶ S.substitutionAlgebra.a) :
    (prod.map m.1 m.1 ≫ constantProductComparison S.substitutionParameters
      S.substitutionCarriers.1 S.substitutionCarriers.1 ≫
        (constantFamilyFunctor S.substitutionParameters).map S.equalitySubstitutionPair) ≫
          (invariantMask S d neg imp truth).2 =
      (prod.map m.1 m.1 ≫ constantProductComparison S.substitutionParameters
        S.substitutionCarriers.1 S.substitutionCarriers.1 ≫
          (constantFamilyFunctor S.substitutionParameters).map S.equalitySubstitutionPair) ≫
            (invariantResult S d neg imp truth).2 := by
  apply (invariant_equation S d neg imp truth _).mpr
  rw [CategoricalSyntax.absence_product_step_value]
  exact equality_pair_good S d neg imp truth _ _

theorem relation_closed {A : Over S.substitutionParameters × Over S.substitutionParameters}
    (m : A ⟶ S.substitutionAlgebra.a) :
    (((SyntaxPolynomial.constructors (fun _ => X) 0).withParameters
        S.substitutionParameters).eval.map m ≫
      (SyntaxPolynomial.parameterComparison S.substitutionParameters S.substitutionCarriers
        (SyntaxPolynomial.constructors (fun _ => X) 0) ≫
        (constantFamilyFunctor S.substitutionParameters).map S.relationSubstitutionPair)) ≫
          (invariantMask S d neg imp truth).2 =
      (((SyntaxPolynomial.constructors (fun _ => X) 0).withParameters
          S.substitutionParameters).eval.map m ≫
        (SyntaxPolynomial.parameterComparison S.substitutionParameters S.substitutionCarriers
          (SyntaxPolynomial.constructors (fun _ => X) 0) ≫
          (constantFamilyFunctor S.substitutionParameters).map S.relationSubstitutionPair)) ≫
            (invariantResult S d neg imp truth).2 := by
  apply (invariant_equation S d neg imp truth _).mpr
  let k := ((SyntaxPolynomial.constructors (fun _ => X) 0).withParameters
      S.substitutionParameters).eval.map m ≫
    SyntaxPolynomial.parameterComparison S.substitutionParameters S.substitutionCarriers
      (SyntaxPolynomial.constructors (fun _ => X) 0)
  simpa only [Over.comp_left, constantFamilyFunctor, Over.homMk_left,
    Category.assoc, prod.map_snd, k] using relation_pair_good S d neg imp truth (k.left ≫ prod.snd)

theorem negation_closed {A : Over S.substitutionParameters × Over S.substitutionParameters}
    (m : A ⟶ S.substitutionAlgebra.a)
    (hm : m ≫ invariantMask S d neg imp truth = m ≫ invariantResult S d neg imp truth) :
    (m.2 ≫ (constantFamilyFunctor S.substitutionParameters).map S.negationSubstitutionPair) ≫
        (invariantMask S d neg imp truth).2 =
      (m.2 ≫ (constantFamilyFunctor S.substitutionParameters).map S.negationSubstitutionPair) ≫
        (invariantResult S d neg imp truth).2 := by
  apply (invariant_equation S d neg imp truth _).mpr
  simpa only [Over.comp_left, constantFamilyFunctor, Over.homMk_left,
    Category.assoc, prod.map_snd] using negation_pair_good S d neg imp truth (m.2.left ≫ prod.snd)
      ((invariant_equation S d neg imp truth m.2).mp (congrArg Prod.snd hm))

theorem implication_closed {A : Over S.substitutionParameters × Over S.substitutionParameters}
    (m : A ⟶ S.substitutionAlgebra.a)
    (hm : m ≫ invariantMask S d neg imp truth = m ≫ invariantResult S d neg imp truth) :
    (prod.map m.2 m.2 ≫ constantProductComparison S.substitutionParameters
      S.substitutionCarriers.2 S.substitutionCarriers.2 ≫
        (constantFamilyFunctor S.substitutionParameters).map S.implicationSubstitutionPair) ≫
          (invariantMask S d neg imp truth).2 =
      (prod.map m.2 m.2 ≫ constantProductComparison S.substitutionParameters
        S.substitutionCarriers.2 S.substitutionCarriers.2 ≫
          (constantFamilyFunctor S.substitutionParameters).map S.implicationSubstitutionPair) ≫
            (invariantResult S d neg imp truth).2 := by
  apply (invariant_equation S d neg imp truth _).mpr
  rw [CategoricalSyntax.absence_product_step_value]
  exact implication_pair_good S d neg imp truth _ _
    (invariant_precomp S d neg imp truth (B := (A.1, A.2 ⨯ A.2)) m hm prod.fst)
    (invariant_precomp S d neg imp truth (B := (A.1, A.2 ⨯ A.2)) m hm prod.snd)

theorem quantifier_closed {A : Over S.substitutionParameters × Over S.substitutionParameters}
    (m : A ⟶ S.substitutionAlgebra.a)
    (hm : m ≫ invariantMask S d neg imp truth = m ≫ invariantResult S d neg imp truth) :
    (prod.map (𝟙 (constantFamily S.substitutionParameters V)) m.2 ≫
      constantProductComparison S.substitutionParameters V S.substitutionCarriers.2 ≫
        parameterHom S.quantifierSubstitutionPair) ≫ (invariantMask S d neg imp truth).2 =
      (prod.map (𝟙 (constantFamily S.substitutionParameters V)) m.2 ≫
        constantProductComparison S.substitutionParameters V S.substitutionCarriers.2 ≫
          parameterHom S.quantifierSubstitutionPair) ≫ (invariantResult S d neg imp truth).2 := by
  apply (invariant_equation S d neg imp truth _).mpr
  rw [CategoricalSyntax.absence_parameter_step_value]
  simpa only [Category.comp_id] using quantifier_pair_good S d neg imp truth
    ((constantFamily S.substitutionParameters V) ⨯ A.2).hom
    ((prod.fst : constantFamily S.substitutionParameters V ⨯ A.2 ⟶ _).left ≫ prod.snd)
    ((prod.snd ≫ m.2).left ≫ prod.snd)
    (invariant_precomp S d neg imp truth
      (B := (A.1, constantFamily S.substitutionParameters V ⨯ A.2)) m hm prod.snd)

end CategoricalEssentialIncompleteness.V46.NullaryPropositionalErasure
