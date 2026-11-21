/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NumericalArithmeticRules
public import CategoricalEssentialIncompleteness.V46NumericalArithmeticSchemeSquares

/-! # The seven-scheme and Gamma nullary label isomorphism -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
namespace CategoricalEssentialIncompleteness.V46.NumericalArithmetic.NullaryRules
open Coordinates SubstitutionParameters SubstitutionDomains RuleParameters EqualityParameters NamedArithmeticSignature
local notation "K" => numericalInterpretation
local notation "S" => numericalSyntax
local notation "S₀" => originalSyntax
abbrev formulaObject := numericalSyntax.algebra.a.2
abbrev originalFormulaObject := originalSyntax.algebra.a.2
local notation "Y" => formulaObject
local notation "Y₀" => originalFormulaObject

def copairedIso {A B : PredicateCategory 𝗣𝗔} {X Z : NumericalTuples.Object}
    (i : X ≅ (K).obj A) (j : Z ≅ (K).obj B) : X ⨿ Z ≅ (K).obj (A ⨿ B) :=
  coprod.mapIso i j ≪≫ (Geometry.coproductIso A B).symm

private theorem coproduct_inv_inl (A B : PredicateCategory 𝗣𝗔) :
    (coprod.inl : (K).obj A ⟶ (K).obj A ⨿ (K).obj B) ≫ (Geometry.coproductIso A B).inv =
      (K).map (coprod.inl : A ⟶ A ⨿ B) := by
  apply (cancel_mono (Geometry.coproductIso A B).hom).1
  rw [Category.assoc,Iso.inv_hom_id,Category.comp_id,Geometry.coproduct_inl]

private theorem coproduct_inv_inr (A B : PredicateCategory 𝗣𝗔) :
    (coprod.inr : (K).obj B ⟶ (K).obj A ⨿ (K).obj B) ≫ (Geometry.coproductIso A B).inv =
      (K).map (coprod.inr : B ⟶ A ⨿ B) := by
  apply (cancel_mono (Geometry.coproductIso A B).hom).1
  rw [Category.assoc,Iso.inv_hom_id,Category.comp_id,Geometry.coproduct_inr]

@[reassoc] theorem copairedIso_inl {A B : PredicateCategory 𝗣𝗔} {X Z : NumericalTuples.Object}
    (i : X ≅ (K).obj A) (j : Z ≅ (K).obj B) :
    coprod.inl ≫ (copairedIso i j).hom = i.hom ≫ (K).map (coprod.inl : A ⟶ A ⨿ B) := by
  simp only [copairedIso,Iso.trans_hom,Iso.symm_hom,coprod.mapIso_hom]
  rw [← Category.assoc,coprod.inl_map,Category.assoc,coproduct_inv_inl]

@[reassoc] theorem copairedIso_inr {A B : PredicateCategory 𝗣𝗔} {X Z : NumericalTuples.Object}
    (i : X ≅ (K).obj A) (j : Z ≅ (K).obj B) :
    coprod.inr ≫ (copairedIso i j).hom = j.hom ≫ (K).map (coprod.inr : B ⟶ A ⨿ B) := by
  simp only [copairedIso,Iso.trans_hom,Iso.symm_hom,coprod.mapIso_hom]
  rw [← Category.assoc,coprod.inr_map,Category.assoc,coproduct_inv_inr]

private theorem factor_right {A B C D : NumericalTuples.Object}
    {u : A ⟶ D} {f : A ⟶ B} {g : B ⟶ C} {h : C ⟶ D}
    (p : u = f ≫ g ≫ h) : u = (f ≫ g) ≫ h :=
  p.trans (Category.assoc f g h).symm

private theorem copaired_square {A B : PredicateCategory 𝗣𝗔} {X Z : NumericalTuples.Object}
    (i : X ≅ (K).obj A) (j : Z ≅ (K).obj B)
    (f : A ⟶ Y₀) (g : B ⟶ Y₀) (f' : X ⟶ Y) (g' : Z ⟶ Y)
    (hf : i.hom ≫ (K).map f = f' ≫ formulaIso.hom)
    (hg : j.hom ≫ (K).map g = g' ≫ formulaIso.hom) :
    (copairedIso i j).hom ≫ (K).map (coprod.desc f g) =
      coprod.desc f' g' ≫ formulaIso.hom := by
  apply coprod.hom_ext
  · calc
      _ = (coprod.inl ≫ (copairedIso i j).hom) ≫ (K).map (coprod.desc f g) := (Category.assoc _ _ _).symm
      _ = (i.hom ≫ (K).map (coprod.inl : A ⟶ A ⨿ B)) ≫ (K).map (coprod.desc f g) :=
        congrArg (fun z => z ≫ (K).map (coprod.desc f g)) (copairedIso_inl i j)
      _ = i.hom ≫ (K).map f := by rw [Category.assoc,← (K).map_comp,coprod.inl_desc]
      _ = f' ≫ formulaIso.hom := hf
      _ = _ := by simp only [coprod.inl_desc_assoc]
  · calc
      _ = (coprod.inr ≫ (copairedIso i j).hom) ≫ (K).map (coprod.desc f g) := (Category.assoc _ _ _).symm
      _ = (j.hom ≫ (K).map (coprod.inr : B ⟶ A ⨿ B)) ≫ (K).map (coprod.desc f g) :=
        congrArg (fun z => z ≫ (K).map (coprod.desc f g)) (copairedIso_inr i j)
      _ = j.hom ≫ (K).map g := by rw [Category.assoc,← (K).map_comp,coprod.inr_desc]
      _ = g' ≫ formulaIso.hom := hg
      _ = _ := by simp only [coprod.inr_desc_assoc]

/-- Every summand is the scheme parameter object. In particular, Q1 and equality retain
their success pullbacks and Q2 its false fiber. -/
def logicalIso : (S).logicalParameters ≅ (K).obj (S₀).logicalParameters :=
  copairedIso (copairedIso (copairedIso (copairedIso
    (copairedIso (copairedIso formulaPairIso formulaTripleIso) formulaPairIso)
      instantiationIso) DistributionParameters.iso) termIso) equalityIso

theorem logical_square : logicalIso.hom ≫ (K).map (S₀).logicalAxioms =
    (S).logicalAxioms ≫ formulaIso.hom := by
  have h₁₂ := copaired_square formulaPairIso formulaTripleIso _ _ _ _
    SchemeSquares.hilbertOne SchemeSquares.hilbertTwo
  have h₁₂₃ := copaired_square (copairedIso formulaPairIso formulaTripleIso) formulaPairIso _ _ _ _
    h₁₂ SchemeSquares.hilbertThree
  have h₁₂₃₄ := copaired_square (copairedIso (copairedIso formulaPairIso formulaTripleIso) formulaPairIso)
    instantiationIso _ _ _ _ h₁₂₃ SchemeSquares.hilbertInstantiation
  have h₁₂₃₄₅ := copaired_square
    (copairedIso (copairedIso (copairedIso formulaPairIso formulaTripleIso) formulaPairIso) instantiationIso)
    DistributionParameters.iso _ _ _ _ h₁₂₃₄ SchemeSquares.hilbertDistribution
  have h₁₂₃₄₅₆ := copaired_square
    (copairedIso (copairedIso (copairedIso (copairedIso formulaPairIso formulaTripleIso) formulaPairIso)
      instantiationIso) DistributionParameters.iso) termIso _ _ _ _ h₁₂₃₄₅ SchemeSquares.hilbertReflexivity
  exact copaired_square
    (copairedIso (copairedIso (copairedIso (copairedIso (copairedIso formulaPairIso formulaTripleIso)
      formulaPairIso) instantiationIso) DistributionParameters.iso) termIso) equalityIso _ _ _ _
      h₁₂₃₄₅₆ SchemeSquares.hilbertEquality

/-- The Gamma leaf branch is the PA sentence axiom object, with the identity label map;
only the seven logical branches are relabelled. -/
def rho0 (Γ : Carrier) : (Rules.rules Γ).instances 0 ≅ (K).obj ((Rules.originalRules Γ).instances 0) :=
  copairedIso (A := (S₀).logicalParameters) (B := ArithmeticLiteralModel.axiomObject Γ)
    logicalIso (Iso.refl (Rules.axiomObject Γ))

theorem rho0_rule_conclusion (Γ : Carrier) :
    (rho0 Γ).hom ≫ (K).map ((Rules.originalRules Γ).conclusion 0) =
      (Rules.rules Γ).conclusion 0 ≫ formulaIso.hom := by
  exact copaired_square logicalIso (Iso.refl (Rules.axiomObject Γ)) _ _ _ _
    logical_square (by simpa only [Iso.refl_hom,Category.id_comp] using factor_right (Rules.axioms_formula Γ).symm)

theorem rho0_rule_premises (Γ : Carrier) :
    (rho0 Γ).hom ≫ (K).map ((Rules.originalRules Γ).premises 0) ≫
      (NumericalDerivationInterpretation.finitePowerIso (S₀).algebra.a.2 0).hom =
      (Rules.rules Γ).premises 0 ≫ finitePowerMap formulaIso.hom 0 :=
  terminal.hom_ext _ _

end CategoricalEssentialIncompleteness.V46.NumericalArithmetic.NullaryRules
