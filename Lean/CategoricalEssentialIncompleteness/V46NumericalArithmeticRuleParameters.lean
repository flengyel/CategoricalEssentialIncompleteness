/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46NumericalArithmeticSubstitutionDomains

/-! # The actual arithmetic scheme-parameter product and success comparisons -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
namespace CategoricalEssentialIncompleteness.V46.NumericalArithmetic.RuleParameters
open Coordinates SubstitutionParameters SubstitutionDomains NamedArithmeticSignature
local notation "K" => numericalInterpretation
local notation "S" => numericalSyntax
local notation "S₀" => originalSyntax

theorem post_mapped_lift {A B W : PredicateCategory 𝗣𝗔} {Z : NumericalTuples.Object}
    (h : Z ⟶ (K).obj W) (f : W ⟶ A) (g : W ⟶ B) :
    h ≫ (K).map (prod.lift f g) =
      prod.lift (h ≫ (K).map f) (h ≫ (K).map g) ≫ (Geometry.productIso A B).inv := by
  apply (cancel_mono (Geometry.productIso A B).hom).1
  simp only [Category.assoc,Iso.inv_hom_id,Category.comp_id]
  apply prod.hom_ext
  · rw [Category.assoc,Category.assoc,Geometry.product_fst,← (K).map_comp,prod.lift_fst]
    simp
  · rw [Category.assoc,Category.assoc,Geometry.product_snd,← (K).map_comp,prod.lift_snd]
    simp

theorem pairedIso_lift {A B : PredicateCategory 𝗣𝗔} {X Y Z : NumericalTuples.Object}
    (i : X ≅ (K).obj A) (j : Y ≅ (K).obj B) (f : Z ⟶ X) (g : Z ⟶ Y) :
    prod.lift f g ≫ (pairedIso i j).hom =
      prod.lift (f ≫ i.hom) (g ≫ j.hom) ≫ (Geometry.productIso A B).inv := by
  apply (cancel_mono (Geometry.productIso A B).hom).1
  simp only [pairedIso,Iso.trans_hom,Iso.symm_hom,prod.mapIso_hom,Category.assoc,Iso.inv_hom_id,Category.comp_id]
  apply prod.hom_ext <;> simp

@[reassoc] theorem pairedIso_snd_fst
    {A B C : PredicateCategory 𝗣𝗔} {X Y Z : NumericalTuples.Object}
    (i : X ≅ (K).obj A) (j : Y ≅ (K).obj B) (k : Z ≅ (K).obj C) :
    (pairedIso i (pairedIso j k)).hom ≫ (K).map
      ((prod.snd : A ⨯ (B ⨯ C) ⟶ B ⨯ C) ≫ (prod.fst : B ⨯ C ⟶ B)) =
        (prod.snd : X ⨯ (Y ⨯ Z) ⟶ Y ⨯ Z) ≫
          (prod.fst : Y ⨯ Z ⟶ Y) ≫ j.hom := by
  rw [(K).map_comp,← Category.assoc,pairedIso_snd,Category.assoc,pairedIso_fst]

@[reassoc] theorem pairedIso_snd_snd
    {A B C : PredicateCategory 𝗣𝗔} {X Y Z : NumericalTuples.Object}
    (i : X ≅ (K).obj A) (j : Y ≅ (K).obj B) (k : Z ≅ (K).obj C) :
    (pairedIso i (pairedIso j k)).hom ≫ (K).map
      ((prod.snd : A ⨯ (B ⨯ C) ⟶ B ⨯ C) ≫ (prod.snd : B ⨯ C ⟶ C)) =
        (prod.snd : X ⨯ (Y ⨯ Z) ⟶ Y ⨯ Z) ≫
          (prod.snd : Y ⨯ Z ⟶ Z) ≫ k.hom := by
  rw [(K).map_comp,← Category.assoc,pairedIso_snd,Category.assoc,pairedIso_snd]

@[reassoc] theorem pairedIso_fst_fst
    {A B C : PredicateCategory 𝗣𝗔} {X Y Z : NumericalTuples.Object}
    (i : X ≅ (K).obj A) (j : Y ≅ (K).obj B) (k : Z ≅ (K).obj C) :
    (pairedIso (pairedIso i j) k).hom ≫ (K).map
      ((prod.fst : (A ⨯ B) ⨯ C ⟶ A ⨯ B) ≫ (prod.fst : A ⨯ B ⟶ A)) =
        (prod.fst : (X ⨯ Y) ⨯ Z ⟶ X ⨯ Y) ≫
          (prod.fst : X ⨯ Y ⟶ X) ≫ i.hom := by
  rw [(K).map_comp,← Category.assoc,pairedIso_fst,Category.assoc,pairedIso_fst]

@[reassoc] theorem pairedIso_fst_snd
    {A B C : PredicateCategory 𝗣𝗔} {X Y Z : NumericalTuples.Object}
    (i : X ≅ (K).obj A) (j : Y ≅ (K).obj B) (k : Z ≅ (K).obj C) :
    (pairedIso (pairedIso i j) k).hom ≫ (K).map
      ((prod.fst : (A ⨯ B) ⨯ C ⟶ A ⨯ B) ≫ (prod.snd : A ⨯ B ⟶ B)) =
        (prod.fst : (X ⨯ Y) ⨯ Z ⟶ X ⨯ Y) ≫
          (prod.snd : X ⨯ Y ⟶ Y) ≫ j.hom := by
  rw [(K).map_comp,← Category.assoc,pairedIso_fst,Category.assoc,pairedIso_snd]

private theorem comparisonSquare {A B C : PredicateCategory 𝗣𝗔}
    {A' B' C' : NumericalTuples.Object} (f : A ⟶ C) (g : B ⟶ C)
    (f' : A' ⟶ C') (g' : B' ⟶ C')
    (i : A' ≅ (K).obj A) (j : B' ≅ (K).obj B) (k : C' ≅ (K).obj C)
    (hf : f' ≫ k.hom = i.hom ≫ (K).map f) (hg : g' ≫ k.hom = j.hom ≫ (K).map g) :
    IsPullback (pullback.fst f' g' ≫ i.hom) (pullback.snd f' g' ≫ j.hom)
      ((K).map f) ((K).map g) := by
  apply (IsPullback.of_hasPullback f' g').of_iso (Iso.refl _) i j k
  · simp
  · simp
  · exact hf
  · exact hg

def pullbackComparison {A B C : PredicateCategory 𝗣𝗔}
    {A' B' C' : NumericalTuples.Object} (f : A ⟶ C) (g : B ⟶ C)
    (f' : A' ⟶ C') (g' : B' ⟶ C')
    (i : A' ≅ (K).obj A) (j : B' ≅ (K).obj B) (k : C' ≅ (K).obj C)
    (hf : f' ≫ k.hom = i.hom ≫ (K).map f) (hg : g' ≫ k.hom = j.hom ≫ (K).map g) :
    pullback f' g' ≅ (K).obj (pullback f g) :=
  (comparisonSquare f g f' g' i j k hf hg).isoPullback ≪≫ (Geometry.pullbackIso f g).symm

@[reassoc] theorem pullbackComparison_fst {A B C : PredicateCategory 𝗣𝗔}
    {A' B' C' : NumericalTuples.Object} (f : A ⟶ C) (g : B ⟶ C)
    (f' : A' ⟶ C') (g' : B' ⟶ C')
    (i : A' ≅ (K).obj A) (j : B' ≅ (K).obj B) (k : C' ≅ (K).obj C)
    (hf : f' ≫ k.hom = i.hom ≫ (K).map f) (hg : g' ≫ k.hom = j.hom ≫ (K).map g) :
    (pullbackComparison f g f' g' i j k hf hg).hom ≫ (K).map (pullback.fst f g) =
      pullback.fst f' g' ≫ i.hom := by
  have hi : (Geometry.pullbackIso f g).inv ≫ (K).map (pullback.fst f g) = pullback.fst _ _ := by
    rw [← Geometry.pullback_fst,Iso.inv_hom_id_assoc]
  simp only [pullbackComparison,Iso.trans_hom,Iso.symm_hom,Category.assoc,hi]
  exact (comparisonSquare f g f' g' i j k hf hg).isoPullback_hom_fst

@[reassoc] theorem pullbackComparison_snd {A B C : PredicateCategory 𝗣𝗔}
    {A' B' C' : NumericalTuples.Object} (f : A ⟶ C) (g : B ⟶ C)
    (f' : A' ⟶ C') (g' : B' ⟶ C')
    (i : A' ≅ (K).obj A) (j : B' ≅ (K).obj B) (k : C' ≅ (K).obj C)
    (hf : f' ≫ k.hom = i.hom ≫ (K).map f) (hg : g' ≫ k.hom = j.hom ≫ (K).map g) :
    (pullbackComparison f g f' g' i j k hf hg).hom ≫ (K).map (pullback.snd f g) =
      pullback.snd f' g' ≫ j.hom := by
  have hi : (Geometry.pullbackIso f g).inv ≫ (K).map (pullback.snd f g) = pullback.snd _ _ := by
    rw [← Geometry.pullback_snd,Iso.inv_hom_id_assoc]
  simp only [pullbackComparison,Iso.trans_hom,Iso.symm_hom,Category.assoc,hi]
  exact (comparisonSquare f g f' g' i j k hf hg).isoPullback_hom_snd

def formulaPairIso : (S).algebra.a.2 ⨯ (S).algebra.a.2 ≅
    (K).obj ((S₀).algebra.a.2 ⨯ (S₀).algebra.a.2) := pairedIso formulaIso formulaIso
def formulaTripleIso : ((S).algebra.a.2 ⨯ (S).algebra.a.2) ⨯ (S).algebra.a.2 ≅
    (K).obj (((S₀).algebra.a.2 ⨯ (S₀).algebra.a.2) ⨯ (S₀).algebra.a.2) :=
  pairedIso formulaPairIso formulaIso
def instantiationBaseIso : NumericalNamed.variableObject ⨯ ((S).algebra.a.2 ⨯ (S).algebra.a.1) ≅
    (K).obj (variableSymbols ⨯ ((S₀).algebra.a.2 ⨯ (S₀).algebra.a.1)) :=
  pairedIso variableIso (pairedIso formulaIso termIso)
def distributionBaseIso : NumericalNamed.variableObject ⨯ ((S).algebra.a.2 ⨯ (S).algebra.a.2) ≅
    (K).obj (variableSymbols ⨯ ((S₀).algebra.a.2 ⨯ (S₀).algebra.a.2)) :=
  pairedIso variableIso formulaPairIso
def equalityBaseIso : (S).equalitySchemeBase ≅ (K).obj (S₀).equalitySchemeBase :=
  pairedIso (pairedIso variableIso formulaIso) (pairedIso termIso termIso)

@[reassoc] theorem instantiation_name : instantiationBaseIso.hom ≫
    (K).map (prod.fst : @Quiver.Hom (PredicateCategory 𝗣𝗔) inferInstance
      (Limits.prod (C := PredicateCategory 𝗣𝗔) variableSymbols (Limits.prod (C := PredicateCategory 𝗣𝗔) (S₀).algebra.a.2 (S₀).algebra.a.1)) variableSymbols) =
      prod.fst ≫ variableIso.hom := pairedIso_fst variableIso (pairedIso formulaIso termIso)

@[reassoc] theorem instantiation_formula : instantiationBaseIso.hom ≫
    (K).map ((prod.snd : @Quiver.Hom (PredicateCategory 𝗣𝗔) inferInstance
      (Limits.prod (C := PredicateCategory 𝗣𝗔) variableSymbols (Limits.prod (C := PredicateCategory 𝗣𝗔) (S₀).algebra.a.2 (S₀).algebra.a.1)) (Limits.prod (C := PredicateCategory 𝗣𝗔) (S₀).algebra.a.2 (S₀).algebra.a.1)) ≫ prod.fst) =
      prod.snd ≫ prod.fst ≫ formulaIso.hom := by
  exact pairedIso_snd_fst variableIso formulaIso termIso

@[reassoc] theorem instantiation_term : instantiationBaseIso.hom ≫
    (K).map ((prod.snd : @Quiver.Hom (PredicateCategory 𝗣𝗔) inferInstance
      (Limits.prod (C := PredicateCategory 𝗣𝗔) variableSymbols (Limits.prod (C := PredicateCategory 𝗣𝗔) (S₀).algebra.a.2 (S₀).algebra.a.1)) (Limits.prod (C := PredicateCategory 𝗣𝗔) (S₀).algebra.a.2 (S₀).algebra.a.1)) ≫ prod.snd) =
      prod.snd ≫ prod.snd ≫ termIso.hom := by
  exact pairedIso_snd_snd variableIso formulaIso termIso

theorem instantiation_input : (S).instantiationInput ≫ formulaInputIso.hom =
    instantiationBaseIso.hom ≫ (K).map (S₀).instantiationInput := by
  simp only [CategoricalSyntax.instantiationInput,formulaInputIso,pairedIso_lift,
    post_mapped_lift,instantiation_formula,instantiation_name,instantiation_term,
    parameterIso,pairedIso_lift,Category.assoc]

/-- The quantifier-instantiation labels are compared by their actual
admissibility pullback, retaining the name, formula and replacement. -/
def instantiationIso : (S).instantiationParameters ≅ (K).obj (S₀).instantiationParameters :=
  pullbackComparison (S₀).instantiationInput (S₀).admissibleInclusion
    (S).instantiationInput (S).admissibleInclusion instantiationBaseIso admissibleIso formulaInputIso
    instantiation_input forward_inclusion.symm

@[reassoc] theorem instantiation_inclusion : instantiationIso.hom ≫ (K).map (S₀).instantiationInclusion =
    (S).instantiationInclusion ≫ instantiationBaseIso.hom :=
  pullbackComparison_fst _ _ _ _ _ _ _ _ _

@[reassoc] theorem instantiation_admissible : instantiationIso.hom ≫ (K).map (S₀).instantiationAdmissible =
    (S).instantiationAdmissible ≫ admissibleIso.hom :=
  pullbackComparison_snd _ _ _ _ _ _ _ _ _

end CategoricalEssentialIncompleteness.V46.NumericalArithmetic.RuleParameters
