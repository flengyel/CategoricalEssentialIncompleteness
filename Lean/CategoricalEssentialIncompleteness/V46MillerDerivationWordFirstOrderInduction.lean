/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerDerivationWordInduction
public import CategoricalEssentialIncompleteness.V46FirstOrderInference
public import Mathlib.Tactic.FinCases

/-! # First-order conclusion induction with arbitrary uniform axioms

This specializes the proved word-rank induction to the printed nullary,
unary and ordered binary premise pullbacks. It makes no enumeration or
decidability assumption on the external induction property.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.RestrictionCategory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness.V46.Miller.Derivation.WordInduction
open SyntacticDerivation
variable {P : Uniform.Family}
local notation "U" => (Total.underlying (P := P))

theorem coprod_cases (X Y : Total.TotalCategory P) (z : (U).obj (X ⨿ Y)) :
    (∃ x : (U).obj X,(U).map (coprod.inl : X ⟶ X ⨿ Y) x=z) ∨
      (∃ y : (U).obj Y,(U).map (coprod.inr : Y ⟶ X ⨿ Y) y=z) := by
  have h := isColimitOfHasBinaryCoproductOfPreservesColimit (U) X Y
  have hc := (Types.binaryCofan_isColimit_iff _).mp ⟨h⟩
  exact (Set.eq_univ_iff_forall.mp hc.2.2.sup_eq_top) z

theorem copair_predicate {X Y Z : Total.TotalCategory P} (f : X ⟶ Z) (g : Y ⟶ Z)
    (H : (U).obj Z → Prop) (hf : ∀ x,H ((U).map f x)) (hg : ∀ y,H ((U).map g y))
    (z : (U).obj (X ⨿ Y)) : H ((U).map (coprod.desc f g) z) := by
  rcases coprod_cases X Y z with ⟨x,rfl⟩ | ⟨y,rfl⟩
  · rw [← CategoryTheory.Functor.map_comp_apply,coprod.inl_desc]
    exact hf x
  · rw [← CategoryTheory.Functor.map_comp_apply,coprod.inr_desc]
    exact hg y

@[simp] theorem finiteChild_one (X : Total.TotalCategory P) (k : Fin 1) : finiteChild X 1 k=𝟙 X := by
  simp only [finiteChild,PolynomialComparison.powerIso,powerProjection,Iso.refl_hom,Category.id_comp]

@[simp] theorem finiteChild_two_zero (X : Total.TotalCategory P) :
    finiteChild X 2 0=(prod.fst : X ⨯ X ⟶ X) := by
  change finiteChild X 2 (Fin.castSucc (0 : Fin 1))=(prod.fst : X ⨯ X ⟶ X)
  simp only [finiteChild,PolynomialComparison.powerIso,prod.mapIso_hom,Iso.refl_hom,
    prod.map_id_id,powerProjection,Fin.lastCases_castSucc]
  change (𝟙 (X ⨯ X))≫(prod.fst : X ⨯ X ⟶ X)≫𝟙 X=prod.fst
  rw [Category.id_comp,Category.comp_id]

@[simp] theorem finiteChild_two_one (X : Total.TotalCategory P) :
    finiteChild X 2 1=(prod.snd : X ⨯ X ⟶ X) := by
  change finiteChild X 2 (Fin.last 1)=(prod.snd : X ⨯ X ⟶ X)
  simp only [finiteChild,PolynomialComparison.powerIso,prod.mapIso_hom,Iso.refl_hom,
    prod.map_id_id,powerProjection,Fin.lastCases_last]
  change (𝟙 (X ⨯ X))≫(prod.snd : X ⨯ X ⟶ X)=prod.snd
  exact Category.id_comp _

variable {V F L Sent A : Total.TotalCategory P}
variable (logical : L ⟶ F) (sentence : Sent ⟶ F) (axioms : A ⟶ Sent)
variable (all : V ⨯ F ⟶ F) (imp : F ⨯ F ⟶ F)

theorem firstOrder_conclusion_induction (H : (U).obj F → Prop)
    (hlogical : ∀ l : (U).obj L,H ((U).map logical l))
    (haxioms : ∀ a : (U).obj A,H ((U).map (axioms ≫ sentence) a))
    (hgen : ∀ z : (U).obj (V ⨯ F),H ((U).map prod.snd z) → H ((U).map all z))
    (hmp : ∀ z : (U).obj (F ⨯ F),H ((U).map prod.fst z) →
      H ((U).map imp z) → H ((U).map prod.snd z)) :
    ∀ d : (U).obj (wordAlgebra (firstOrderRules logical sentence axioms all imp)).a.left,
      H ((U).map (wordConclusion (firstOrderRules logical sentence axioms all imp)) d) := by
  let R := firstOrderRules logical sentence axioms all imp
  apply conclusion_induction R H
  intro i r ih
  fin_cases i
  · change H ((U).map (pullback.fst _ _ ≫ coprod.desc logical (axioms ≫ sentence)) r)
    rw [CategoryTheory.Functor.map_comp_apply]
    exact copair_predicate logical (axioms ≫ sentence) H hlogical haxioms _
  · change H ((U).map (pullback.fst _ _ ≫ all) r)
    rw [CategoryTheory.Functor.map_comp_apply]
    apply hgen
    have h := ih (0 : Fin 1)
    change H ((U).map (pullback.fst _ _ ≫ prod.snd ≫ finiteChild F 1 0) r) at h
    erw [finiteChild_one,Category.comp_id,CategoryTheory.Functor.map_comp_apply] at h
    exact h
  · change H ((U).map (pullback.fst _ _ ≫ prod.snd) r)
    rw [CategoryTheory.Functor.map_comp_apply]
    apply hmp
    · have h := ih (0 : Fin 2)
      change H ((U).map (pullback.fst _ _ ≫ prod.lift prod.fst imp ≫ finiteChild F 2 0) r) at h
      erw [finiteChild_two_zero,prod.lift_fst,CategoryTheory.Functor.map_comp_apply] at h
      exact h
    · have h := ih (1 : Fin 2)
      change H ((U).map (pullback.fst _ _ ≫ prod.lift prod.fst imp ≫ finiteChild F 2 1) r) at h
      erw [finiteChild_two_one,prod.lift_snd,CategoryTheory.Functor.map_comp_apply] at h
      exact h

end CategoricalEssentialIncompleteness.V46.Miller.Derivation.WordInduction
