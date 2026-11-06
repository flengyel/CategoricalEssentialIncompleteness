/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46SyntaxBooleanTransport
import CategoricalEssentialIncompleteness.V46CategoricalSubstitutionIdentityOptions

/-! # Actual option and product comparisons through an equivalence -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v₁ v₂ u₁ u₂
open CategoryTheory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness.V46.SyntaxOptionTransport
open DecidableVariables.Transport
variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
variable (E : C ≌ D)
local notation "F" => E.functor

section Comparisons
variable [Regular C] [FinitaryExtensive C]
variable [Regular D] [FinitaryExtensive D]

def optionIso {X : C} {X' : D} (i : E.functor.obj X ≅ X') : E.functor.obj (OptionSyntax.obj X) ≅ OptionSyntax.obj X' :=
  (asIso (coprodComparison F (⊤_ C) X)).symm ≪≫ coprod.mapIso (terminalIso E) i

def productIso {X Y : C} {X' Y' : D} (i : E.functor.obj X ≅ X') (j : E.functor.obj Y ≅ Y') :
    E.functor.obj (X ⨯ Y) ≅ X' ⨯ Y' :=
  asIso (prodComparison F X Y) ≪≫ prod.mapIso i j

@[reassoc] theorem optionIso_inl {X : C} {X' : D} (i : E.functor.obj X ≅ X') :
    E.functor.map (coprod.inl : ⊤_ C ⟶ OptionSyntax.obj X) ≫ (optionIso E i).hom =
      (terminalIso E).hom ≫ coprod.inl := by
  change E.functor.map coprod.inl ≫ (inv (coprodComparison F (⊤_ C) X) ≫
    coprod.map (terminalComparison F) i.hom) = _
  rw [← Category.assoc,map_inl_inv_coprodComparison,coprod.inl_map]
  rfl

@[reassoc] theorem optionIso_inr {X : C} {X' : D} (i : E.functor.obj X ≅ X') :
    E.functor.map (coprod.inr : X ⟶ OptionSyntax.obj X) ≫ (optionIso E i).hom = i.hom ≫ coprod.inr := by
  change E.functor.map coprod.inr ≫ (inv (coprodComparison F (⊤_ C) X) ≫
    coprod.map (terminalComparison F) i.hom) = _
  rw [← Category.assoc,map_inr_inv_coprodComparison,coprod.inr_map]

omit [FinitaryExtensive C] [FinitaryExtensive D] in
@[reassoc] theorem productIso_fst {X Y : C} {X' Y' : D}
    (i : E.functor.obj X ≅ X') (j : E.functor.obj Y ≅ Y') :
    (productIso E i j).hom ≫ prod.fst = E.functor.map prod.fst ≫ i.hom := by
  simp [productIso,Category.assoc]

omit [FinitaryExtensive C] [FinitaryExtensive D] in
@[reassoc] theorem productIso_snd {X Y : C} {X' Y' : D}
    (i : E.functor.obj X ≅ X') (j : E.functor.obj Y ≅ Y') :
    (productIso E i j).hom ≫ prod.snd = E.functor.map prod.snd ≫ j.hom := by
  simp [productIso,Category.assoc]

omit [FinitaryExtensive C] [FinitaryExtensive D] in
theorem mapped_product_fst {W X Y : C} {X' Y' : D}
    (i : E.functor.obj X ≅ X') (j : E.functor.obj Y ≅ Y') (k : W ⟶ X ⨯ Y) :
    (E.functor.map k ≫ (productIso E i j).hom) ≫ prod.fst = E.functor.map (k ≫ prod.fst) ≫ i.hom := by
  rw [Category.assoc,productIso_fst,← Category.assoc,← E.functor.map_comp]

omit [FinitaryExtensive C] [FinitaryExtensive D] in
theorem mapped_product_snd {W X Y : C} {X' Y' : D}
    (i : E.functor.obj X ≅ X') (j : E.functor.obj Y ≅ Y') (k : W ⟶ X ⨯ Y) :
    (E.functor.map k ≫ (productIso E i j).hom) ≫ prod.snd = E.functor.map (k ≫ prod.snd) ≫ j.hom := by
  rw [Category.assoc,productIso_snd,← Category.assoc,← E.functor.map_comp]

omit [FinitaryExtensive C] [FinitaryExtensive D] in
theorem map_lift {W X Y : C} {X' Y' : D}
    (i : E.functor.obj X ≅ X') (j : E.functor.obj Y ≅ Y') (x : W ⟶ X) (y : W ⟶ Y) :
    E.functor.map (prod.lift x y) ≫ (productIso E i j).hom =
      prod.lift (E.functor.map x ≫ i.hom) (E.functor.map y ≫ j.hom) := by
  apply prod.hom_ext
  · rw [mapped_product_fst,prod.lift_fst,prod.lift_fst]
  · rw [mapped_product_snd,prod.lift_snd,prod.lift_snd]

theorem map_fail {W X : C} {X' : D} (i : E.functor.obj X ≅ X') :
    E.functor.map (OptionSyntax.fail : W ⟶ OptionSyntax.obj X) ≫ (optionIso E i).hom =
      (OptionSyntax.fail : E.functor.obj W ⟶ OptionSyntax.obj X') := by
  unfold OptionSyntax.fail
  rw [E.functor.map_comp,Category.assoc,optionIso_inl,← Category.assoc]
  congr 1
  exact terminalIsTerminal.hom_ext _ _

theorem map_some {W X : C} {X' : D} (i : E.functor.obj X ≅ X') (x : W ⟶ X) :
    E.functor.map (x ≫ (coprod.inr : X ⟶ OptionSyntax.obj X)) ≫ (optionIso E i).hom =
      (E.functor.map x ≫ i.hom) ≫ coprod.inr := by
  rw [E.functor.map_comp,Category.assoc,optionIso_inr,← Category.assoc]

theorem map_none {W X : C} {X' : D} (i : E.functor.obj X ≅ X') (x : W ⟶ ⊤_ C) :
    E.functor.map (x ≫ (coprod.inl : ⊤_ C ⟶ OptionSyntax.obj X)) ≫ (optionIso E i).hom =
      (E.functor.map x ≫ (terminalIso E).hom) ≫ coprod.inl := by
  rw [E.functor.map_comp,Category.assoc,optionIso_inl,← Category.assoc]

/-- A value-map square induces the actual option-map square. -/
theorem map_option_map {X Y : C} {X' Y' : D}
    (i : E.functor.obj X ≅ X') (j : E.functor.obj Y ≅ Y') (f : X ⟶ Y) (g : X' ⟶ Y')
    (hf : E.functor.map f ≫ j.hom = i.hom ≫ g) :
    E.functor.map (OptionSyntax.map f) ≫ (optionIso E j).hom =
      (optionIso E i).hom ≫ OptionSyntax.map g := by
  apply BinaryCofan.IsColimit.hom_ext
    (isColimitOfHasBinaryCoproductOfPreservesColimit F (⊤_ C) X)
  · change E.functor.map (coprod.inl : ⊤_ C ⟶ OptionSyntax.obj X) ≫
      (E.functor.map (OptionSyntax.map f) ≫ (optionIso E j).hom) =
        E.functor.map (coprod.inl : ⊤_ C ⟶ OptionSyntax.obj X) ≫
          ((optionIso E i).hom ≫ OptionSyntax.map g)
    calc
      _ = E.functor.map (coprod.inl : ⊤_ C ⟶ OptionSyntax.obj Y) ≫ (optionIso E j).hom := by
        rw [← Category.assoc,← E.functor.map_comp]
        simp [OptionSyntax.map]
      _ = (terminalIso E).hom ≫ coprod.inl := optionIso_inl E j
      _ = _ := by
        rw [← Category.assoc,optionIso_inl,Category.assoc]
        simp [OptionSyntax.map]
  · change E.functor.map (coprod.inr : X ⟶ OptionSyntax.obj X) ≫
      (E.functor.map (OptionSyntax.map f) ≫ (optionIso E j).hom) =
        E.functor.map (coprod.inr : X ⟶ OptionSyntax.obj X) ≫
          ((optionIso E i).hom ≫ OptionSyntax.map g)
    calc
      _ = E.functor.map f ≫ j.hom ≫ coprod.inr := by
        rw [← Category.assoc,← E.functor.map_comp,OptionSyntax.map,coprod.inr_map,
          E.functor.map_comp,Category.assoc,optionIso_inr]
      _ = i.hom ≫ g ≫ coprod.inr := by rw [← Category.assoc,hf,Category.assoc]
      _ = _ := by
        rw [optionIso_inr_assoc,OptionSyntax.map,coprod.inr_map]

/-- The ordinary constructor square also determines its successful
option-valued square, including the actual product comparison. -/
theorem map_pair_some {W X Y Z : C} {X' Y' Z' : D}
    (i : E.functor.obj X ≅ X') (j : E.functor.obj Y ≅ Y') (k : E.functor.obj Z ≅ Z')
    (h : X ⨯ Y ⟶ Z) (h' : X' ⨯ Y' ⟶ Z')
    (hh : E.functor.map h ≫ k.hom = (productIso E i j).hom ≫ h')
    (x : W ⟶ X) (y : W ⟶ Y) :
    E.functor.map (prod.lift x y ≫ h ≫ (coprod.inr : Z ⟶ OptionSyntax.obj Z)) ≫
        (optionIso E k).hom =
      prod.lift (E.functor.map x ≫ i.hom) (E.functor.map y ≫ j.hom) ≫ h' ≫ coprod.inr := by
  calc
    _ = (E.functor.map (prod.lift x y ≫ h) ≫ k.hom) ≫ coprod.inr := by
      rw [← Category.assoc,map_some]
    _ = (E.functor.map (prod.lift x y) ≫ (E.functor.map h ≫ k.hom)) ≫ coprod.inr := by
      simp only [E.functor.map_comp,Category.assoc]
    _ = (E.functor.map (prod.lift x y) ≫ ((productIso E i j).hom ≫ h')) ≫ coprod.inr := by rw [hh]
    _ = (E.functor.map (prod.lift x y) ≫ (productIso E i j).hom) ≫ h' ≫ coprod.inr := by
      simp only [Category.assoc]
    _ = _ := by rw [map_lift]

end Comparisons

section Branches
variable [Regular C] [FinitaryExtensive C]

theorem coefficient_failure {W V Y Z : C} (h : V ⨯ Y ⟶ Z)
    (k : W ⟶ V ⨯ OptionSyntax.obj Y) (a : W ⟶ ⊤_ C)
    (hk : k ≫ prod.snd = a ≫ coprod.inl) :
    k ≫ OptionSyntax.coefficient h = OptionSyntax.fail := by
  unfold OptionSyntax.coefficient
  rw [SumFibers.comp_caseOf_inl _ _ _ k a hk]
  unfold OptionSyntax.fail
  rw [← Category.assoc]
  congr 1
  exact terminalIsTerminal.hom_ext _ _

theorem coefficient_success {W V Y Z : C} (h : V ⨯ Y ⟶ Z)
    (k : W ⟶ V ⨯ OptionSyntax.obj Y) (y : W ⟶ Y)
    (hk : k ≫ prod.snd = y ≫ coprod.inr) :
    k ≫ OptionSyntax.coefficient h = prod.lift (k ≫ prod.fst) y ≫ h ≫ coprod.inr := by
  have he : k = prod.lift (k ≫ prod.fst) (y ≫ coprod.inr) := by
    apply prod.hom_ext <;> simp [hk]
  rw [he,OptionSyntax.coefficient_ok]
  simp only [prod.lift_fst]

theorem binary_failure_first {W Y Z : C} (h : Y ⨯ Y ⟶ Z)
    (k : W ⟶ OptionSyntax.obj Y ⨯ OptionSyntax.obj Y) (a : W ⟶ ⊤_ C)
    (hk : k ≫ prod.fst = a ≫ coprod.inl) :
    k ≫ OptionSyntax.binary h = OptionSyntax.fail := by
  unfold OptionSyntax.binary
  rw [SumFibers.comp_caseOf_inl _ _ _ k a hk]
  unfold OptionSyntax.fail
  rw [← Category.assoc]
  congr 1
  exact terminalIsTerminal.hom_ext _ _

theorem binary_failure_second {W Y Z : C} (h : Y ⨯ Y ⟶ Z)
    (k : W ⟶ OptionSyntax.obj Y ⨯ OptionSyntax.obj Y)
    (y : W ⟶ Y) (a : W ⟶ ⊤_ C)
    (hy : k ≫ prod.fst = y ≫ coprod.inr) (ha : k ≫ prod.snd = a ≫ coprod.inl) :
    k ≫ OptionSyntax.binary h = OptionSyntax.fail := by
  let l := pullback.lift k y hy
  have hl : l ≫ (pullback.fst (prod.fst : OptionSyntax.obj Y ⨯ OptionSyntax.obj Y ⟶ _) coprod.inr ≫
      prod.snd) = a ≫ coprod.inl := by simp [l,ha]
  unfold OptionSyntax.binary
  rw [SumFibers.comp_caseOf_inr _ _ _ k y hy,SumFibers.comp_caseOf_inl _ _ _ l a hl]
  unfold OptionSyntax.fail
  rw [← Category.assoc]
  congr 1
  exact terminalIsTerminal.hom_ext _ _

theorem binary_success {W Y Z : C} (h : Y ⨯ Y ⟶ Z)
    (k : W ⟶ OptionSyntax.obj Y ⨯ OptionSyntax.obj Y) (y z : W ⟶ Y)
    (hy : k ≫ prod.fst = y ≫ coprod.inr) (hz : k ≫ prod.snd = z ≫ coprod.inr) :
    k ≫ OptionSyntax.binary h = prod.lift y z ≫ h ≫ coprod.inr := by
  have he : k = prod.lift (y ≫ coprod.inr) (z ≫ coprod.inr) := by
    apply prod.hom_ext <;> simp [hy,hz]
  rw [he,OptionSyntax.binary_ok]

end Branches
end CategoricalEssentialIncompleteness.V46.SyntaxOptionTransport
