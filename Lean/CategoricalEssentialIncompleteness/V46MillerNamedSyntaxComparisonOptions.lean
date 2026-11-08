import CategoricalEssentialIncompleteness.V46MillerDerivationEquality
import CategoricalEssentialIncompleteness.V46CategoricalSubstitutionIdentityOptions
import CategoricalEssentialIncompleteness.V46SyntaxOptionTransport

/-! # Actual option/product comparison for a finite-geometry functor

This contains no equivalence or initiality-preservation assumption.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v₁ v₂ u₁ u₂
open CategoryTheory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness.V46.Miller.NamedSyntaxComparison.Options
variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
variable (F : C ⥤ D) [PreservesFiniteLimits F] [PreservesFiniteCoproducts F]

section Comparisons
variable [Regular C] [FinitaryExtensive C]
variable [Regular D] [FinitaryExtensive D]

def optionIso {X : C} {X' : D} (i : F.obj X ≅ X') : F.obj (OptionSyntax.obj X) ≅ OptionSyntax.obj X' :=
  (asIso (coprodComparison F (⊤_ C) X)).symm ≪≫ coprod.mapIso (asIso (terminalComparison F)) i

def productIso {X Y : C} {X' Y' : D} (i : F.obj X ≅ X') (j : F.obj Y ≅ Y') :
    F.obj (X ⨯ Y) ≅ X' ⨯ Y' :=
  asIso (prodComparison F X Y) ≪≫ prod.mapIso i j

@[reassoc] theorem optionIso_inl {X : C} {X' : D} (i : F.obj X ≅ X') :
    F.map (coprod.inl : ⊤_ C ⟶ OptionSyntax.obj X) ≫ (optionIso F i).hom =
      (asIso (terminalComparison F)).hom ≫ coprod.inl := by
  change F.map coprod.inl ≫ (inv (coprodComparison F (⊤_ C) X) ≫
    coprod.map (terminalComparison F) i.hom) = _
  rw [← Category.assoc,map_inl_inv_coprodComparison,coprod.inl_map]
  rfl

@[reassoc] theorem optionIso_inr {X : C} {X' : D} (i : F.obj X ≅ X') :
    F.map (coprod.inr : X ⟶ OptionSyntax.obj X) ≫ (optionIso F i).hom = i.hom ≫ coprod.inr := by
  change F.map coprod.inr ≫ (inv (coprodComparison F (⊤_ C) X) ≫
    coprod.map (terminalComparison F) i.hom) = _
  rw [← Category.assoc,map_inr_inv_coprodComparison,coprod.inr_map]

omit [FinitaryExtensive C] [FinitaryExtensive D] [PreservesFiniteCoproducts F] in
@[reassoc] theorem productIso_fst {X Y : C} {X' Y' : D}
    (i : F.obj X ≅ X') (j : F.obj Y ≅ Y') :
    (productIso F i j).hom ≫ prod.fst = F.map prod.fst ≫ i.hom := by
  simp [productIso,Category.assoc]

omit [FinitaryExtensive C] [FinitaryExtensive D] [PreservesFiniteCoproducts F] in
@[reassoc] theorem productIso_snd {X Y : C} {X' Y' : D}
    (i : F.obj X ≅ X') (j : F.obj Y ≅ Y') :
    (productIso F i j).hom ≫ prod.snd = F.map prod.snd ≫ j.hom := by
  simp [productIso,Category.assoc]

omit [FinitaryExtensive C] [FinitaryExtensive D] [PreservesFiniteCoproducts F] in
theorem mapped_product_fst {W X Y : C} {X' Y' : D}
    (i : F.obj X ≅ X') (j : F.obj Y ≅ Y') (k : W ⟶ X ⨯ Y) :
    (F.map k ≫ (productIso F i j).hom) ≫ prod.fst = F.map (k ≫ prod.fst) ≫ i.hom := by
  rw [Category.assoc,productIso_fst,← Category.assoc,← F.map_comp]

omit [FinitaryExtensive C] [FinitaryExtensive D] [PreservesFiniteCoproducts F] in
theorem mapped_product_snd {W X Y : C} {X' Y' : D}
    (i : F.obj X ≅ X') (j : F.obj Y ≅ Y') (k : W ⟶ X ⨯ Y) :
    (F.map k ≫ (productIso F i j).hom) ≫ prod.snd = F.map (k ≫ prod.snd) ≫ j.hom := by
  rw [Category.assoc,productIso_snd,← Category.assoc,← F.map_comp]

omit [FinitaryExtensive C] [FinitaryExtensive D] [PreservesFiniteCoproducts F] in
theorem map_lift {W X Y : C} {X' Y' : D}
    (i : F.obj X ≅ X') (j : F.obj Y ≅ Y') (x : W ⟶ X) (y : W ⟶ Y) :
    F.map (prod.lift x y) ≫ (productIso F i j).hom =
      prod.lift (F.map x ≫ i.hom) (F.map y ≫ j.hom) := by
  apply prod.hom_ext
  · rw [mapped_product_fst,prod.lift_fst,prod.lift_fst]
  · rw [mapped_product_snd,prod.lift_snd,prod.lift_snd]

theorem map_fail {W X : C} {X' : D} (i : F.obj X ≅ X') :
    F.map (OptionSyntax.fail : W ⟶ OptionSyntax.obj X) ≫ (optionIso F i).hom =
      (OptionSyntax.fail : F.obj W ⟶ OptionSyntax.obj X') := by
  unfold OptionSyntax.fail
  rw [F.map_comp,Category.assoc,optionIso_inl,← Category.assoc]
  congr 1
  exact terminalIsTerminal.hom_ext _ _

theorem map_some {W X : C} {X' : D} (i : F.obj X ≅ X') (x : W ⟶ X) :
    F.map (x ≫ (coprod.inr : X ⟶ OptionSyntax.obj X)) ≫ (optionIso F i).hom =
      (F.map x ≫ i.hom) ≫ coprod.inr := by
  rw [F.map_comp,Category.assoc,optionIso_inr,← Category.assoc]

theorem map_none {W X : C} {X' : D} (i : F.obj X ≅ X') (x : W ⟶ ⊤_ C) :
    F.map (x ≫ (coprod.inl : ⊤_ C ⟶ OptionSyntax.obj X)) ≫ (optionIso F i).hom =
      (F.map x ≫ (asIso (terminalComparison F)).hom) ≫ coprod.inl := by
  rw [F.map_comp,Category.assoc,optionIso_inl,← Category.assoc]

/-- A value-map square induces the actual option-map square. -/
theorem map_option_map {X Y : C} {X' Y' : D}
    (i : F.obj X ≅ X') (j : F.obj Y ≅ Y') (f : X ⟶ Y) (g : X' ⟶ Y')
    (hf : F.map f ≫ j.hom = i.hom ≫ g) :
    F.map (OptionSyntax.map f) ≫ (optionIso F j).hom =
      (optionIso F i).hom ≫ OptionSyntax.map g := by
  apply BinaryCofan.IsColimit.hom_ext
    (isColimitOfHasBinaryCoproductOfPreservesColimit F (⊤_ C) X)
  · change F.map (coprod.inl : ⊤_ C ⟶ OptionSyntax.obj X) ≫
      (F.map (OptionSyntax.map f) ≫ (optionIso F j).hom) =
        F.map (coprod.inl : ⊤_ C ⟶ OptionSyntax.obj X) ≫
          ((optionIso F i).hom ≫ OptionSyntax.map g)
    calc
      _ = F.map (coprod.inl : ⊤_ C ⟶ OptionSyntax.obj Y) ≫ (optionIso F j).hom := by
        rw [← Category.assoc,← F.map_comp]
        simp [OptionSyntax.map]
      _ = (asIso (terminalComparison F)).hom ≫ coprod.inl := optionIso_inl F j
      _ = _ := by
        rw [← Category.assoc,optionIso_inl,Category.assoc]
        simp [OptionSyntax.map]
  · change F.map (coprod.inr : X ⟶ OptionSyntax.obj X) ≫
      (F.map (OptionSyntax.map f) ≫ (optionIso F j).hom) =
        F.map (coprod.inr : X ⟶ OptionSyntax.obj X) ≫
          ((optionIso F i).hom ≫ OptionSyntax.map g)
    calc
      _ = F.map f ≫ j.hom ≫ coprod.inr := by
        rw [← Category.assoc,← F.map_comp,OptionSyntax.map,coprod.inr_map,
          F.map_comp,Category.assoc,optionIso_inr]
      _ = i.hom ≫ g ≫ coprod.inr := by rw [← Category.assoc,hf,Category.assoc]
      _ = _ := by
        rw [optionIso_inr_assoc,OptionSyntax.map,coprod.inr_map]

/-- The ordinary constructor square also determines its successful
option-valued square, including the actual product comparison. -/
theorem map_pair_some {W X Y Z : C} {X' Y' Z' : D}
    (i : F.obj X ≅ X') (j : F.obj Y ≅ Y') (k : F.obj Z ≅ Z')
    (h : X ⨯ Y ⟶ Z) (h' : X' ⨯ Y' ⟶ Z')
    (hh : F.map h ≫ k.hom = (productIso F i j).hom ≫ h')
    (x : W ⟶ X) (y : W ⟶ Y) :
    F.map (prod.lift x y ≫ h ≫ (coprod.inr : Z ⟶ OptionSyntax.obj Z)) ≫
        (optionIso F k).hom =
      prod.lift (F.map x ≫ i.hom) (F.map y ≫ j.hom) ≫ h' ≫ coprod.inr := by
  calc
    _ = (F.map (prod.lift x y ≫ h) ≫ k.hom) ≫ coprod.inr := by
      rw [← Category.assoc,map_some]
    _ = (F.map (prod.lift x y) ≫ (F.map h ≫ k.hom)) ≫ coprod.inr := by
      simp only [F.map_comp,Category.assoc]
    _ = (F.map (prod.lift x y) ≫ ((productIso F i j).hom ≫ h')) ≫ coprod.inr := by rw [hh]
    _ = (F.map (prod.lift x y) ≫ (productIso F i j).hom) ≫ h' ≫ coprod.inr := by
      simp only [Category.assoc]
    _ = _ := by rw [map_lift]

end Comparisons
end CategoricalEssentialIncompleteness.V46.Miller.NamedSyntaxComparison.Options
