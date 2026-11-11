/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SyntaxOptionTransport

/-! # Preservation of the actual lifted option constructors -/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v₁ v₂ u₁ u₂
open CategoryTheory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness.V46.SyntaxOptionTransport
variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
variable [Regular C] [FinitaryExtensive C] [Regular D] [FinitaryExtensive D]
variable (E : C ≌ D)
local notation "F" => E.functor

omit [Regular C] [Regular D] in
/-- Equivalences preserve the actual source-fiber coproduct cover.
The target fibers do not have to use the same chosen objects. -/
theorem map_sumFibers_hom_ext {W A B : C} (f : W ⟶ A ⨿ B) {Z : D}
    {g h : E.functor.obj W ⟶ Z}
    (h₀ : E.functor.map (pullback.fst f coprod.inl) ≫ g = E.functor.map (pullback.fst f coprod.inl) ≫ h)
    (h₁ : E.functor.map (pullback.fst f coprod.inr) ≫ g = E.functor.map (pullback.fst f coprod.inr) ≫ h) : g = h := by
  apply (isColimitOfPreserves F (SumFibers.isColimit f)).hom_ext
  rintro ⟨i⟩
  cases i
  · exact h₀
  · exact h₁

private theorem map_coefficient_failure {W V Y Z : C} {V' Y' Z' : D}
    (i : E.functor.obj V ≅ V') (j : E.functor.obj Y ≅ Y') (l : E.functor.obj Z ≅ Z')
    (h : V ⨯ Y ⟶ Z) (h' : V' ⨯ Y' ⟶ Z')
    (u : W ⟶ V ⨯ OptionSyntax.obj Y) (a : W ⟶ ⊤_ C)
    (hu : u ≫ prod.snd = a ≫ coprod.inl) :
    (E.functor.map u ≫ E.functor.map (OptionSyntax.coefficient h)) ≫ (optionIso E l).hom =
      (E.functor.map u ≫ (productIso E i (optionIso E j)).hom) ≫ OptionSyntax.coefficient h' := by
  have ht : (E.functor.map u ≫ (productIso E i (optionIso E j)).hom) ≫ prod.snd =
      (E.functor.map a ≫ (DecidableVariables.Transport.terminalIso E).hom) ≫ coprod.inl := by
    rw [mapped_product_snd,hu,map_none]
  rw [← E.functor.map_comp,coefficient_failure h u a hu,map_fail]
  exact (coefficient_failure h' _ _ ht).symm

private theorem map_coefficient_success {W V Y Z : C} {V' Y' Z' : D}
    (i : E.functor.obj V ≅ V') (j : E.functor.obj Y ≅ Y') (l : E.functor.obj Z ≅ Z')
    (h : V ⨯ Y ⟶ Z) (h' : V' ⨯ Y' ⟶ Z')
    (hh : E.functor.map h ≫ l.hom = (productIso E i j).hom ≫ h')
    (u : W ⟶ V ⨯ OptionSyntax.obj Y) (y : W ⟶ Y)
    (hu : u ≫ prod.snd = y ≫ coprod.inr) :
    (E.functor.map u ≫ E.functor.map (OptionSyntax.coefficient h)) ≫ (optionIso E l).hom =
      (E.functor.map u ≫ (productIso E i (optionIso E j)).hom) ≫ OptionSyntax.coefficient h' := by
  have ht : (E.functor.map u ≫ (productIso E i (optionIso E j)).hom) ≫ prod.snd =
      (E.functor.map y ≫ j.hom) ≫ coprod.inr := by
    rw [mapped_product_snd,hu,map_some]
  calc
    _ = prod.lift (E.functor.map (u ≫ prod.fst) ≫ i.hom) (E.functor.map y ≫ j.hom) ≫ h' ≫ coprod.inr := by
      rw [← E.functor.map_comp,coefficient_success h u y hu,map_pair_some E i j l h h' hh]
    _ = _ := by
      rw [coefficient_success h' _ _ ht,mapped_product_fst]

/-- Lifting an arbitrary coefficient constructor commutes with the
equivalence whenever its ordinary constructor square commutes. -/
theorem map_coefficient {V Y Z : C} {V' Y' Z' : D}
    (i : E.functor.obj V ≅ V') (j : E.functor.obj Y ≅ Y') (l : E.functor.obj Z ≅ Z')
    (h : V ⨯ Y ⟶ Z) (h' : V' ⨯ Y' ⟶ Z')
    (hh : E.functor.map h ≫ l.hom = (productIso E i j).hom ≫ h') :
    E.functor.map (OptionSyntax.coefficient h) ≫ (optionIso E l).hom =
      (productIso E i (optionIso E j)).hom ≫ OptionSyntax.coefficient h' := by
  apply map_sumFibers_hom_ext E (prod.snd : V ⨯ OptionSyntax.obj Y ⟶ _)
  · simpa only [Category.assoc] using map_coefficient_failure E i j l h h'
      (pullback.fst (prod.snd : V ⨯ OptionSyntax.obj Y ⟶ _) coprod.inl)
      (pullback.snd (prod.snd : V ⨯ OptionSyntax.obj Y ⟶ _) coprod.inl) pullback.condition
  · simpa only [Category.assoc] using map_coefficient_success E i j l h h' hh
      (pullback.fst (prod.snd : V ⨯ OptionSyntax.obj Y ⟶ _) coprod.inr)
      (pullback.snd (prod.snd : V ⨯ OptionSyntax.obj Y ⟶ _) coprod.inr) pullback.condition

private theorem map_binary_failure_first {W Y Z : C} {Y' Z' : D}
    (i : E.functor.obj Y ≅ Y') (j : E.functor.obj Z ≅ Z') (h : Y ⨯ Y ⟶ Z) (h' : Y' ⨯ Y' ⟶ Z')
    (u : W ⟶ OptionSyntax.obj Y ⨯ OptionSyntax.obj Y) (a : W ⟶ ⊤_ C)
    (hu : u ≫ prod.fst = a ≫ coprod.inl) :
    (E.functor.map u ≫ E.functor.map (OptionSyntax.binary h)) ≫ (optionIso E j).hom =
      (E.functor.map u ≫ (productIso E (optionIso E i) (optionIso E i)).hom) ≫ OptionSyntax.binary h' := by
  have ht : (E.functor.map u ≫ (productIso E (optionIso E i) (optionIso E i)).hom) ≫ prod.fst =
      (E.functor.map a ≫ (DecidableVariables.Transport.terminalIso E).hom) ≫ coprod.inl := by
    rw [mapped_product_fst,hu,map_none]
  rw [← E.functor.map_comp,binary_failure_first h u a hu,map_fail]
  exact (binary_failure_first h' _ _ ht).symm

private theorem map_binary_failure_second {W Y Z : C} {Y' Z' : D}
    (i : E.functor.obj Y ≅ Y') (j : E.functor.obj Z ≅ Z') (h : Y ⨯ Y ⟶ Z) (h' : Y' ⨯ Y' ⟶ Z')
    (u : W ⟶ OptionSyntax.obj Y ⨯ OptionSyntax.obj Y) (y : W ⟶ Y) (a : W ⟶ ⊤_ C)
    (hy : u ≫ prod.fst = y ≫ coprod.inr) (ha : u ≫ prod.snd = a ≫ coprod.inl) :
    (E.functor.map u ≫ E.functor.map (OptionSyntax.binary h)) ≫ (optionIso E j).hom =
      (E.functor.map u ≫ (productIso E (optionIso E i) (optionIso E i)).hom) ≫ OptionSyntax.binary h' := by
  have ht₁ : (E.functor.map u ≫ (productIso E (optionIso E i) (optionIso E i)).hom) ≫ prod.fst =
      (E.functor.map y ≫ i.hom) ≫ coprod.inr := by
    rw [mapped_product_fst,hy,map_some]
  have ht₂ : (E.functor.map u ≫ (productIso E (optionIso E i) (optionIso E i)).hom) ≫ prod.snd =
      (E.functor.map a ≫ (DecidableVariables.Transport.terminalIso E).hom) ≫ coprod.inl := by
    rw [mapped_product_snd,ha,map_none]
  rw [← E.functor.map_comp,binary_failure_second h u y a hy ha,map_fail]
  exact (binary_failure_second h' _ _ _ ht₁ ht₂).symm

private theorem map_binary_success {W Y Z : C} {Y' Z' : D}
    (i : E.functor.obj Y ≅ Y') (j : E.functor.obj Z ≅ Z') (h : Y ⨯ Y ⟶ Z) (h' : Y' ⨯ Y' ⟶ Z')
    (hh : E.functor.map h ≫ j.hom = (productIso E i i).hom ≫ h')
    (u : W ⟶ OptionSyntax.obj Y ⨯ OptionSyntax.obj Y) (y z : W ⟶ Y)
    (hy : u ≫ prod.fst = y ≫ coprod.inr) (hz : u ≫ prod.snd = z ≫ coprod.inr) :
    (E.functor.map u ≫ E.functor.map (OptionSyntax.binary h)) ≫ (optionIso E j).hom =
      (E.functor.map u ≫ (productIso E (optionIso E i) (optionIso E i)).hom) ≫ OptionSyntax.binary h' := by
  have ht₁ : (E.functor.map u ≫ (productIso E (optionIso E i) (optionIso E i)).hom) ≫ prod.fst =
      (E.functor.map y ≫ i.hom) ≫ coprod.inr := by
    rw [mapped_product_fst,hy,map_some]
  have ht₂ : (E.functor.map u ≫ (productIso E (optionIso E i) (optionIso E i)).hom) ≫ prod.snd =
      (E.functor.map z ≫ i.hom) ≫ coprod.inr := by
    rw [mapped_product_snd,hz,map_some]
  calc
    _ = prod.lift (E.functor.map y ≫ i.hom) (E.functor.map z ≫ i.hom) ≫ h' ≫ coprod.inr := by
      rw [← E.functor.map_comp,binary_success h u y z hy hz,map_pair_some E i i j h h' hh]
    _ = _ := (binary_success h' _ _ _ ht₁ ht₂).symm

/-- Both operand failures and the simultaneous success case are
transported for the actual binary option operation. -/
theorem map_binary {Y Z : C} {Y' Z' : D}
    (i : E.functor.obj Y ≅ Y') (j : E.functor.obj Z ≅ Z') (h : Y ⨯ Y ⟶ Z) (h' : Y' ⨯ Y' ⟶ Z')
    (hh : E.functor.map h ≫ j.hom = (productIso E i i).hom ≫ h') :
    E.functor.map (OptionSyntax.binary h) ≫ (optionIso E j).hom =
      (productIso E (optionIso E i) (optionIso E i)).hom ≫ OptionSyntax.binary h' := by
  let p := (prod.fst : OptionSyntax.obj Y ⨯ OptionSyntax.obj Y ⟶ OptionSyntax.obj Y)
  apply map_sumFibers_hom_ext E p
  · simpa only [Category.assoc] using map_binary_failure_first E i j h h'
      (pullback.fst p coprod.inl) (pullback.snd p coprod.inl) pullback.condition
  · let q := pullback.fst p coprod.inr ≫ prod.snd
    apply map_sumFibers_hom_ext E q
    · have hy : (pullback.fst q coprod.inl ≫ pullback.fst p coprod.inr) ≫ prod.fst =
          (pullback.fst q coprod.inl ≫ pullback.snd p coprod.inr) ≫ coprod.inr := by
        rw [Category.assoc,pullback.condition,← Category.assoc]
      have ha : (pullback.fst q coprod.inl ≫ pullback.fst p coprod.inr) ≫ prod.snd =
          pullback.snd q coprod.inl ≫ coprod.inl := by
        rw [Category.assoc]
        exact pullback.condition
      have h := map_binary_failure_second E i j h h'
        (pullback.fst q coprod.inl ≫ pullback.fst p coprod.inr)
        (pullback.fst q coprod.inl ≫ pullback.snd p coprod.inr)
        (pullback.snd q coprod.inl) hy ha
      simpa only [E.functor.map_comp,Category.assoc] using h
    · have hy : (pullback.fst q coprod.inr ≫ pullback.fst p coprod.inr) ≫ prod.fst =
          (pullback.fst q coprod.inr ≫ pullback.snd p coprod.inr) ≫ coprod.inr := by
        rw [Category.assoc,pullback.condition,← Category.assoc]
      have hz : (pullback.fst q coprod.inr ≫ pullback.fst p coprod.inr) ≫ prod.snd =
          pullback.snd q coprod.inr ≫ coprod.inr := by
        rw [Category.assoc]
        exact pullback.condition
      have h := map_binary_success E i j h h' hh
        (pullback.fst q coprod.inr ≫ pullback.fst p coprod.inr)
        (pullback.fst q coprod.inr ≫ pullback.snd p coprod.inr)
        (pullback.snd q coprod.inr) hy hz
      simpa only [E.functor.map_comp,Category.assoc] using h

end CategoricalEssentialIncompleteness.V46.SyntaxOptionTransport
