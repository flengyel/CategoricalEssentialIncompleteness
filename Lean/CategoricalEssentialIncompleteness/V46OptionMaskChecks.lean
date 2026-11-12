/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46OptionMask

/-! # Statement checks for OptionMask -/

@[expose] public section

noncomputable section

universe v u
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness CategoricalEssentialIncompleteness.V46

variable {D : Type u} [Category.{v} D] [Regular D] [FinitaryExtensive D]
open OptionSyntax
example {W Y Z : D} (v : W ⟶ Z) (a : W ⟶ Y) :
    mask v (a ≫ coprod.inr) = v ≫ coprod.inr := mask_ok v a
example {W Y Z : D} (v : W ⟶ Z) (b : W ⟶ Two D) (a₀ a₁ : W ⟶ obj Y) :
    mask v (Two.branch b a₀ a₁) = Two.branch b (mask v a₀) (mask v a₁) :=
  mask_branch v b a₀ a₁
example {W Y Y' Z Z' : D} (h : Y ⨯ Y ⟶ Z) (h' : Y' ⨯ Y' ⟶ Z')
    (a b : W ⟶ obj Y) (v w : W ⟶ Y') :
    mask (prod.lift v w ≫ h') (prod.lift a b ≫ binary h) =
      prod.lift (mask v a) (mask w b) ≫ binary h' := mask_binary h h' a b v w

#print axioms CategoricalEssentialIncompleteness.V46.OptionSyntax.mask_precomp
#print axioms CategoricalEssentialIncompleteness.V46.OptionSyntax.mask_map
#print axioms CategoricalEssentialIncompleteness.V46.OptionSyntax.mask_postcomp
#print axioms CategoricalEssentialIncompleteness.V46.OptionSyntax.mask_branch
#print axioms CategoricalEssentialIncompleteness.V46.OptionSyntax.mask_coefficient
#print axioms CategoricalEssentialIncompleteness.V46.OptionSyntax.mask_binary
