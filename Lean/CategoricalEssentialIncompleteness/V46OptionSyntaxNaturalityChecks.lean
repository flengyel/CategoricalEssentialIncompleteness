/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46OptionSyntaxNaturality

/-! # Statement checks for OptionSyntaxNaturality -/

@[expose] public section

noncomputable section

universe v u
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness CategoricalEssentialIncompleteness.V46

variable {D : Type u} [Category.{v} D] [Regular D] [FinitaryExtensive D]
open OptionSyntax

example {V Y Y' Z Z' : D}
    (h : V ⨯ Y ⟶ Z) (h' : V ⨯ Y' ⟶ Z') (p : Y ⟶ Y') (q : Z ⟶ Z')
    (hw : h ≫ q = prod.map (𝟙 V) p ≫ h') :
    coefficient h ≫ map q = prod.map (𝟙 V) (map p) ≫ coefficient h' := OptionSyntax.coefficient_natural h h' p q hw

#print axioms CategoricalEssentialIncompleteness.V46.OptionSyntax.coefficient_natural

example {Y Y' Z Z' : D}
    (h : Y ⨯ Y ⟶ Z) (h' : Y' ⨯ Y' ⟶ Z') (p : Y ⟶ Y') (q : Z ⟶ Z')
    (hw : h ≫ q = prod.map p p ≫ h') :
    binary h ≫ map q = prod.map (map p) (map p) ≫ binary h' := OptionSyntax.binary_natural h h' p q hw

#print axioms CategoricalEssentialIncompleteness.V46.OptionSyntax.binary_natural
