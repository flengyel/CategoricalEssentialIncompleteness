/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SignedFirstOrderAdjunction

/-! # Statement checks for the free first-order adjunction -/

@[expose] public section

noncomputable section

universe v u
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness CategoricalEssentialIncompleteness.V46

variable {D : Type u} [Category.{v} D] [Regular D] [FinitaryExtensive D]
variable {V : D}
variable (F : NullaryPresentations V)
open SignedFirstOrder

example : generation F ⊣ extraction F := adjunction F

example (A : Pair F) (B : Theories (D := D) (V := V)) :
    (generatedObject F A ⟶ B) ≃ (A ⟶ extractionObject F B) := homEquiv F A B

#print axioms CategoricalEssentialIncompleteness.V46.SignedFirstOrder.adjunction
#print axioms CategoricalEssentialIncompleteness.V46.SignedFirstOrder.homEquiv

example (A : Pair F) :
    ((adjunction F).unit.app A).arrow = NullaryInterpretation.atomSentence (F.syntaxData A.carrier) :=
  unit_arrow F A

#print axioms
  CategoricalEssentialIncompleteness.V46.SignedFirstOrder.unit_arrow

example (A : Theories (D := D) (V := V)) :
    ((adjunction F).counit.app A).hom.hom.translation =
      F.interpretation A.presentation (𝟙 A.presentation.syntaxData.sentenceObject) :=
  counit_translation F A

#print axioms
  CategoricalEssentialIncompleteness.V46.SignedFirstOrder.counit_translation
