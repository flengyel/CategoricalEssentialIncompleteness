/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ComputablePowers
public import CategoricalEssentialIncompleteness.V46SplitIdempotentSubcategory

/-! # The representation of a Turing category by its computable finite powers

Cockett and Hofstra, Theorem 4.9(ii), split a class of idempotents in the category
of morphisms computable at the given Turing object. The class below consists
precisely of those idempotents that have a splitting in the ambient category.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory PCategoryStruct RecursionCategory RestrictionCategory Idempotents

namespace CategoricalEssentialIncompleteness.V46.ApplicativeSystem

universe v u
variable {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
variable {A Z : C} (app : nearProd A A ⟶ A) (t : ∀ X : C, X ⟶ Z)

noncomputable def representation (universal : IsTuringMorphism app) (ht : isTotal (t A))
    (unit : ∀ {X : C} (f : X ⟶ Z), f = PCategoryStruct.rst f ≫ t X)
    (retracts : ∀ X : C, ∃ (i : X ⟶ A) (r : A ⟶ X), i ≫ r = 𝟙 X) :
    C ≌ (IdempotentSplitting.splitsIn (inclusion app t)).FullSubcategory := by
  apply IdempotentSplitting.equivalence _ (fullyFaithfulInclusion app t universal ht unit)
  intro X
  obtain ⟨i, r, h⟩ := retracts X
  exact ⟨⟨1⟩, i, r, h⟩

/-- The Turing application is an internal partial combinatory algebra. Its computable
finite powers embed fully faithfully, and splitting the specified idempotents recovers C. -/
theorem structure_of_turing (universal : IsTuringMorphism app) (ht : isTotal (t A))
    (unit : ∀ {X : C} (f : X ⟶ Z), f = PCategoryStruct.rst f ≫ t X)
    (retracts : ∀ X : C, ∃ (i : X ⟶ A) (r : A ⟶ X), i ≫ r = 𝟙 X) :
    CombinatoriallyComplete app t ∧
    (∀ (n m : ℕ) (f : power Z A n ⟶ power Z A m), Computable app t n m f) ∧
    ∃ E : ObjectProperty (Karoubi (Powers app t)),
      (∀ X : Powers app t, E ((toKaroubi _).obj X)) ∧ Nonempty (C ≌ E.FullSubcategory) := by
  have complete := turing_combinatoriallyComplete app t universal ht
  refine ⟨complete, fun n m f => (polynomial_iff_computable app t complete unit n m f).mp
    (all_polynomial app t universal ht unit n m f), IdempotentSplitting.splitsIn (inclusion app t), ?_, ?_⟩
  · exact IdempotentSplitting.identity_mem (inclusion app t)
  · exact ⟨representation app t universal ht unit retracts⟩

end CategoricalEssentialIncompleteness.V46.ApplicativeSystem
