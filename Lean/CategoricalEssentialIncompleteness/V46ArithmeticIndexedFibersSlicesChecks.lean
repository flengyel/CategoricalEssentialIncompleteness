/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ArithmeticIndexedFibersSlices


/-! # Extensive slice decomposition for numeral fibers -/

@[expose] public section
noncomputable section
universe u v
open CategoryTheory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness.V46.ArithmeticIndexedFibers
variable {D : Type u} [Category.{v} D] [Regular D] [FinitaryExtensive D]
example (A B : D) : Over (A ⨿ B) ≌ Over A × Over B := coproductSliceEquivalence A B
example (A B C : D) (b : A ⨿ B ≅ C) : Over C ≌ Over A × Over B := splitAtEquivalence A B b
example (A B C : D) (b : A ⨿ B ≅ C) :
    (splitOverIso A B b).functor ≅
      (Over.pullback ((coprod.inl : A ⟶ A ⨿ B) ≫ b.hom)).prod'
        (Over.pullback ((coprod.inr : B ⟶ A ⨿ B) ≫ b.hom)) := splitAtComparison A B b
example (A B X : D) : (A ⨯ X) ⨿ (B ⨯ X) ≅ (A ⨿ B) ⨯ X := productSumIso A B X
end CategoricalEssentialIncompleteness.V46.ArithmeticIndexedFibers
