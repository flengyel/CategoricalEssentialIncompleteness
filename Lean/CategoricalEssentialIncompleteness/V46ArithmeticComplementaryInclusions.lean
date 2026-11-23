/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.CharacteristicArrows
public import CategoricalEssentialIncompleteness.V46ArithmeticOmegaComparison
public import CategoricalEssentialIncompleteness.V46SyntacticPredicatesRegular
public import CategoricalEssentialIncompleteness.V46SyntacticPredicatesExtensive

/-! # The total conditional on complementary subobjects in Lemma 8.9 -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.Limits CategoryTheory.RestrictionCategory
open FailureOfComposition.TypedProgramCategory
open CategoricalEssentialIncompleteness.LocalConnectedness

namespace CategoricalEssentialIncompleteness.V46.ArithmeticComplementaryInclusions

open SyntacticPredicates ArithmeticOmegaComparison

/-- The identity splitting of the coproduct in the syntactic recursion category. -/
abbrev numberSum : TotalSplit 𝗣𝗔 :=
  ⟨(splittingInclusion.obj (CoprodStruct.coprod (omegaObject 𝗣𝗔) (omegaObject 𝗣𝗔)))⟩

/-- A total source morphism induces a morphism between identity splittings. -/
def identitySplittingMap {X Y : CodedProgramCategory 𝗣𝗔} (f : X ⟶ Y) (h : isTotal f) :
    (⟨splittingInclusion.obj X⟩ : TotalSplit 𝗣𝗔) ⟶ ⟨splittingInclusion.obj Y⟩ :=
  ⟨splittingInclusion.map f, SplitObject.Hom.ext h⟩

def leftInjection : identityOmega 𝗣𝗔 ⟶ numberSum :=
  identitySplittingMap _ (FailureOfComposition.TypedCoproducts.typed_i0_isTotal 𝗣𝗔 .omega .omega)

def rightInjection : identityOmega 𝗣𝗔 ⟶ numberSum :=
  identitySplittingMap _ (FailureOfComposition.TypedCoproducts.typed_i1_isTotal 𝗣𝗔 .omega .omega)

/-- In the total category the inverse of the copairing chooses a summand.
The resulting conditional is total on the original number object. -/
theorem conditional (A B : Subobject (identityOmega 𝗣𝗔)) (h : IsCompl A B) :
    ∃ (c : (A : TotalSplit 𝗣𝗔) ⨿ (B : TotalSplit 𝗣𝗔) ≅ identityOmega 𝗣𝗔)
      (ℓ : identityOmega 𝗣𝗔 ⟶ numberSum),
      c.hom = coprod.desc A.arrow B.arrow ∧
      ℓ = c.inv ≫ coprod.desc (A.arrow ≫ rightInjection) (B.arrow ≫ leftInjection) ∧
      A.arrow ≫ ℓ = A.arrow ≫ rightInjection ∧ B.arrow ≫ ℓ = B.arrow ≫ leftInjection ∧
      isTotal ℓ.hom.hom := by
  let p : SubobjectPartition (identityOmega 𝗣𝗔) := ⟨B, A, h.symm⟩
  let : IsIso p.cover := SubobjectPartition.cover_isIso p
  let c := asIso p.cover
  let branches := coprod.desc (A.arrow ≫ rightInjection) (B.arrow ≫ leftInjection)
  let ℓ := c.inv ≫ branches
  have hl : (coprod.inl : (A : TotalSplit 𝗣𝗔) ⟶ _) ≫ c.hom = A.arrow :=
    coprod.inl_desc A.arrow B.arrow
  have hr : (coprod.inr : (B : TotalSplit 𝗣𝗔) ⟶ _) ≫ c.hom = B.arrow :=
    coprod.inr_desc A.arrow B.arrow
  refine ⟨c, ℓ, rfl, rfl, ?_, ?_, ?_⟩
  · calc
      A.arrow ≫ ℓ = (coprod.inl ≫ c.hom) ≫ ℓ := congrArg (· ≫ ℓ) hl.symm
      _ = A.arrow ≫ rightInjection := by
        rw [Category.assoc, show c.hom ≫ ℓ = branches from c.hom_inv_id_assoc branches]
        exact coprod.inl_desc _ _
  · calc
      B.arrow ≫ ℓ = (coprod.inr ≫ c.hom) ≫ ℓ := congrArg (· ≫ ℓ) hr.symm
      _ = B.arrow ≫ leftInjection := by
        rw [Category.assoc, show c.hom ≫ ℓ = branches from c.hom_inv_id_assoc branches]
        exact coprod.inr_desc _ _
  · exact congrArg SplitObject.Hom.hom ℓ.property

end CategoricalEssentialIncompleteness.V46.ArithmeticComplementaryInclusions
