/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NumericalCoordinatesCoding

/-! # The same numerical equivalence with literal tuple-code predicate coordinates -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates

namespace CategoricalEssentialIncompleteness.V46.NumericalNamed
local notation "E" => NumericalSyntax.predicateEquivalence
local notation "χ" => NumericalCoordinates.coefficientIso

/-- This inverse uses the actual c.e. set of tuple codes at every object.
Its arrows are recovered through the already proved full numerical functor. -/
def literalInverse : NumericalTuples.Object ⥤ PredicateCategory 𝗧𝗔 where
  obj := NumericalCoordinates.codedPredicate
  map {C D} f := (E).functor.preimage ((χ C).hom ≫ f ≫ (χ D).inv)
  map_id C := by
    apply (E).functor.map_injective
    simp only [Functor.map_preimage, Category.id_comp, Iso.hom_inv_id]
    exact ((E).functor.map_id (NumericalCoordinates.codedPredicate C)).symm
  map_comp f g := by
    apply (E).functor.map_injective
    simp only [Functor.map_preimage, Functor.map_comp, Category.assoc,
      Iso.inv_hom_id_assoc]

def literalCounit : literalInverse ⋙ (E).functor ≅ 𝟭 NumericalTuples.Object :=
  NatIso.ofComponents χ (by
    intro C D f
    change (E).functor.map ((E).functor.preimage ((χ C).hom ≫ f ≫ (χ D).inv)) ≫
      (χ D).hom = (χ C).hom ≫ f
    simp only [Functor.map_preimage, Category.assoc, Iso.inv_hom_id, Category.comp_id])

def literalUnit : 𝟭 (PredicateCategory 𝗧𝗔) ≅ (E).functor ⋙ literalInverse :=
  NatIso.ofComponents
    (fun C => (E).functor.preimageIso ((χ ((E).functor.obj C)).symm)) (by
      intro C D f
      apply (E).functor.map_injective
      change (E).functor.map (f ≫ (E).functor.preimage ((χ ((E).functor.obj D)).inv)) =
        (E).functor.map ((E).functor.preimage ((χ ((E).functor.obj C)).inv) ≫
          (E).functor.preimage ((χ ((E).functor.obj C)).hom ≫
            (E).functor.map f ≫ (χ ((E).functor.obj D)).inv))
      simp only [Functor.map_comp, Functor.map_preimage, Iso.inv_hom_id_assoc])

/-- The forward functor is unchanged. Only its explicit inverse coordinates
are chosen to be the manuscript's actual tuple codes. -/
def literalEquivalence : PredicateCategory 𝗧𝗔 ≌ NumericalTuples.Object :=
  CategoryTheory.Equivalence.mk (E).functor literalInverse literalUnit literalCounit

theorem literalEquivalence_functor : literalEquivalence.functor = (E).functor := rfl

theorem literalEquivalence_inverse_obj (C : NumericalTuples.Object) :
    literalEquivalence.inverse.obj C = NumericalCoordinates.codedPredicate C := rfl

theorem literalEquivalence_counit (C : NumericalTuples.Object) :
    literalEquivalence.counitIso.app C = NumericalCoordinates.coefficientIso C := rfl

end CategoricalEssentialIncompleteness.V46.NumericalNamed
