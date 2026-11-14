/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SliceBaseChangeGeometry

/-! # The ordinary-slice coordinates of the evaluation retraction -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u
open CategoryTheory CategoryTheory.Limits

namespace CategoricalEssentialIncompleteness.V46.SliceBaseChangeGeometry

variable {C : Type u} [Category.{v} C] [HasFiniteLimits C] [HasFiniteCoproducts C]
variable {Z U : C} (point : Z ⟶ U) (hZ : IsTerminal Z)

def productFiberIso (S : C) : pullback (prod.fst : U ⨯ S ⟶ U) point ≅ S where
  hom := pullback.fst (prod.fst : U ⨯ S ⟶ U) point ≫ prod.snd
  inv := pullback.lift (f := (prod.fst : U ⨯ S ⟶ U)) (g := point)
    (prod.lift (hZ.from S ≫ point) (𝟙 S)) (hZ.from S) (by simp)
  hom_inv_id := by
    apply pullback.hom_ext
    · simp only [Category.assoc, pullback.lift_fst]
      apply prod.hom_ext
      · simp only [Category.assoc, prod.lift_fst]
        rw [← Category.assoc]
        have ht : (pullback.fst (prod.fst : U ⨯ S ⟶ U) point ≫ prod.snd) ≫ hZ.from S =
            pullback.snd (prod.fst : U ⨯ S ⟶ U) point := hZ.hom_ext _ _
        rw [← Category.assoc _ (hZ.from S) point, ht]
        simpa only [Category.id_comp] using
          (pullback.condition (f := (prod.fst : U ⨯ S ⟶ U)) (g := point)).symm
      · simp
    · exact hZ.hom_ext _ _
  inv_hom_id := by simp

def evaluationConstantIso (S : C) :
    (evaluation point hZ).obj ((constantFamilyFunctor U).obj S) ≅ S :=
  productFiberIso point hZ S

omit [HasFiniteCoproducts C] in
@[reassoc] theorem evaluationConstantIso_inv_fst (S : C) :
    (evaluationConstantIso point hZ S).inv ≫ pullback.fst _ _ =
      prod.lift (hZ.from S ≫ point) (𝟙 S) := by
  change (productFiberIso point hZ S).inv ≫ pullback.fst (prod.fst : U ⨯ S ⟶ U) point = _
  simp [productFiberIso]

def ordinaryRetraction : constantFamilyFunctor U ⋙ evaluation point hZ ≅ 𝟭 C :=
  NatIso.ofComponents (evaluationConstantIso point hZ) (by
    intro S T f
    simp [evaluation, evaluationConstantIso, productFiberIso, Over.pullback, constantFamilyFunctor,
      constantFamily, Category.assoc])

end CategoricalEssentialIncompleteness.V46.SliceBaseChangeGeometry
