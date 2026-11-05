/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46SyntacticListsEquivalence
import CategoricalEssentialIncompleteness.V46CategoricalSubstitutionIdentityParameters

/-! # Constant-family comparisons over an equivalence -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v₁ v₂ u₁ u₂
open CategoryTheory CategoryTheory.Limits

namespace CategoricalEssentialIncompleteness.V46.SyntacticSyntax.Transport
open SyntacticLists.Transport

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
variable [Regular C] [FinitaryExtensive C] [Regular D] [FinitaryExtensive D]
variable (E : C ≌ D) {P : C} {Q : D} (b : E.functor.obj P ≅ Q)

/-- The slice equivalence compares constant families naturally in the
coefficient or recursive carrier, using the actual product comparison. -/
def familyNaturalIso :
    constantFamilyFunctor P ⋙ (sliceEquivalence E b).functor ≅
      E.functor ⋙ constantFamilyFunctor Q := by
  refine NatIso.ofComponents (familyComparison E b) ?_
  intro X Y f
  apply Over.OverMorphism.ext
  apply prod.hom_ext
  · exact (Over.w _).trans (Over.w _).symm
  · change (E.functor.map (prod.map (𝟙 P) f) ≫
        (familyComparison E b Y).hom.left) ≫ prod.snd =
      ((familyComparison E b X).hom.left ≫ prod.map (𝟙 Q) (E.functor.map f)) ≫ prod.snd
    simp only [Category.assoc, prod.map_snd]
    erw [familyComparison_snd, ← E.functor.map_comp,
      prod.map_snd, E.functor.map_comp]
    erw [← Category.assoc, familyComparison_snd]

omit [FinitaryExtensive C] [FinitaryExtensive D] in
/-- The terminal comparison square needs only terminal uniqueness;
it does not invert a constant-family comparison. -/
theorem family_unit :
    terminalComparison (sliceEquivalence E b).functor ≫ constantUnitComparison Q =
      (sliceEquivalence E b).functor.map (constantUnitComparison P) ≫
        (familyComparison E b (⊤_ C)).hom ≫
          (constantFamilyFunctor Q).map (terminalComparison E.functor) := by
  apply Over.OverMorphism.ext
  apply prod.hom_ext
  · exact (Over.w _).trans (Over.w _).symm
  · exact terminalIsTerminal.hom_ext _ _

omit [FinitaryExtensive C] [FinitaryExtensive D] in
/-- The product square follows from naturality of the universal product
comparison. In particular, it compares the actual parameter projections. -/
theorem family_product (X Y : C) :
    prodComparison (sliceEquivalence E b).functor
        (constantFamily P X) (constantFamily P Y) ≫
      prod.map (familyComparison E b X).hom (familyComparison E b Y).hom ≫
        constantProductComparison Q (E.functor.obj X) (E.functor.obj Y) =
      (sliceEquivalence E b).functor.map (constantProductComparison P X Y) ≫
        (familyComparison E b (X ⨯ Y)).hom ≫
          (constantFamilyFunctor Q).map (prodComparison E.functor X Y) := by
  apply (cancel_mono
    (prodComparison (constantFamilyFunctor Q) (E.functor.obj X) (E.functor.obj Y))).mp
  simp only [Category.assoc,
    SyntaxParameterChange.constant_comparison_prodComparison, Category.comp_id]
  have hn := prodComparison_natural_of_natTrans (familyNaturalIso E b).hom
    (A := X) (B := Y)
  rw [prodComparison_comp, prodComparison_comp] at hn
  change (familyComparison E b (X ⨯ Y)).hom ≫
      ((constantFamilyFunctor Q).map (prodComparison E.functor X Y) ≫
        prodComparison (constantFamilyFunctor Q) (E.functor.obj X) (E.functor.obj Y)) =
    ((sliceEquivalence E b).functor.map
        (prodComparison (constantFamilyFunctor P) X Y) ≫
      prodComparison (sliceEquivalence E b).functor
        (constantFamily P X) (constantFamily P Y)) ≫
      prod.map (familyComparison E b X).hom (familyComparison E b Y).hom at hn
  rw [hn]
  simp only [Category.assoc]
  rw [← Category.assoc, ← Functor.map_comp,
    SyntaxParameterChange.constant_comparison_prodComparison,
    (sliceEquivalence E b).functor.map_id, Category.id_comp]

/-- Coproduct coherence uses preserved coproducts of the equivalence.
No inverse of the constant-family coproduct comparison is used. -/
theorem family_sum (X Y : C) :
    inv (coprodComparison (sliceEquivalence E b).functor
      (constantFamily P X) (constantFamily P Y)) ≫
        coprod.map (familyComparison E b X).hom (familyComparison E b Y).hom ≫
          constantCoproductComparison Q (E.functor.obj X) (E.functor.obj Y) =
      (sliceEquivalence E b).functor.map (constantCoproductComparison P X Y) ≫
        (familyComparison E b (X ⨿ Y)).hom ≫
          (constantFamilyFunctor Q).map (inv (coprodComparison E.functor X Y)) := by
  apply (cancel_epi (coprodComparison (sliceEquivalence E b).functor
    (constantFamily P X) (constantFamily P Y))).mp
  rw [IsIso.hom_inv_id_assoc]
  apply coprod.hom_ext
  · simp only [coprod.inl_map_assoc, constantCoproductComparison,
      coprod.inl_desc, coprodComparison_inl_assoc]
    rw [← (sliceEquivalence E b).functor.map_comp_assoc, coprod.inl_desc]
    erw [(familyNaturalIso E b).hom.naturality_assoc (coprod.inl : X ⟶ X ⨿ Y)]
    simp only [Functor.comp_map, ← Functor.map_comp, map_inl_inv_coprodComparison]
    rfl
  · simp only [coprod.inr_map_assoc, constantCoproductComparison,
      coprod.inr_desc, coprodComparison_inr_assoc]
    rw [← (sliceEquivalence E b).functor.map_comp_assoc, coprod.inr_desc]
    erw [(familyNaturalIso E b).hom.naturality_assoc (coprod.inr : Y ⟶ X ⨿ Y)]
    simp only [Functor.comp_map, ← Functor.map_comp, map_inr_inv_coprodComparison]
    rfl

omit [FinitaryExtensive C] [FinitaryExtensive D] in
/-- Product coherence also allows arbitrary changes of the two
coefficient objects after applying the equivalence. -/
theorem family_product_map {X Y : C} {X' Y' : D}
    (u : E.functor.obj X ⟶ X') (v : E.functor.obj Y ⟶ Y') :
    prodComparison (sliceEquivalence E b).functor
        (constantFamily P X) (constantFamily P Y) ≫
      prod.map ((familyComparison E b X).hom ≫ (constantFamilyFunctor Q).map u)
        ((familyComparison E b Y).hom ≫ (constantFamilyFunctor Q).map v) ≫
          constantProductComparison Q X' Y' =
      (sliceEquivalence E b).functor.map (constantProductComparison P X Y) ≫
        (familyComparison E b (X ⨯ Y)).hom ≫
          (constantFamilyFunctor Q).map (prodComparison E.functor X Y ≫ prod.map u v) := by
  calc
    _ = (prodComparison (sliceEquivalence E b).functor
        (constantFamily P X) (constantFamily P Y) ≫
        prod.map (familyComparison E b X).hom (familyComparison E b Y).hom ≫
        constantProductComparison Q (E.functor.obj X) (E.functor.obj Y)) ≫
          (constantFamilyFunctor Q).map (prod.map u v) := by
      rw [← prod.map_map]
      simp only [Category.assoc, constantProductComparison_natural]
    _ = _ := by
      rw [family_product, Functor.map_comp]
      simp only [Category.assoc]

/-- The corresponding coproduct square uses only functoriality and the
universal coproduct injections, including when a coefficient is initial. -/
theorem family_sum_map {X Y : C} {X' Y' : D}
    (u : E.functor.obj X ⟶ X') (v : E.functor.obj Y ⟶ Y') :
    inv (coprodComparison (sliceEquivalence E b).functor
        (constantFamily P X) (constantFamily P Y)) ≫
      coprod.map ((familyComparison E b X).hom ≫ (constantFamilyFunctor Q).map u)
        ((familyComparison E b Y).hom ≫ (constantFamilyFunctor Q).map v) ≫
          constantCoproductComparison Q X' Y' =
      (sliceEquivalence E b).functor.map (constantCoproductComparison P X Y) ≫
        (familyComparison E b (X ⨿ Y)).hom ≫
          (constantFamilyFunctor Q).map
            (inv (coprodComparison E.functor X Y) ≫ coprod.map u v) := by
  calc
    _ = (inv (coprodComparison (sliceEquivalence E b).functor
        (constantFamily P X) (constantFamily P Y)) ≫
        coprod.map (familyComparison E b X).hom (familyComparison E b Y).hom ≫
        constantCoproductComparison Q (E.functor.obj X) (E.functor.obj Y)) ≫
          (constantFamilyFunctor Q).map (coprod.map u v) := by
      rw [← coprod.map_map]
      simp only [Category.assoc, constantCoproductComparison_natural]
    _ = _ := by
      rw [family_sum, Functor.map_comp]
      simp only [Category.assoc]

end CategoricalEssentialIncompleteness.V46.SyntacticSyntax.Transport
