/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SyntacticSyntaxPolynomialTransport

/-! # Polynomial transport commutes with the actual parameter comparison -/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v₁ v₂ u₁ u₂ w
open CategoryTheory CategoryTheory.Limits

namespace CategoricalEssentialIncompleteness.V46.SyntacticSyntax.Transport
open SyntacticLists.Transport

variable {I : Type w} {C : Type u₁} {D : Type u₂}
variable [Category.{v₁} C] [Category.{v₂} D]
variable [Regular C] [FinitaryExtensive C] [Regular D] [FinitaryExtensive D]
variable (E : C ≌ D) {P : C} {Q : D} (b : E.functor.obj P ≅ Q)
variable (f : I → C) (g : I → D) (χ : ∀ i, E.functor.obj (f i) ≅ g i)

theorem parameterComponent_product (a c : SyntaxPolynomial I) (X : C × C) :
    (parameterComponent E b f g χ (.product a c) X).hom =
      prodComparison (sliceEquivalence E b).functor
        (((a.mapCoefficients f).withParameters P).eval.obj
          (constantFamily P X.1, constantFamily P X.2))
        (((c.mapCoefficients f).withParameters P).eval.obj
          (constantFamily P X.1, constantFamily P X.2)) ≫
        prod.map (parameterComponent E b f g χ a X).hom
          (parameterComponent E b f g χ c X).hom := by
  change (prodComparison _ _ _ ≫ prod.map _ _) ≫ prod.map _ _ = _
  rw [Category.assoc, prod.map_map]
  rfl

theorem parameterComponent_sum (a c : SyntaxPolynomial I) (X : C × C) :
    (parameterComponent E b f g χ (.sum a c) X).hom =
      inv (coprodComparison (sliceEquivalence E b).functor
        (((a.mapCoefficients f).withParameters P).eval.obj
          (constantFamily P X.1, constantFamily P X.2))
        (((c.mapCoefficients f).withParameters P).eval.obj
          (constantFamily P X.1, constantFamily P X.2))) ≫
        coprod.map (parameterComponent E b f g χ a X).hom
          (parameterComponent E b f g χ c X).hom := by
  change (inv (coprodComparison _ _ _) ≫ coprod.map _ _) ≫ coprod.map _ _ = _
  rw [Category.assoc, coprod.map_map]
  rfl

/-- The full comparison square is proved structurally. Its left edge
is the actual parameterComparison used by the manuscript interface,
and its right edge is the actual comparison in the target category. -/
theorem parameterComponent_comparison (p : SyntaxPolynomial I) (X : C × C) :
    (parameterComponent E b f g χ p X).hom ≫
      SyntaxPolynomial.parameterComparison Q
        ((E.prod E).functor.obj X) (p.mapCoefficients g) =
      (sliceEquivalence E b).functor.map
          (SyntaxPolynomial.parameterComparison P X (p.mapCoefficients f)) ≫
        (familyComparison E b ((p.mapCoefficients f).eval.obj X)).hom ≫
          (constantFamilyFunctor Q).map
            (SyntaxPolynomialTransport.component E f g χ p X).hom := by
  induction p with
  | term =>
      change (𝟙 _ ≫ (familyComparison E b X.1).hom) ≫ 𝟙 _ =
        (sliceEquivalence E b).functor.map (𝟙 _) ≫
          (familyComparison E b X.1).hom ≫ (constantFamilyFunctor Q).map (𝟙 _)
      rw [(sliceEquivalence E b).functor.map_id, (constantFamilyFunctor Q).map_id]
      simp only [Category.id_comp, Category.comp_id]
      erw [Category.comp_id]
  | formula =>
      change (𝟙 _ ≫ (familyComparison E b X.2).hom) ≫ 𝟙 _ =
        (sliceEquivalence E b).functor.map (𝟙 _) ≫
          (familyComparison E b X.2).hom ≫ (constantFamilyFunctor Q).map (𝟙 _)
      rw [(sliceEquivalence E b).functor.map_id, (constantFamilyFunctor Q).map_id]
      simp only [Category.id_comp, Category.comp_id]
      erw [Category.comp_id]
  | coefficient i =>
      change (((familyComparison E b (f i)).hom ≫ (constantFamilyFunctor Q).map
        (χ i).hom) ≫ 𝟙 _) ≫ 𝟙 _ = (sliceEquivalence E b).functor.map (𝟙 _) ≫
          (familyComparison E b (f i)).hom ≫ (constantFamilyFunctor Q).map (χ i).hom
      rw [(sliceEquivalence E b).functor.map_id]
      simp only [Category.id_comp, Category.comp_id]
  | unit =>
      change (terminalComparison (sliceEquivalence E b).functor ≫ 𝟙 _) ≫
          constantUnitComparison Q = _
      rw [Category.comp_id]
      exact family_unit E b
  | product a c ia ic =>
      rw [parameterComponent_product]
      change (prodComparison _ _ _ ≫ prod.map _ _) ≫
          (prod.map _ _ ≫ constantProductComparison Q _ _) =
        (sliceEquivalence E b).functor.map
          (prod.map _ _ ≫ constantProductComparison P _ _) ≫
          (familyComparison E b _).hom ≫
          (constantFamilyFunctor Q).map
            (prodComparison E.functor _ _ ≫ prod.map _ _)
      rw [Category.assoc, ← Category.assoc (prod.map _ _), prod.map_map, ia, ic,
        ← prod.map_map, ← Category.assoc, ← Category.assoc,
        ← prodComparison_natural]
      simp only [Category.assoc]
      rw [family_product_map, ← Category.assoc,
        ← (sliceEquivalence E b).functor.map_comp]
  | sum a c ia ic =>
      rw [parameterComponent_sum]
      change (inv (coprodComparison _ _ _) ≫ coprod.map _ _) ≫
          (coprod.map _ _ ≫ constantCoproductComparison Q _ _) =
        (sliceEquivalence E b).functor.map
          (coprod.map _ _ ≫ constantCoproductComparison P _ _) ≫
          (familyComparison E b _).hom ≫
          (constantFamilyFunctor Q).map
            (inv (coprodComparison E.functor _ _) ≫ coprod.map _ _)
      rw [Category.assoc, ← Category.assoc (coprod.map _ _), coprod.map_map, ia, ic,
        ← coprod.map_map, ← Category.assoc, ← Category.assoc,
        coprodComparison_inv_natural]
      simp only [Category.assoc]
      rw [family_sum_map, ← Category.assoc,
        ← (sliceEquivalence E b).functor.map_comp]

end CategoricalEssentialIncompleteness.V46.SyntacticSyntax.Transport
