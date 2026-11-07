/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46NumericalCoordinatesValues

/-! # Values obtained from proved operation and literal-coordinate squares -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
namespace CategoricalEssentialIncompleteness.V46.NumericalNamed

theorem conjugate_operation {K : Type} [Category K]
    {A B A' B' A₀ B₀ : K} (f : A ⟶ B) (g : A' ⟶ B')
    (i : A ≅ A') (j : B ≅ B') (p : A ≅ A₀) (q : B ≅ B₀)
    (hf : f ≫ j.hom = i.hom ≫ g) :
    g ≫ (j.symm ≪≫ q).hom =
      (i.symm ≪≫ p).hom ≫ (p.inv ≫ f ≫ q.hom) := by
  have h := congrArg (fun k => k ≫ j.inv ≫ q.hom) hf
  simp only [Category.assoc, Iso.hom_inv_id_assoc] at h
  apply (cancel_epi i.hom).mp
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.hom_inv_id_assoc]
  exact h.symm

/-- The code square and the standard source value equation have already
been proved when this lemma is specialized to a concrete operation. -/
theorem predicate_operation_value {C D : PredicateCategory 𝗧𝗔}
    {X Y : NumericalTuples.Object} (f : C ⟶ D) (g : X ⟶ Y)
    (i : X ≅ NumericalCoordinates.predicateObject C)
    (j : Y ≅ NumericalCoordinates.predicateObject D)
    (hf : g ≫ j.hom = i.hom ≫ NumericalCoordinates.predicateMap f)
    {Z : Type} (value : PredicateInterpretation.Obj ℕ D → Z)
    (output : PredicateInterpretation.Obj ℕ C → Z)
    (hsource : ∀ a, value ((PredicateInterpretation.functor 𝗧𝗔 ℕ).map f a) = output a)
    (x : NumericalTuples.Point X) :
    value (j.hom.toFun (g.toFun x)) = output (i.hom.toFun x) := by
  exact (congrArg value (congrArg (fun h => h.toFun x) hf)).trans
    ((congrArg value (NumericalCoordinates.predicateMap_value f (i.hom.toFun x))).trans
      (hsource (i.hom.toFun x)))

end CategoricalEssentialIncompleteness.V46.NumericalNamed
