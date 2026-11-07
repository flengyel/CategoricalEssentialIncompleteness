/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46NumericalArithmeticGraphs
import CategoricalEssentialIncompleteness.V46NumericalCoordinatesValues

/-! # The arithmetic graph-extension functor with unchanged carrier formulas -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
namespace CategoricalEssentialIncompleteness.V46.NumericalArithmetic

/-- The source graph, its input coordinates and its output coordinates
are unchanged. The target theory supplies the weakened proof terms. -/
def extended {C D : PredicateCategory 𝗣𝗔} (f : C ⟶ D) :
    @Quiver.Hom (PredicateCategory 𝗧𝗔) inferInstance C D :=
  representedArrow 𝗧𝗔 (liftGraph (chosenGraph 𝗣𝗔 f))

section Models
variable (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗧𝗔]
local instance : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 := models_of_subtheory (U := 𝗧𝗔) inferInstance

/-- This graph comparison holds throughout the target theory's models. -/
theorem extended_relation {C D : PredicateCategory 𝗣𝗔} (f : C ⟶ D) (x y : M) :
    relation 𝗧𝗔 (extended f) M x y ↔ relation 𝗣𝗔 f M x y :=
  (relation_class 𝗧𝗔 (liftGraph (chosenGraph 𝗣𝗔 f)) M x y).trans
    (chosenGraph_eval 𝗣𝗔 f M x y)

theorem extended_value {C D : PredicateCategory 𝗣𝗔} (f : C ⟶ D)
    (x : PredicateInterpretation.Obj M C) :
    (PredicateInterpretation.functor 𝗧𝗔 M).map (extended f) x =
      (PredicateInterpretation.functor 𝗣𝗔 M).map f x := by
  apply (SyntacticLists.map_eq_iff_relation 𝗧𝗔 M (extended f) x _).mpr
  apply (extended_relation M f x.val _).mpr
  exact (SyntacticLists.map_eq_iff_relation 𝗣𝗔 M f x
    ((PredicateInterpretation.functor 𝗣𝗔 M).map f x)).mp rfl

end Models

/-- Theory extension is a functor because the same graph formulas
satisfy the identity and composition equations in every target model. -/
def theoryExtension : PredicateCategory 𝗣𝗔 ⥤ PredicateCategory 𝗧𝗔 where
  obj C := C
  map := extended
  map_id C := by
    apply hom_ext 𝗧𝗔
    intro M _ _ x y
    let _ : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 := models_of_subtheory (U := 𝗧𝗔) inferInstance
    simp only [extended_relation,relation_id]
  map_comp f g := by
    apply hom_ext 𝗧𝗔
    intro M _ _ x y
    let _ : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 := models_of_subtheory (U := 𝗧𝗔) inferInstance
    simp only [extended_relation,relation_comp]

theorem theoryExtension_class {C D : PredicateCategory 𝗣𝗔} (f : GraphMorphism 𝗣𝗔 C D) :
    theoryExtension.map (representedArrow 𝗣𝗔 f) = representedArrow 𝗧𝗔 (liftGraph f) := by
  apply hom_ext 𝗧𝗔
  intro M _ _ x y
  let _ : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 := models_of_subtheory (U := 𝗧𝗔) inferInstance
  exact (extended_relation M (representedArrow 𝗣𝗔 f) x y).trans
    ((relation_class 𝗣𝗔 f M x y).trans (relation_class 𝗧𝗔 (liftGraph f) M x y).symm)

theorem theoryExtension_value {C D : PredicateCategory 𝗣𝗔} (f : C ⟶ D)
    (x : PredicateInterpretation.Obj ℕ C) :
    (PredicateInterpretation.functor 𝗧𝗔 ℕ).map (theoryExtension.map f) x =
      (PredicateInterpretation.functor 𝗣𝗔 ℕ).map f x := extended_value ℕ f x

private theorem coordinate_id (C : PredicateCategory 𝗧𝗔) :
    NumericalCoordinates.predicateMap (𝟙 C) = 𝟙 (NumericalCoordinates.predicateObject C) := by
  unfold NumericalCoordinates.predicateMap
  erw [CategoryTheory.Functor.map_id]
  simp only [Category.id_comp,Iso.inv_hom_id]

/-- The computable unary numerical presentation of the actual PA
predicate category, with the same standard carrier coordinates. -/
def numericalInterpretation : PredicateCategory 𝗣𝗔 ⥤ NumericalTuples.Object where
  obj C := NumericalCoordinates.predicateObject (C : PredicateCategory 𝗧𝗔)
  map f := NumericalCoordinates.predicateMap (theoryExtension.map f)
  map_id C := by
    change NumericalCoordinates.predicateMap (theoryExtension.map (𝟙 C)) =
      𝟙 (NumericalCoordinates.predicateObject (theoryExtension.obj C))
    rw [CategoryTheory.Functor.map_id]
    exact coordinate_id (theoryExtension.obj C)
  map_comp f g := by simp [NumericalCoordinates.predicateMap,Category.assoc]

theorem numericalInterpretation_value {C D : PredicateCategory 𝗣𝗔} (f : C ⟶ D)
    (x : NumericalTuples.Point (numericalInterpretation.obj C)) :
    (numericalInterpretation.map f).toFun x =
      (PredicateInterpretation.functor 𝗣𝗔 ℕ).map f x :=
  (NumericalCoordinates.predicateMap_value (theoryExtension.map f) x).trans
    (theoryExtension_value f x)

end CategoricalEssentialIncompleteness.V46.NumericalArithmetic
