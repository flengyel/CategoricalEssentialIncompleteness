/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46PredicateInterpretationRegular
public import CategoricalEssentialIncompleteness.V46SyntacticLists
public import CategoricalEssentialIncompleteness.V46SyntacticPredicatesExtensive
public import Mathlib.CategoryTheory.Subobject.Limits
public import Mathlib.CategoryTheory.Subobject.Lattice

/-! # Empty subobjects and image witnesses in all arithmetic models -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates

namespace CategoricalEssentialIncompleteness.V46.PredicateModelSubobjects
variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]

/-- The theory proves emptiness when all its models have no carrier points. -/
theorem empty_inclusion (C : PredicateCategory T)
    (empty : ∀ (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T],
      PredicateInterpretation.Obj M C → False) :
    T ⊢ inclusionSentence C PredicateInterpretation.emptyCarrier := by
  apply complete.{0} T
  intro M _ _
  rw [models_iff, inclusionSentence_eval]
  intro x hx
  exact False.elim (empty M ⟨x, hx⟩)

/-- Emptiness is reflected from all model interpretations to initiality. -/
def initialOfModelsEmpty (C : PredicateCategory T)
    (empty : ∀ (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T],
      PredicateInterpretation.Obj M C → False) : IsInitial C :=
  IsInitial.ofUniqueHom
    (fun D => representedArrow T (GraphMorphism.inclusion (empty_inclusion T C empty)) ≫
      (PredicateInterpretation.emptyIsInitial T).to D)
    (by
      intro D f
      apply hom_ext T
      intro M _ _ x y
      exact iff_of_false
        (fun h => empty M ⟨x, (relation_support T f M x y h).1⟩)
        (fun h => empty M ⟨x, (relation_support T _ M x y h).1⟩))

/-- A subobject with no points in any model is the bottom subobject. -/
theorem eq_bot_of_models_empty {X : PredicateCategory T} (A : Subobject X)
    (empty : ∀ (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T],
      PredicateInterpretation.Obj M (A : PredicateCategory T) → False) : A = ⊥ := by
  let hI := initialOfModelsEmpty T (A : PredicateCategory T) empty
  apply le_antisymm _ bot_le
  exact Subobject.le_of_comm (hI.to (⊥ : Subobject X)) (hI.hom_ext _ _)

/-- The represented image factor has a constructed witness section. -/
theorem factorThruImage_isSplitEpi {C D : PredicateCategory T} (f : C ⟶ D) :
    IsSplitEpi (factorThruImage f) := by
  obtain ⟨g, rfl⟩ := Quotient.exists_rep f
  let e := representedArrow T g.corestriction
  let m := representedArrow T (GraphMorphism.inclusion g.imageInclusionProof)
  let : IsSplitEpi e := g.corestriction.isSplitEpi_of_surjective g.corestriction_surjective
  let i := (image.isoStrongEpiMono e m g.image_factor).symm
  have hi : i.hom ≫ m = image.ι (representedArrow T g) :=
    image.isoStrongEpiMono_inv_comp_mono e m g.image_factor
  have he : factorThruImage (representedArrow T g) ≫ i.hom = e := by
    apply (cancel_mono m).mp
    rw [Category.assoc, hi, image.fac, g.image_factor]
  have hf : factorThruImage (representedArrow T g) = e ≫ i.inv := by
    calc
      _ = (factorThruImage (representedArrow T g) ≫ i.hom) ≫ i.inv := by simp
      _ = e ≫ i.inv := by rw [he]
  erw [hf]
  infer_instance

section Models
variable (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T]

/-- Every point of the actual categorical image has a source witness. -/
theorem image_point {C D : PredicateCategory T} (f : C ⟶ D)
    (x : PredicateInterpretation.Obj M (image (C := PredicateCategory T) f)) :
    ∃ c : PredicateInterpretation.Obj M C,
      (PredicateInterpretation.functor T M).map f c =
        (PredicateInterpretation.functor T M).map (image.ι f) x := by
  let : IsSplitEpi (factorThruImage f) := factorThruImage_isSplitEpi T f
  have hs : Function.Surjective
      ((PredicateInterpretation.functor T M).map (factorThruImage f)) :=
    (epi_iff_surjective _).mp inferInstance
  obtain ⟨c, hc⟩ := hs x
  refine ⟨c, ?_⟩
  have h := congrArg ((PredicateInterpretation.functor T M).map (image.ι f)) hc
  rw [← Functor.map_comp_apply, image.fac] at h
  exact h

/-- Image witnesses respect the chosen subobject inclusion. -/
theorem imageSubobject_point {C D : PredicateCategory T} (f : C ⟶ D)
    (x : PredicateInterpretation.Obj M (imageSubobject f : PredicateCategory T)) :
    ∃ c : PredicateInterpretation.Obj M C,
      (PredicateInterpretation.functor T M).map f c =
        (PredicateInterpretation.functor T M).map (imageSubobject f).arrow x := by
  obtain ⟨c, hc⟩ := image_point T M f
    ((PredicateInterpretation.functor T M).map (imageSubobjectIso f).hom x)
  refine ⟨c, ?_⟩
  rw [← Functor.map_comp_apply, imageSubobject_arrow] at hc
  exact hc

end Models
end CategoricalEssentialIncompleteness.V46.PredicateModelSubobjects
