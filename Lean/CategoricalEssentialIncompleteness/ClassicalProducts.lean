/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.ClassicalProgramBase

/-! # Restriction products for extensional partial recursive arrows -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open CategoryTheory CategoryTheory.RestrictionCategory
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open PCategoryStruct

namespace CategoricalEssentialIncompleteness.LocalConnectedness.ClassicalPrograms

open SyntacticModel

theorem exists_source {X Y : Rec} (f : X ⟶ Y) :
    ∃ g : X.base ⟶ Y.base, Q.map g = f :=
  FunctorImage.quotient_map_surjective standardFunctor X.base Y.base f

instance : PCategoryStruct Rec where
  nearProd X Y := ⟨nearProd X.base Y.base⟩
  nearProd_map f g := ⟨PFun.prodMap f.val g.val,
    ⟨nearProd_map (FunctorImage.representative standardFunctor f)
      (FunctorImage.representative standardFunctor g), by
      rw [model_map_product, FunctorImage.map_representative, FunctorImage.map_representative]⟩⟩
  diag X := Q.map (diag X.base)
  p0 X Y := Q.map (p0 X.base Y.base)
  p1 X Y := Q.map (p1 X.base Y.base)

@[simp] theorem Q_obj_base (X : Rec) : Q.obj X.base = X := rfl

@[simp] theorem Q_product_obj
    (X Y : FailureOfComposition.TypedProgramCategory.CodedProgramCategory 𝗣𝗔) :
    Q.obj (nearProd X Y) = nearProd (Q.obj X) (Q.obj Y) := rfl

@[simp] theorem Q_product {W X Y Z : FailureOfComposition.TypedProgramCategory.CodedProgramCategory 𝗣𝗔}
    (f : W ⟶ X) (g : Y ⟶ Z) : Q.map (nearProd_map f g) = nearProd_map (Q.map f) (Q.map g) :=
  FunctorImage.Hom.ext (model_map_product 𝗣𝗔 ℕ f g)

@[simp] theorem Q_diag (X : FailureOfComposition.TypedProgramCategory.CodedProgramCategory 𝗣𝗔) :
    Q.map (diag X) = diag (Q.obj X) := rfl
@[simp] theorem Q_first (X Y : FailureOfComposition.TypedProgramCategory.CodedProgramCategory 𝗣𝗔) :
    Q.map (p0 X Y) = p0 (Q.obj X) (Q.obj Y) := rfl
@[simp] theorem Q_second (X Y : FailureOfComposition.TypedProgramCategory.CodedProgramCategory 𝗣𝗔) :
    Q.map (p1 X Y) = p1 (Q.obj X) (Q.obj Y) := rfl

@[simp] theorem Q_assoc (X Y Z : FailureOfComposition.TypedProgramCategory.CodedProgramCategory 𝗣𝗔) :
    Q.map (PCategoryStruct.assoc X Y Z) = PCategoryStruct.assoc (Q.obj X) (Q.obj Y) (Q.obj Z) := by
  simp only [PCategoryStruct.assoc, partialPairing, Functor.map_comp, Q_product,
    Q_diag, Q_first, Q_second]
  rfl

@[simp] theorem Q_swap (X Y : FailureOfComposition.TypedProgramCategory.CodedProgramCategory 𝗣𝗔) :
    Q.map (PCategoryStruct.swap X Y) = PCategoryStruct.swap (Q.obj X) (Q.obj Y) := by
  simp only [PCategoryStruct.swap, partialPairing, Functor.map_comp, Q_product,
    Q_diag, Q_first, Q_second]
  rfl

instance : PCategory Rec where
  nearProd_id X Y := by
    simpa [Q_obj_base, Q_product_obj, Q.map_id, Q_product] using
      congrArg (fun f => Q.map f) (PCategory.nearProd_id X.base Y.base)
  nearProd_comp f g h k := by
    obtain ⟨f, rfl⟩ := exists_source f
    obtain ⟨g, rfl⟩ := exists_source g
    obtain ⟨h, rfl⟩ := exists_source h
    obtain ⟨k, rfl⟩ := exists_source k
    simpa [Q_obj_base, Q_product_obj, Functor.map_comp, Q_product] using
      congrArg (fun f => Q.map f) (PCategory.nearProd_comp f g h k)
  diag_p0 X := by
    simpa [Q_obj_base, Q_product_obj, Q.map_comp, Q.map_id, Q_diag, Q_first] using
      congrArg (fun f => Q.map f) (PCategory.diag_p0 X.base)
  diag_p1 X := by
    simpa [Q_obj_base, Q_product_obj, Q.map_comp, Q.map_id, Q_diag, Q_second] using
      congrArg (fun f => Q.map f) (PCategory.diag_p1 X.base)
  diag_p0_p1 X Y := by
    simpa [Q_obj_base, Q_product_obj, Q.map_comp, Q.map_id, Q_product, Q_diag, Q_first, Q_second] using
      congrArg (fun f => Q.map f) (PCategory.diag_p0_p1 X.base Y.base)
  p0_p0 X Y Z := by
    simpa [Q_obj_base, Q_product_obj, Q.map_comp, Q.map_id, Q_product, Q_first] using
      congrArg (fun f => Q.map f) (PCategory.p0_p0 X.base Y.base Z.base)
  p0_p1 X Y Z := by
    simpa [Q_obj_base, Q_product_obj, Q.map_comp, Q.map_id, Q_product, Q_first, Q_second] using
      congrArg (fun f => Q.map f) (PCategory.p0_p1 X.base Y.base Z.base)
  p1_p0 X Y Z := by
    simpa [Q_obj_base, Q_product_obj, Q.map_comp, Q.map_id, Q_product, Q_first, Q_second] using
      congrArg (fun f => Q.map f) (PCategory.p1_p0 X.base Y.base Z.base)
  p1_p1 X Y Z := by
    simpa [Q_obj_base, Q_product_obj, Q.map_comp, Q.map_id, Q_product, Q_second] using
      congrArg (fun f => Q.map f) (PCategory.p1_p1 X.base Y.base Z.base)
  diag_nat f := by
    obtain ⟨f, rfl⟩ := exists_source f
    simpa [Q_obj_base, Q_product_obj, Functor.map_comp, Q_product, Q_diag] using
      congrArg (fun f => Q.map f) (PCategory.diag_nat f)
  p0_nat {X Y Z} f := by
    obtain ⟨f, rfl⟩ := exists_source f
    simpa [Q_obj_base, Q_product_obj, Q.map_comp, Q.map_id, Q_product, Q_first] using
      congrArg (fun f => Q.map f) (PCategory.p0_nat (Z := Z.base) f)
  p1_nat {X Y Z} f := by
    obtain ⟨f, rfl⟩ := exists_source f
    simpa [Q_obj_base, Q_product_obj, Q.map_comp, Q.map_id, Q_product, Q_second] using
      congrArg (fun f => Q.map f) (PCategory.p1_nat (Z := Z.base) f)
  assoc_nat f g h := by
    obtain ⟨f, rfl⟩ := exists_source f
    obtain ⟨g, rfl⟩ := exists_source g
    obtain ⟨h, rfl⟩ := exists_source h
    simpa [Q_obj_base, Q_product_obj, Functor.map_comp, Q_product, Q_assoc] using
      congrArg (fun f => Q.map f) (PCategory.assoc_nat f g h)
  swap_nat f g := by
    obtain ⟨f, rfl⟩ := exists_source f
    obtain ⟨g, rfl⟩ := exists_source g
    simpa [Q_obj_base, Q_product_obj, Functor.map_comp, Q_product, Q_swap] using
      congrArg (fun f => Q.map f) (PCategory.swap_nat f g)

end CategoricalEssentialIncompleteness.LocalConnectedness.ClassicalPrograms
