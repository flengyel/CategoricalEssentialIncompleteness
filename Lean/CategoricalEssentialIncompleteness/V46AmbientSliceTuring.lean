/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46AmbientPartialSlice
public import CategoricalEssentialIncompleteness.V46SliceTuringParameters

/-! # Universal computations as partial morphisms over T -/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u
open CategoryTheory CategoryTheory.RestrictionCategory PCategoryStruct RecursionCategory

namespace CategoricalEssentialIncompleteness.V46.AmbientSliceTuring

open AmbientPartialSlice

variable {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]

def constantFamily (T Q : C) : Family T :=
  ⟨nearProd T Q, p0 T Q, PCategory.p0_isTotal T Q⟩

def tensorConstant {T : C} (X : Family T) (Q : C) : Family T where
  base := nearProd X.base Q
  proj := p0 X.base Q ≫ X.proj
  total := by
    change PCategoryStruct.rst (p0 X.base Q ≫ X.proj) = 𝟙 _
    rw [PCategory.rst_comp_of_isTotal' _ X.total, PCategory.p0_isTotal]

def tensorMap {T : C} {X Y : Family T} (f : X ⟶ Y) (Q : C) :
    tensorConstant X Q ⟶ tensorConstant Y Q where
  hom := nearProd_map f.hom (𝟙 Q)
  over := by
    have hr : CategoryTheory.RestrictionCategory.rst (nearProd_map f.hom (𝟙 Q)) ≫
        p0 X.base Q = p0 X.base Q ≫ CategoryTheory.RestrictionCategory.rst f.hom := by
      change PCategoryStruct.rst (nearProd_map f.hom (𝟙 Q)) ≫ p0 X.base Q = _
      rw [PCategory.rst_nearProd_map,
        show PCategoryStruct.rst (𝟙 Q) = 𝟙 Q from rst_id Q, PCategory.p0_nat]
      rfl
    change nearProd_map f.hom (𝟙 Q) ≫ (p0 Y.base Q ≫ Y.proj) =
      CategoryTheory.RestrictionCategory.rst (nearProd_map f.hom (𝟙 Q)) ≫
        (p0 X.base Q ≫ X.proj)
    calc
      _ = (p0 X.base Q ≫ f.hom) ≫ Y.proj := by
        rw [← Category.assoc, PCategory.p0_nat]
      _ = (p0 X.base Q ≫ CategoryTheory.RestrictionCategory.rst f.hom) ≫ X.proj := by
        rw [Category.assoc, f.over, ← Category.assoc]
      _ = _ := by rw [← hr, Category.assoc]

def tensorFunctor (T Q : C) : Family T ⥤ Family T where
  obj X := tensorConstant X Q
  map f := tensorMap f Q
  map_id X := Hom.ext (PCategory.nearProd_id X.base Q)
  map_comp f g := Hom.ext (by
    change nearProd_map (f.hom ≫ g.hom) (𝟙 Q) =
      nearProd_map f.hom (𝟙 Q) ≫ nearProd_map g.hom (𝟙 Q)
    rw [PCategory.nearProd_comp, Category.id_comp])

def constantMap (T : C) {X Y : C} (f : X ⟶ Y) :
    constantFamily T X ⟶ constantFamily T Y where
  hom := nearProd_map (𝟙 T) f
  over := by
    change nearProd_map (𝟙 T) f ≫ p0 T Y =
      CategoryTheory.RestrictionCategory.rst (nearProd_map (𝟙 T) f) ≫ p0 T X
    rw [PCategory.p0_proj_domain_id]
    change _ = PCategoryStruct.rst (nearProd_map (𝟙 T) f) ≫ p0 T X
    rw [PCategory.rst_nearProd_map,
      show PCategoryStruct.rst (𝟙 T) = 𝟙 T from rst_id T]

def reassociate (T Q : C) : tensorConstant (constantFamily T Q) Q ⟶
    constantFamily T (nearProd Q Q) where
  hom := assoc T Q Q
  over := by
    have ht : isTotal (assoc T Q Q) :=
      CategoricalEssentialIncompleteness.LocalConnectedness.total_of_comp_total
        (assoc T Q Q) (PCategory.assocInv T Q Q)
        (by rw [PCategory.assoc_assocInv]; exact rst_id _)
    change assoc T Q Q ≫ p0 T (nearProd Q Q) =
      CategoryTheory.RestrictionCategory.rst (assoc T Q Q) ≫
        (p0 (nearProd T Q) Q ≫ p0 T Q)
    rw [PCategory.assoc_p0, ht, Category.id_comp]

def evaluator (T : C) {Q : C} (τ : nearProd Q Q ⟶ Q) :
    tensorConstant (constantFamily T Q) Q ⟶ constantFamily T Q :=
  reassociate T Q ≫ constantMap T τ

def tensorFst {T : C} (X : Family T) (Q : C) : tensorConstant X Q ⟶ X :=
  ⟨p0 X.base Q, by
    change p0 X.base Q ≫ X.proj =
      PCategoryStruct.rst (p0 X.base Q) ≫ (p0 X.base Q ≫ X.proj)
    rw [PCategory.p0_isTotal, Category.id_comp]⟩

def tensorSnd {T : C} (X : Family T) (Q : C) :
    tensorConstant X Q ⟶ constantFamily T Q :=
  ⟨partialPairing (p0 X.base Q ≫ X.proj) (p1 X.base Q), by
    change partialPairing (p0 X.base Q ≫ X.proj) (p1 X.base Q) ≫ p0 T Q =
      PCategoryStruct.rst (partialPairing (p0 X.base Q ≫ X.proj) (p1 X.base Q)) ≫
        (p0 X.base Q ≫ X.proj)
    rw [PCategory.p0_partialPairing, PCategory.rst_partialPairing,
      PCategory.p1_isTotal, Category.id_comp, Category.comp_id,
      show PCategoryStruct.rst (p0 X.base Q ≫ X.proj) = 𝟙 _ from
        (tensorConstant X Q).total, Category.id_comp]⟩

theorem tensorSnd_second {T : C} (X : Family T) (Q : C) :
    (tensorSnd X Q).hom ≫ p1 T Q = p1 X.base Q := by
  change partialPairing (p0 X.base Q ≫ X.proj) (p1 X.base Q) ≫ p1 T Q = p1 X.base Q
  rw [PCategory.p1_partialPairing,
    show PCategoryStruct.rst (p0 X.base Q ≫ X.proj) = 𝟙 _ from
      (tensorConstant X Q).total, Category.id_comp]

theorem tensorFst_total {T : C} (X : Family T) (Q : C) : isTotal (tensorFst X Q) := by
  apply (AmbientPartialSlice.total_iff _).mpr
  exact PCategory.p0_isTotal X.base Q

theorem tensorSnd_total {T : C} (X : Family T) (Q : C) : isTotal (tensorSnd X Q) := by
  apply (AmbientPartialSlice.total_iff _).mpr
  change PCategoryStruct.rst (partialPairing (p0 X.base Q ≫ X.proj) (p1 X.base Q)) = 𝟙 _
  rw [PCategory.rst_partialPairing, PCategory.p1_isTotal, Category.comp_id]
  exact (tensorConstant X Q).total

def tensorPair {T Q : C} {V X : Family T} (f : V ⟶ X) (g : V ⟶ constantFamily T Q) :
    V ⟶ tensorConstant X Q where
  hom := partialPairing f.hom (g.hom ≫ p1 T Q)
  over := by
    change partialPairing f.hom (g.hom ≫ p1 T Q) ≫ (p0 X.base Q ≫ X.proj) =
      PCategoryStruct.rst (partialPairing f.hom (g.hom ≫ p1 T Q)) ≫ V.proj
    rw [← Category.assoc, PCategory.p0_partialPairing, PCategory.rst_comp_p1,
      Category.assoc, f.over, ← Category.assoc, PCategory.rst_partialPairing,
      PCategory.rst_comp_p1]
    exact congrArg (fun k => k ≫ V.proj) (rst_comm g.hom f.hom)

theorem tensorPair_restriction {T Q : C} {V X : Family T}
    (f : V ⟶ X) (g : V ⟶ constantFamily T Q) :
    rst (tensorPair f g) = rst f ≫ rst g := by
  apply Hom.ext
  change PCategoryStruct.rst (partialPairing f.hom (g.hom ≫ p1 T Q)) =
    PCategoryStruct.rst f.hom ≫ PCategoryStruct.rst g.hom
  rw [PCategory.rst_partialPairing, PCategory.rst_comp_p1]

theorem tensorPair_fst {T Q : C} {V X : Family T}
    (f : V ⟶ X) (g : V ⟶ constantFamily T Q) :
    tensorPair f g ≫ tensorFst X Q = rst g ≫ f := by
  apply Hom.ext
  change partialPairing f.hom (g.hom ≫ p1 T Q) ≫ p0 X.base Q =
    PCategoryStruct.rst g.hom ≫ f.hom
  rw [PCategory.p0_partialPairing, PCategory.rst_comp_p1]

theorem tensorPair_snd {T Q : C} {V X : Family T}
    (f : V ⟶ X) (g : V ⟶ constantFamily T Q) :
    tensorPair f g ≫ tensorSnd X Q = rst f ≫ g := by
  dsimp only [constantFamily] at g
  apply Hom.ext
  change partialPairing f.hom (g.hom ≫ p1 T Q) ≫
    partialPairing (p0 X.base Q ≫ X.proj) (p1 X.base Q) =
      CategoryTheory.RestrictionCategory.rst f.hom ≫ g.hom
  rw [PCategory.comp_partialPairing]
  apply Eq.symm
  apply PCategory.eq_partialPairing_of_proj
  · calc
      _ = (CategoryTheory.RestrictionCategory.rst f.hom ≫
          CategoryTheory.RestrictionCategory.rst g.hom) ≫ V.proj := by
        simpa only [Category.assoc] using congrArg
          (fun k => CategoryTheory.RestrictionCategory.rst f.hom ≫ k) g.over
      _ = (CategoryTheory.RestrictionCategory.rst g.hom ≫
          CategoryTheory.RestrictionCategory.rst f.hom) ≫ V.proj :=
        congrArg (fun k => k ≫ V.proj) (rst_comm f.hom g.hom)
      _ = (CategoryTheory.RestrictionCategory.rst g.hom ≫ f.hom) ≫ X.proj := by
        simpa only [Category.assoc] using (congrArg
          (fun k => CategoryTheory.RestrictionCategory.rst g.hom ≫ k) f.over).symm
      _ = _ := by
        rw [← Category.assoc, PCategory.p0_partialPairing, PCategory.rst_comp_p1]
        rfl
  · rw [PCategory.p1_partialPairing, Category.assoc]
    rfl

theorem tensorPair_proj {T Q : C} {V X : Family T} (h : V ⟶ tensorConstant X Q) :
    tensorPair (h ≫ tensorFst X Q) (h ≫ tensorSnd X Q) = h := by
  apply Hom.ext
  change partialPairing (h.hom ≫ p0 X.base Q)
    ((h.hom ≫ (tensorSnd X Q).hom) ≫ p1 T Q) = h.hom
  rw [Category.assoc, tensorSnd_second, PCategory.partialPairing_proj]

theorem tensorMap_eq_pair {T : C} {X Y : Family T} (f : X ⟶ Y) (Q : C) :
    tensorMap f Q = tensorPair (tensorFst X Q ≫ f) (tensorSnd X Q) := by
  apply Hom.ext
  change nearProd_map f.hom (𝟙 Q) =
    partialPairing (p0 X.base Q ≫ f.hom) ((tensorSnd X Q).hom ≫ p1 T Q)
  rw [tensorSnd_second, PCategory.nearProd_eq_partialPairing, Category.comp_id]

theorem tensorFunctor_restriction {T Q : C} {X Y : Family T} (f : X ⟶ Y) :
    (tensorFunctor T Q).map (rst f) = rst ((tensorFunctor T Q).map f) := by
  apply Hom.ext
  change nearProd_map (PCategoryStruct.rst f.hom) (𝟙 Q) =
    PCategoryStruct.rst (nearProd_map f.hom (𝟙 Q))
  rw [PCategory.rst_nearProd_map, show PCategoryStruct.rst (𝟙 Q) = 𝟙 Q from rst_id Q]

theorem tensor_hom_ext {T Q : C} {V X : Family T} {h k : V ⟶ tensorConstant X Q}
    (h0 : h ≫ tensorFst X Q = k ≫ tensorFst X Q)
    (h1 : h ≫ tensorSnd X Q = k ≫ tensorSnd X Q) : h = k := by
  rw [← tensorPair_proj h, ← tensorPair_proj k, h0, h1]

theorem tensor_product_existsUnique {T Q : C} {V X : Family T}
    (f : V ⟶ X) (g : V ⟶ constantFamily T Q) (hf : isTotal f) (hg : isTotal g) :
    ∃! h : V ⟶ tensorConstant X Q, isTotal h ∧
      h ≫ tensorFst X Q = f ∧ h ≫ tensorSnd X Q = g := by
  refine ⟨tensorPair f g, ⟨?_, ?_, ?_⟩, ?_⟩
  · change rst (tensorPair f g) = 𝟙 V
    rw [tensorPair_restriction, hf, hg, Category.id_comp]
  · rw [tensorPair_fst, hg, Category.id_comp]
  · rw [tensorPair_snd, hf, Category.id_comp]
  · rintro h ⟨_, h0, h1⟩
    apply tensor_hom_ext
    · rw [h0, tensorPair_fst, hg, Category.id_comp]
    · rw [h1, tensorPair_snd, hf, Category.id_comp]

/-- A universal computation over T, with a total parameter morphism in
the partial slice and its product with the fixed input object. -/
theorem parameterization {T Q : C} (τ : nearProd Q Q ⟶ Q)
    (hτ : IsTuringMorphism τ) (X : Family T)
    (φ : tensorConstant X Q ⟶ constantFamily T Q) :
    ∃ a : X ⟶ constantFamily T Q, isTotal a ∧
      (tensorFunctor T Q).map a ≫ evaluator T τ = φ := by
  have hφ : φ.hom ≫ p0 T Q =
      CategoryTheory.RestrictionCategory.rst φ.hom ≫ (p0 X.base Q ≫ X.proj) := φ.over
  obtain ⟨a, ha, ha0, hcode⟩ := SliceTuringParameters.slice_parameterization
    τ hτ X.proj X.total φ.hom hφ
  let a' : X ⟶ constantFamily T Q := ⟨a, by
    change a ≫ p0 T Q = CategoryTheory.RestrictionCategory.rst a ≫ X.proj
    rw [ha0, ha, Category.id_comp]⟩
  refine ⟨a', (AmbientPartialSlice.total_iff a').mpr ha, Hom.ext ?_⟩
  exact hcode

end CategoricalEssentialIncompleteness.V46.AmbientSliceTuring
