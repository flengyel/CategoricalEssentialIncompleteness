/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import Mathlib.CategoryTheory.Endofunctor.Algebra
import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.CategoryTheory.RegularCategory.Basic
import CategoricalEssentialIncompleteness.LocalSwitch
import Mathlib.CategoryTheory.Widesubcategory

/-! # Initial derivation algebras and their images -/

noncomputable section

universe v u

open CategoryTheory CategoryTheory.Limits CategoryTheory.RestrictionCategory

namespace CategoricalEssentialIncompleteness.V46

variable {D : Type u} [Category.{v} D] {F : D}

/-- A subobject is closed when its object in the slice admits an algebra
structure for the inference endofunctor. -/
def ClosedUnder (H : Over F ⥤ Over F) {T : D} (m : T ⟶ F) : Prop :=
  Nonempty (H.obj (Over.mk m) ⟶ Over.mk m)

/-- The preservation property used to transfer the derivation algebra to
its regular image. It concerns the underlying morphisms of the slice. -/
def PreservesUnderlyingRegularEpis (H : Over F ⥤ Over F) : Prop :=
  ∀ {X Y : Over F} (e : X ⟶ Y), IsRegularEpi e.left →
    IsRegularEpi (H.map e).left

section Image

variable [Regular D] (H : Over F ⥤ Over F) (A : Endofunctor.Algebra H)

def derivationImage : Over F := Over.mk (image.ι A.a.hom)

def derivationImageQuotient : A.a ⟶ derivationImage H A :=
  Over.homMk (factorThruImage A.a.hom) (image.fac A.a.hom)

private theorem imageSquare :
    CommSq (A.str.left ≫ factorThruImage A.a.hom)
      (H.map (derivationImageQuotient H A)).left (image.ι A.a.hom)
      (H.obj (derivationImage H A)).hom := by
  constructor
  rw [Category.assoc, image.fac, Over.w A.str,
    Over.w (H.map (derivationImageQuotient H A))]

/-- The regular image of the conclusion morphism is closed. -/
def derivationImageAlgebra
    (hH : PreservesUnderlyingRegularEpis H) : Endofunctor.Algebra H := by
  letI := hH (derivationImageQuotient H A)
    (inferInstance : IsRegularEpi (factorThruImage A.a.hom))
  exact ⟨derivationImage H A, Over.homMk (imageSquare H A).lift
    (imageSquare H A).fac_right⟩

/-- The quotient from derivations to their image respects the inference
algebra structures. -/
def derivationImageAlgebraQuotient
    (hH : PreservesUnderlyingRegularEpis H) : A ⟶ derivationImageAlgebra H A hH := by
  letI := hH (derivationImageQuotient H A)
    (inferInstance : IsRegularEpi (factorThruImage A.a.hom))
  refine ⟨derivationImageQuotient H A, ?_⟩
  apply Over.OverMorphism.ext
  exact (imageSquare H A).fac_left

/-- Theorem A.5, in its endofunctor form: the image of the conclusion
morphism of an initial derivation algebra is the least closed subobject.
The rule endofunctor is required only to preserve regular epimorphisms. -/
theorem least_closed_image (hH : PreservesUnderlyingRegularEpis H)
    (hA : IsInitial A) :
    ClosedUnder H (image.ι A.a.hom) ∧
      ∀ {U : D} (m : U ⟶ F) [Mono m], ClosedUnder H m →
        ∃ w : image A.a.hom ⟶ U, w ≫ m = image.ι A.a.hom := by
  constructor
  · exact ⟨(derivationImageAlgebra H A hH).str⟩
  · intro U m _ hm
    rcases hm with ⟨α⟩
    let B : Endofunctor.Algebra H := ⟨Over.mk m, α⟩
    let f : A ⟶ B := hA.to B
    let M : MonoFactorisation A.a.hom :=
      { I := U, m := m, e := f.f.left, fac := Over.w f.f }
    exact ⟨image.lift M, image.lift_fac M⟩

end Image

end CategoricalEssentialIncompleteness.V46

namespace CategoricalEssentialIncompleteness.LocalConnectedness.V46

variable {S : Type u} [Category.{v} S] [RestrictionCategory S]
  [Ranges S] [Splits S]

abbrev TotalCategory (S : Type u) [Category.{v} S] [RestrictionCategory S] :=
  WideSubcategory (isTotal (C := S))

omit [Ranges S] [Splits S] in
/-- A total split inclusion is monic among total morphisms, even when
its retraction is partial. -/
theorem total_split_mono {X Y : TotalCategory S} (m : X ⟶ Y)
    (r : Y.obj ⟶ X.obj) (hmr : m.hom ≫ r = 𝟙 X.obj) : Mono m := by
  constructor
  intro Z u v h
  apply WideSubcategory.hom_ext
  have h' := congrArg (fun k : Z ⟶ Y => k.hom ≫ r) h
  change (u.hom ≫ m.hom) ≫ r = (v.hom ≫ m.hom) ≫ r at h'
  simpa only [Category.assoc, hmr, Category.comp_id] using h'

/-- Lemma A.7. Only the image inclusion under consideration is required
to have a partial inverse. Regularity supplies the regular epimorphism
in an image factorization; no further use of regularity is needed. -/
theorem range_regularImage {X I Y : TotalCategory S} (e : X ⟶ I)
    (m : I ⟶ Y) [IsRegularEpi e] (r : Y.obj ⟶ I.obj)
    (hmr : m.hom ≫ r = 𝟙 I.obj) (hrm : r ≫ m.hom = rst r) :
    (Ranges.range (e.hom ≫ m.hom)).hom = r ≫ m.hom := by
  let a := Ranges.range (e.hom ≫ m.hom)
  have hreceives : (e.hom ≫ m.hom) ≫ a.hom = e.hom ≫ m.hom :=
    Ranges.receives _
  have hleast : a ≤ Idem.ofRestrict r := by
    apply Ranges.least
    change (e.hom ≫ m.hom) ≫ rst r = e.hom ≫ m.hom
    rw [← hrm]
    simp only [Category.assoc]
    rw [← Category.assoc m.hom, hmr, Category.id_comp]
  obtain ⟨J, j, s, hj, hjs, hsj⟩ := Splits.splitting a
  let JT : TotalCategory S := ⟨J⟩
  let jT : JT ⟶ Y := ⟨j, hj⟩
  have : Mono jT := total_split_mono jT s hjs
  have hscomp : ((e.hom ≫ m.hom) ≫ s) ≫ j = e.hom ≫ m.hom := by
    rw [Category.assoc, hsj, hreceives]
  have hsf : isTotal ((e.hom ≫ m.hom) ≫ s) := by
    change rst ((e.hom ≫ m.hom) ≫ s) = 𝟙 X.obj
    rw [← rst_comp_of_isTotal _ hj, hscomp]
    exact isTotal_comp e.property m.property
  let sf : X ⟶ JT := ⟨(e.hom ≫ m.hom) ≫ s, hsf⟩
  have sq : CommSq sf e jT m := ⟨by apply WideSubcategory.hom_ext; exact hscomp⟩
  have hu : sq.lift.hom ≫ j = m.hom :=
    congrArg (fun k : I ⟶ Y => k.hom) sq.fac_right
  have hma : m.hom ≫ a.hom = m.hom := by
    rw [← hu, Category.assoc, ← hsj, ← Category.assoc j, hjs, Category.id_comp]
  have hother : Idem.ofRestrict r ≤ a := by
    change rst r ≫ a.hom = rst r
    rw [← hrm, Category.assoc, hma]
  have ha := le_antisymm hleast hother
  exact (congrArg Idem.hom ha).trans hrm.symm

end CategoricalEssentialIncompleteness.LocalConnectedness.V46
