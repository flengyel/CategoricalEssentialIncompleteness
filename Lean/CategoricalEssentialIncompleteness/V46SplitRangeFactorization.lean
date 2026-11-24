/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46AlgebraFactorization
public import CategoricalEssentialIncompleteness.V46RegularImage

/-!
# The factorization of total morphisms in a split range category

Appendix A cites Cockett, Guo and Hofstra, *Range categories I*, Theorem 4.7.
The left class consists of total morphisms of full range. The right class
consists of total partial isomorphisms. Splitting the range of a morphism gives
its factorization, and the partial inverse of the right side of a square gives
its diagonal.
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory CategoryTheory.RestrictionCategory
open CategoricalEssentialIncompleteness.LocalConnectedness
open CategoricalEssentialIncompleteness.LocalConnectedness.V46 (TotalCategory total_split_mono)

namespace CategoricalEssentialIncompleteness.V46

universe v u
variable {C : Type u} [Category.{v} C] [RestrictionCategory C]

/-- The range operation of Definition 2.12 in *Range categories I*. The
codomain of the operation expresses axiom RR.1. -/
structure RangeOperation (C : Type u) [Category.{v} C] [RestrictionCategory C] where
  range {X Y : C} : (X ⟶ Y) → Idem Y
  receives {X Y : C} (f : X ⟶ Y) : f ≫ (range f).hom = f
  restrict_range {X Y : C} (f : X ⟶ Y) (e : Idem Y) :
    (range (f ≫ e.hom)).hom = (range f).hom ≫ e.hom
  range_comp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    range ((range f).hom ≫ g) = range (f ≫ g)

namespace RangeOperation

variable (R : RangeOperation C)

def fullRange : MorphismProperty (TotalCategory C) :=
  fun _ Y f => (R.range f.hom).hom = 𝟙 Y.obj

/-- A total morphism is a partial isomorphism precisely when a partial
inverse splits its target restriction idempotent. -/
def restrictionMonics : MorphismProperty (TotalCategory C) :=
  fun X Y m => ∃ r : Y.obj ⟶ X.obj, m.hom ≫ r = 𝟙 X.obj ∧ r ≫ m.hom = rst r

theorem range_of_section {X Y : C} {f : X ⟶ Y} (s : Y ⟶ X) (h : s ≫ f = 𝟙 Y) :
    (R.range f).hom = 𝟙 Y := by
  calc (R.range f).hom = (s ≫ f) ≫ (R.range f).hom := by rw [h, Category.id_comp]
       _ = 𝟙 Y := by rw [Category.assoc, R.receives, h]

theorem range_comp_of_full {X Y Z : C} {f : X ⟶ Y} (g : Y ⟶ Z)
    (hf : (R.range f).hom = 𝟙 Y) : R.range (f ≫ g) = R.range g := by
  rw [← R.range_comp, hf, Category.id_comp]

private theorem full_comp {X Y Z : TotalCategory C} {f : X ⟶ Y} {g : Y ⟶ Z}
    (hf : R.fullRange f) (hg : R.fullRange g) : R.fullRange (f ≫ g) := by
  change (R.range (f.hom ≫ g.hom)).hom = _
  rw [R.range_comp_of_full g.hom hf]
  exact hg

private theorem full_iso {X Y : TotalCategory C} (i : X ≅ Y) : R.fullRange i.hom :=
  R.range_of_section i.inv.hom (congrArg (fun k : Y ⟶ Y => k.hom) i.inv_hom_id)

theorem restrictionMonics_comp {X Y Z : TotalCategory C} {m : X ⟶ Y} {n : Y ⟶ Z}
    (hm : restrictionMonics m) (hn : restrictionMonics n) : restrictionMonics (m ≫ n) := by
  obtain ⟨s, ms, sm⟩ := hm
  obtain ⟨t, nt, tn⟩ := hn
  refine ⟨t ≫ s, ?_, ?_⟩
  · change (m.hom ≫ n.hom) ≫ t ≫ s = _
    rw [Category.assoc, ← Category.assoc n.hom, nt, Category.id_comp, ms]
  · change (t ≫ s) ≫ m.hom ≫ n.hom = _
    calc _ = (t ≫ rst s) ≫ n.hom := by simp only [Category.assoc, ← sm]
         _ = rst (t ≫ s) ≫ rst t := by rw [← rst_comp, Category.assoc, tn]
         _ = rst (t ≫ s) := by rw [rst_comm, rst_comp_absorb]

private theorem restrictionMonics_iso {X Y : TotalCategory C} (i : X ≅ Y) :
    restrictionMonics i.hom := by
  refine ⟨i.inv.hom, congrArg (fun k : X ⟶ X => k.hom) i.hom_inv_id, ?_⟩
  rw [show rst i.inv.hom = 𝟙 Y.obj from i.inv.property]
  exact congrArg (fun k : Y ⟶ Y => k.hom) i.inv_hom_id

theorem full_respectsIso : R.fullRange.RespectsIso :=
  MorphismProperty.RespectsIso.mk _ (fun i _ h => R.full_comp (R.full_iso i) h)
    (fun i _ h => R.full_comp h (R.full_iso i))

theorem restrictionMonics_respectsIso : (restrictionMonics (C := C)).RespectsIso :=
  MorphismProperty.RespectsIso.mk _
    (fun i _ h => restrictionMonics_comp (restrictionMonics_iso i) h)
    (fun i _ h => restrictionMonics_comp h (restrictionMonics_iso i))

theorem restrictionMonics_mono {X Y : TotalCategory C} {m : X ⟶ Y}
    (hm : restrictionMonics m) : Mono m := by
  obtain ⟨r, mr, _⟩ := hm
  exact total_split_mono m r mr

theorem splitter_restriction {X Z : C} {j : Z ⟶ X} {s : X ⟶ Z}
    (hj : isTotal j) {e : Idem X} (hs : s ≫ j = e.hom) : rst s = e.hom := by
  rw [← rst_comp_of_isTotal s hj, hs, e.restriction]

private theorem factors [Splits C] {X Y : TotalCategory C} (f : X ⟶ Y) :
    Nonempty (MorphismProperty.MapFactorizationData R.fullRange restrictionMonics f) := by
  obtain ⟨I, j, s, hj, js, sj⟩ := Splits.splitting (R.range f.hom)
  have fsj : (f.hom ≫ s) ≫ j = f.hom := by rw [Category.assoc, sj, R.receives]
  have left : isTotal (f.hom ≫ s) := total_of_comp_total _ j (by rw [fsj]; exact f.property)
  refine ⟨{ Z := ⟨I⟩, i := ⟨f.hom ≫ s, left⟩, p := ⟨j, hj⟩,
            fac := WideSubcategory.hom_ext _ fsj, hi := ?_, hp := ?_ }⟩
  · change (R.range (f.hom ≫ s)).hom = 𝟙 I
    rw [← R.range_comp, ← sj, Category.assoc, js, Category.comp_id]
    exact R.range_of_section j js
  · exact ⟨s, js, sj.trans (splitter_restriction hj sj).symm⟩

private theorem absorbs_of_full {A B Y : C} {e : A ⟶ B} {g : B ⟶ Y}
    (he : (R.range e).hom = 𝟙 B) (a : Idem Y) (h : (e ≫ g) ≫ a.hom = e ≫ g) :
    g ≫ a.hom = g := by
  have hr := R.restrict_range (e ≫ g) a
  rw [h, R.range_comp_of_full _ he] at hr
  calc g ≫ a.hom = (g ≫ (R.range g).hom) ≫ a.hom := by rw [R.receives]
       _ = g := by rw [Category.assoc, ← hr, R.receives]

theorem factorizationSystem [Splits C] :
    OrthogonalFactorizationSystem R.fullRange restrictionMonics := by
  refine ⟨R.full_respectsIso, restrictionMonics_respectsIso, ⟨fun f => R.factors f⟩, ?_⟩
  intro A B X Y e m he hm f g w
  have := restrictionMonics_mono hm
  obtain ⟨r, mr, rm⟩ := hm
  have sq : f.hom ≫ m.hom = e.hom ≫ g.hom := congrArg (fun k : A ⟶ Y => k.hom) w
  have fixed : (e.hom ≫ g.hom) ≫ rst r = e.hom ≫ g.hom := by
    rw [← sq, ← rm]
    simp only [Category.assoc, ← Category.assoc m.hom r, mr, Category.id_comp]
  have right : (g.hom ≫ r) ≫ m.hom = g.hom := by
    rw [Category.assoc, rm]
    exact R.absorbs_of_full he (Idem.ofRestrict r) fixed
  let d : B ⟶ X := ⟨g.hom ≫ r, total_of_comp_total _ m.hom (by rw [right]; exact g.property)⟩
  have dm : d ≫ m = g := WideSubcategory.hom_ext _ right
  exact ⟨d, ⟨(cancel_mono m).mp (by rw [Category.assoc, dm, w]), dm⟩,
    fun k hk => (cancel_mono m).mp (hk.2.trans dm.symm)⟩

end RangeOperation
end CategoricalEssentialIncompleteness.V46
