/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.LocalSwitch
public import Mathlib.CategoryTheory.Widesubcategory

/-! # Monic spans in the total category of a split restriction category -/

@[expose] public section

universe v u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open CategoryTheory CategoryTheory.RestrictionCategory

namespace CategoricalEssentialIncompleteness.LocalConnectedness.PartialSpans

variable {C : Type u} [Category.{v} C] [RestrictionCategory C] [Splits C]
  [WeakChoice C] [Ranges C]

abbrev Total (C : Type u) [Category.{v} C] [RestrictionCategory C] :=
  WideSubcategory (isTotal (C := C))

theorem partialMono_of_mono {X Y : Total C} (m : X ⟶ Y) [Mono m] : PartialMono m.hom := by
  apply partial_mono_of_total_tests
  intro W f g hf hg he
  let f' : (⟨W⟩ : Total C) ⟶ X := ⟨f,hf⟩
  let g' : (⟨W⟩ : Total C) ⟶ X := ⟨g,hg⟩
  have hh : f' ≫ m=g' ≫ m := by apply WideSubcategory.hom_ext; exact he
  exact congrArg (fun k => k.hom ≫ rst m.hom) ((cancel_mono m).mp hh)

def inverse {X Y : Total C} (m : X ⟶ Y) [Mono m] : Y.obj ⟶ X.obj :=
  Classical.choose (WeakChoice.section_exists m.hom (partialMono_of_mono m))

theorem inverse_section {X Y : Total C} (m : X ⟶ Y) [Mono m] :
    SectionOf m.hom (inverse m) := Classical.choose_spec
      (WeakChoice.section_exists m.hom (partialMono_of_mono m))

@[simp] theorem inverse_hom {X Y : Total C} (m : X ⟶ Y) [Mono m] :
    inverse m ≫ m.hom = rst (inverse m) := (inverse_section m).comp

@[simp] theorem hom_inverse {X Y : Total C} (m : X ⟶ Y) [Mono m] :
    m.hom ≫ inverse m = 𝟙 X.obj := by
  have hh := partialMono_of_mono m (m.hom ≫ inverse m) (𝟙 X.obj)
    (by simpa only [Category.id_comp, Category.assoc] using (inverse_section m).receives)
  simpa only [show rst m.hom=𝟙 X.obj from m.property,
    Category.comp_id, Category.id_comp] using hh

@[simp] theorem hom_restrict_inverse {X Y : Total C} (m : X ⟶ Y) [Mono m] :
    m.hom ≫ rst (inverse m)=m.hom := by
  rw [← inverse_hom, ← Category.assoc, hom_inverse, Category.id_comp]

theorem inverse_comp {X Y Z : Total C} (m : X ⟶ Y) (n : Y ⟶ Z) [Mono m] [Mono n] :
    inverse (m ≫ n) = inverse n ≫ inverse m := by
  apply PartialMono.section_unique (partialMono_of_mono (m ≫ n)) (inverse_section _)
  constructor
  · change (inverse n ≫ inverse m) ≫ (m.hom ≫ n.hom) = _
    calc
      _ = (inverse n ≫ (inverse m ≫ m.hom)) ≫ n.hom := by simp only [Category.assoc]
      _ = inverse n ≫ rst (inverse m) ≫ n.hom :=
        by simpa only [Category.assoc] using
          congrArg (fun k => (inverse n ≫ k) ≫ n.hom) (inverse_hom m)
      _ = rst (inverse n ≫ inverse m) ≫ (inverse n ≫ n.hom) := by
        simpa only [Category.assoc] using
          congrArg (fun k => k ≫ n.hom) (rst_comp (inverse n) (inverse m)).symm
      _ = rst (inverse n ≫ inverse m) := by
        rw [inverse_hom, rst_comm (inverse n ≫ inverse m) (inverse n), rst_comp_absorb]
  · change (m.hom ≫ n.hom) ≫ (inverse n ≫ inverse m) ≫ (m.hom ≫ n.hom)=_
    simp only [Category.assoc]
    rw [← Category.assoc n.hom, hom_inverse, Category.id_comp,
      ← Category.assoc m.hom, hom_inverse, Category.id_comp]
    rfl

structure Span (X Y : C) where
  apex : Total C
  mono : apex ⟶ (⟨X⟩ : Total C)
  map : apex ⟶ (⟨Y⟩ : Total C)
  monic : Mono mono := by infer_instance

attribute [instance] Span.monic

def Span.value {X Y : C} (s : Span X Y) : X ⟶ Y := inverse s.mono ≫ s.map.hom

@[simp] theorem Span.restrict_value {X Y : C} (s : Span X Y) :
    rst s.value = rst (inverse s.mono) := rst_comp_of_isTotal _ s.map.property

def Span.Isomorphic {X Y : C} (s t : Span X Y) : Prop :=
  ∃ i : s.apex ≅ t.apex, i.hom ≫ t.mono=s.mono ∧ i.hom ≫ t.map=s.map

theorem Span.value_eq_of_isomorphic {X Y : C} {s t : Span X Y}
    (h : s.Isomorphic t) : s.value=t.value := by
  obtain ⟨i,hi,hv⟩ := h
  have hm : s.mono.hom=i.hom.hom ≫ t.mono.hom := congrArg (fun k => k.hom) hi.symm
  have hv' : s.map.hom=i.hom.hom ≫ t.map.hom := congrArg (fun k => k.hom) hv.symm
  have hii : i.inv.hom ≫ i.hom.hom=𝟙 t.apex.obj :=
    congrArg (fun k => k.hom) i.inv_hom_id
  have hs : SectionOf s.mono.hom (inverse t.mono ≫ i.inv.hom) := by
    constructor
    · rw [hm, Category.assoc, ← Category.assoc i.inv.hom, hii, Category.id_comp,
        inverse_hom, rst_comp_of_isTotal _ i.inv.property]
    · rw [hm]
      simp only [Category.assoc]
      rw [← Category.assoc i.inv.hom, hii, Category.id_comp,
        ← Category.assoc t.mono.hom, hom_inverse, Category.id_comp]
  have he := PartialMono.section_unique (partialMono_of_mono s.mono) (inverse_section _) hs
  unfold Span.value
  rw [he, hv', Category.assoc, ← Category.assoc i.inv.hom, hii, Category.id_comp]

theorem Span.isomorphic_of_value_eq {X Y : C} (s t : Span X Y)
    (he : s.value=t.value) : s.Isomorphic t := by
  have hd : rst (inverse s.mono)=rst (inverse t.mono) := by
    simpa only [Span.restrict_value] using congrArg rst he
  let h := s.mono.hom ≫ inverse t.mono
  let k := t.mono.hom ≫ inverse s.mono
  have hk : h ≫ k=𝟙 s.apex.obj := by
    dsimp [h,k]
    rw [Category.assoc, ← Category.assoc (inverse t.mono), inverse_hom, ← hd,
      rst_comp_self, hom_inverse]
  have kh : k ≫ h=𝟙 t.apex.obj := by
    dsimp [h,k]
    rw [Category.assoc, ← Category.assoc (inverse s.mono), inverse_hom, hd,
      rst_comp_self, hom_inverse]
  let h' : s.apex ⟶ t.apex := ⟨h,total_of_comp_total h k (by rw [hk]; exact rst_id _)⟩
  let k' : t.apex ⟶ s.apex := ⟨k,total_of_comp_total k h (by rw [kh]; exact rst_id _)⟩
  refine ⟨⟨h',k',?_,?_⟩,?_,?_⟩
  · apply WideSubcategory.hom_ext; exact hk
  · apply WideSubcategory.hom_ext; exact kh
  · apply WideSubcategory.hom_ext
    change (s.mono.hom ≫ inverse t.mono) ≫ t.mono.hom=s.mono.hom
    rw [Category.assoc, inverse_hom, ← hd, hom_restrict_inverse]
  · apply WideSubcategory.hom_ext
    change (s.mono.hom ≫ inverse t.mono) ≫ t.map.hom=s.map.hom
    rw [Category.assoc, ← Span.value, ← he]
    change s.mono.hom ≫ (inverse s.mono ≫ s.map.hom)=s.map.hom
    rw [← Category.assoc, hom_inverse, Category.id_comp]

theorem Span.isomorphic_iff_value_eq {X Y : C} (s t : Span X Y) :
    s.Isomorphic t ↔ s.value=t.value :=
  ⟨Span.value_eq_of_isomorphic,Span.isomorphic_of_value_eq s t⟩

def spanSetoid (X Y : C) : Setoid (Span X Y) where
  r s t := s.Isomorphic t
  iseqv := ⟨fun s => (s.isomorphic_iff_value_eq s).mpr rfl,
    fun h => Span.isomorphic_of_value_eq _ _ (Span.value_eq_of_isomorphic h).symm,
    fun h k => Span.isomorphic_of_value_eq _ _
      ((Span.value_eq_of_isomorphic h).trans (Span.value_eq_of_isomorphic k))⟩

def spanClassValue {X Y : C} : Quotient (spanSetoid X Y) → (X ⟶ Y) :=
  Quotient.lift Span.value (fun _ _ => Span.value_eq_of_isomorphic)

theorem spanClassValue_injective {X Y : C} :
    Function.Injective (spanClassValue (X := X) (Y := Y)) := by
  intro s t
  induction s using Quotient.inductionOn with | _ s =>
    induction t using Quotient.inductionOn with | _ t =>
      intro h
      exact Quotient.sound (Span.isomorphic_of_value_eq s t h)

theorem Span.exists_value {X Y : C} (f : X ⟶ Y) : ∃ s : Span X Y, s.value=f := by
  obtain ⟨D,m,r,hm,hmr,hrm⟩ := Splits.splitting (Idem.ofRestrict f)
  change r ≫ m=rst f at hrm
  have hmrst : m ≫ rst f=m := by
    rw [← hrm, ← Category.assoc, hmr, Category.id_comp]
  have hmf : isTotal (m ≫ f) := by
    change rst (m ≫ f)=𝟙 D
    rw [rst_comp_rst_right,hmrst]
    exact hm
  let m' : (⟨D⟩ : Total C) ⟶ ⟨X⟩ := ⟨m,hm⟩
  haveI : Mono m' := ⟨by
    intro W u v he
    apply WideSubcategory.hom_ext
    have hh := congrArg (fun k => k.hom ≫ r) he
    change (u.hom ≫ m) ≫ r=(v.hom ≫ m) ≫ r at hh
    simpa only [WideSubcategory.comp_def, Category.assoc, hmr, Category.comp_id] using hh⟩
  have hs : SectionOf m r := by
    constructor
    · have hh := congrArg rst hrm
      rw [rst_comp_of_isTotal r hm, restrict_restrict] at hh
      exact hrm.trans hh.symm
    · rw [← Category.assoc,hmr,Category.id_comp]
  refine ⟨⟨⟨D⟩,m',⟨m ≫ f,hmf⟩,inferInstance⟩,?_⟩
  change inverse m' ≫ (m ≫ f)=f
  have he := PartialMono.section_unique (partialMono_of_mono m') (inverse_section m') hs
  rw [he, ← Category.assoc,hrm,rst_comp_self]

theorem spanClassValue_surjective {X Y : C} :
    Function.Surjective (spanClassValue (X := X) (Y := Y)) := by
  intro f
  obtain ⟨s,hs⟩ := Span.exists_value f
  exact ⟨Quotient.mk _ s,hs⟩

/-- Isomorphism classes of monic spans are precisely the partial morphisms. -/
def homEquiv (X Y : C) : Quotient (spanSetoid X Y) ≃ (X ⟶ Y) :=
  Equiv.ofBijective spanClassValue ⟨spanClassValue_injective,spanClassValue_surjective⟩

/-- Objects for the category of isomorphism classes of monic spans. -/
structure Par (C : Type u) where
  obj : C

instance parCategory : Category.{max u v} (Par C) where
  Hom X Y := Quotient (spanSetoid X.obj Y.obj)
  id X := (homEquiv X.obj X.obj).symm (𝟙 X.obj)
  comp {X Y Z} f g := (homEquiv X.obj Z.obj).symm
    (homEquiv X.obj Y.obj f ≫ homEquiv Y.obj Z.obj g)
  id_comp {X Y} f := by apply (homEquiv X.obj Y.obj).injective; simp
  comp_id {X Y} f := by apply (homEquiv X.obj Y.obj).injective; simp
  assoc {W X Y Z} f g h := by apply (homEquiv W.obj Z.obj).injective; simp [Category.assoc]

def comparison : Par C ⥤ C where
  obj X := X.obj
  map {X Y} f := homEquiv X.obj Y.obj f
  map_id X := (homEquiv X.obj X.obj).apply_symm_apply _
  map_comp f g := (homEquiv _ _).apply_symm_apply _

def Span.toHom {X Y : C} (s : Span X Y) : (Par.mk X ⟶ Par.mk Y) :=
  Quotient.mk (spanSetoid X Y) s

def representation : C ⥤ Par C where
  obj X := ⟨X⟩
  map {X Y} f := (homEquiv X Y).symm f
  map_id X := rfl
  map_comp f g := by simp only [CategoryStruct.comp, Equiv.apply_symm_apply]

def equivalence : Par C ≌ C where
  functor := comparison
  inverse := representation
  unitIso := NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro X Y f
    simp only [Functor.comp_map,Functor.id_map,Iso.refl_hom,Category.comp_id,Category.id_comp]
    exact ((homEquiv X.obj Y.obj).symm_apply_apply f).symm)
  counitIso := NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro X Y f
    simp only [Functor.comp_map,Functor.id_map,Iso.refl_hom,Category.comp_id,Category.id_comp]
    exact (homEquiv X Y).apply_symm_apply f)

end CategoricalEssentialIncompleteness.LocalConnectedness.PartialSpans
