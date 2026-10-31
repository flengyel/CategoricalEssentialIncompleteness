/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.PartialFunctions
import CategoricalEssentialIncompleteness.RangeFunctor

/-! # A range functor whose product comparison is not surjective -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open CategoryTheory CategoryTheory.RestrictionCategory
open CategoryTheory.CoprodStruct CategoryTheory.HasCoproducts

namespace CategoricalEssentialIncompleteness.LocalConnectedness.PartialFunctions

def doubling : Pfn ⥤ Pfn where
  obj X := PartialFun.of (X × Bool)
  map f := fun p => (f p.1).map (fun y => (y,p.2))
  map_id X := by
    funext p
    exact Part.map_some _ _
  map_comp f g := by
    funext p
    change ((f p.1).bind g).map (fun y => (y,p.2))=
      ((f p.1).map (fun y => (y,p.2))).bind
        (fun q => (g q.1).map (fun z => (z,q.2)))
    rw [Part.map_bind,Part.bind_map]

theorem mem_doubling {X Y : Pfn} (f : X ⟶ Y) (x : X × Bool) (y : Y × Bool) :
    y ∈ doubling.map f x ↔ y.1 ∈ f x.1 ∧ y.2=x.2 := by
  change y ∈ ((f x.1).map (fun z => (z,x.2)) : Part (Y × Bool)) ↔ _
  rw [Part.mem_map_iff]
  constructor
  · rintro ⟨z,hz,he⟩
    subst y
    exact ⟨hz,rfl⟩
  · rintro ⟨hy,he⟩
    exact ⟨y.1,hy,Prod.ext rfl he.symm⟩

theorem mem_actual_range {X Y : Pfn} (f : X ⟶ Y) (x y : Y) :
    y ∈ (Ranges.range f).hom x ↔ (∃ z,x ∈ f z) ∧ y=x := mem_identity _ x y

def distribute {X Y : Pfn} : (X × Bool) ⊕ (Y × Bool) → (X ⊕ Y) × Bool
  | .inl (x,a) => (.inl x,a)
  | .inr (y,a) => (.inr y,a)

def undistribute {X Y : Pfn} : (X ⊕ Y) × Bool → (X × Bool) ⊕ (Y × Bool)
  | (.inl x,a) => .inl (x,a)
  | (.inr y,a) => .inr (y,a)

theorem doubling_comparison (X Y : Pfn) :
    coproductComparison doubling X Y=PFun.lift (distribute (X := X) (Y := Y)) := by
  funext s
  rw [coproductComparison]
  cases s with
  | inl p =>
    rw [copair_inl]
    exact Part.map_some _ _
  | inr p =>
    rw [copair_inr]
    exact Part.map_some _ _

def doublingCoproductIso (X Y : Pfn) :
    coprod (doubling.obj X) (doubling.obj Y) ≅ doubling.obj (coprod X Y) where
  hom := PFun.lift distribute
  inv := PFun.lift undistribute
  hom_inv_id := by
    funext s
    change (Part.some (distribute s)).bind (fun z => Part.some (undistribute z))=Part.some s
    rw [Part.bind_some]
    cases s <;> rfl
  inv_hom_id := by
    funext s
    change (Part.some (undistribute s)).bind (fun z => Part.some (distribute z))=Part.some s
    rw [Part.bind_some]
    rcases s with ⟨s,a⟩
    cases s <;> rfl

def doublingRangeFunctor : RangeFunctor Pfn Pfn where
  toFunctor := doubling
  map_restrict f := by
    apply PFun.ext
    intro x y
    rw [mem_doubling,mem_rst,mem_rst]
    constructor
    · rintro ⟨⟨⟨z,hz⟩,h0⟩,h1⟩
      exact ⟨⟨(z,x.2),(mem_doubling f x (z,x.2)).mpr ⟨hz,rfl⟩⟩,Prod.ext h0 h1⟩
    · rintro ⟨⟨z,hz⟩,he⟩
      exact ⟨⟨⟨z.1,((mem_doubling f x z).mp hz).1⟩,congrArg Prod.fst he⟩,
        congrArg Prod.snd he⟩
  map_range f := by
    apply PFun.ext
    intro x y
    rw [mem_doubling,mem_actual_range,mem_actual_range]
    constructor
    · rintro ⟨⟨⟨z,hz⟩,h0⟩,h1⟩
      exact ⟨⟨(z,x.2),(mem_doubling f (z,x.2) x).mpr ⟨hz,rfl⟩⟩,Prod.ext h0 h1⟩
    · rintro ⟨⟨z,hz⟩,he⟩
      exact ⟨⟨⟨z.1,((mem_doubling f z x).mp hz).1⟩,congrArg Prod.fst he⟩,
        congrArg Prod.snd he⟩
  map_zero X Y := by funext p; exact Part.map_none _
  comparison_isIso X Y := by
    rw [doubling_comparison]
    exact (doublingCoproductIso X Y).isIso_hom

def doublingProductComparison (X Y : Pfn) : ((X × Y) × Bool) → (X × Bool) × (Y × Bool) :=
  fun p => ((p.1.1,p.2),(p.1.2,p.2))

/-- Pairing the images of the two actual product projections gives precisely
the diagonal-tag comparison displayed in Section 2. -/
theorem doubling_product_comparison (X Y : Pfn) :
    (fun p : (X × Y) × Bool =>
      (doubling.map (PFun.lift (Prod.fst : X × Y → X)) p).bind fun x =>
        (doubling.map (PFun.lift (Prod.snd : X × Y → Y)) p).map (fun y => (x,y)))=
      PFun.lift (doublingProductComparison X Y) := by
  funext p
  change ((Part.some p.1.1).map (fun x => (x,p.2))).bind
    (fun x => ((Part.some p.1.2).map (fun y => (y,p.2))).map (fun y => (x,y)))=Part.some _
  simp only [Part.map_some,Part.bind_some]
  rfl

theorem doubling_product_not_surjective (X Y : Pfn) [Nonempty X] [Nonempty Y] :
    ¬ Function.Surjective (doublingProductComparison X Y) := by
  rintro h
  obtain ⟨x⟩ := ‹Nonempty X›
  obtain ⟨y⟩ := ‹Nonempty Y›
  obtain ⟨p,hp⟩ := h ((x,false),(y,true))
  have h0 := congrArg (fun q => q.1.2) hp
  have h1 := congrArg (fun q => q.2.2) hp
  exact Bool.false_ne_true (h0.symm.trans h1)

end CategoricalEssentialIncompleteness.LocalConnectedness.PartialFunctions
