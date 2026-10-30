/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.EffectiveFork

/-! # Comparison with the actual functor category on the walking span -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open CategoryTheory CategoryTheory.RestrictionCategory CategoryTheory.Limits

namespace CategoricalEssentialIncompleteness.LocalConnectedness.EffectiveFork

open EnumerableCarriers (Carrier val)

theorem respects_of_eq {C A D B : Carrier} {r : C ⟶ A} {s : D ⟶ B}
    {f : C ⟶ D} {g : A ⟶ B} (he : r ≫ g = f ≫ s) : Respects r s f g := by
  intro x y u v hxy hxu hyv
  have hh : v ∈ val (r ≫ g) x := by
    rw [he]
    exact (EnumerableCarriers.mem_val_comp f s x v).mpr ⟨y, hxy, hyv⟩
  obtain ⟨u', hu', hv⟩ := (EnumerableCarriers.mem_val_comp r g x v).mp hh
  have he' : u' = u := Part.mem_unique hu' hxu
  exact he' ▸ hv

theorem eq_of_respects_total {C A D B : Carrier} {r : C ⟶ A} {s : D ⟶ B}
    {f : C ⟶ D} {g : A ⟶ B} (rt : isTotal r) (st : isTotal s) (ft : isTotal f)
    (hf : Respects r s f g) : r ≫ g = f ≫ s := by
  apply EnumerableCarriers.val_injective
  apply PFun.ext
  intro x v
  constructor
  · intro h
    obtain ⟨u, hu, hv⟩ := (EnumerableCarriers.mem_val_comp r g x v).mp h
    obtain ⟨y, hy⟩ := Part.dom_iff_mem.mp ((EnumerableCarriers.total_iff f).mp ft x
      (EnumerableCarriers.val_source r x u hu))
    obtain ⟨w, hw⟩ := Part.dom_iff_mem.mp ((EnumerableCarriers.total_iff s).mp st y
      (EnumerableCarriers.val_target f x y hy))
    have he : w = v := Part.mem_unique (hf x y u w hy hu hw) hv
    exact (EnumerableCarriers.mem_val_comp f s x v).mpr ⟨y, hy, he ▸ hw⟩
  · intro h
    obtain ⟨y, hy, hv⟩ := (EnumerableCarriers.mem_val_comp f s x v).mp h
    obtain ⟨u, hu⟩ := Part.dom_iff_mem.mp ((EnumerableCarriers.total_iff r).mp rt x
      (EnumerableCarriers.val_source f x y hy))
    exact (EnumerableCarriers.mem_val_comp r g x v).mpr ⟨u, hu, hf x y u v hy hu hv⟩

abbrev Total := WideSubcategory (isTotal (C := Object))

def totalFunctor : Total ⥤ (WalkingSpan ⥤ EnumerableCarriers.Total) where
  obj X := totalDiagram X.obj
  map {X Y} f := spanHomMk
    ⟨f.hom.center, ((total_iff _).mp f.property).1⟩
    ⟨f.hom.left, ((total_iff _).mp f.property).2.1⟩
    ⟨f.hom.right, ((total_iff _).mp f.property).2.2⟩
    (by
      apply WideSubcategory.hom_ext
      exact eq_of_respects_total X.obj.left_total Y.obj.left_total
        ((total_iff _).mp f.property).1 f.hom.natural_left)
    (by
      apply WideSubcategory.hom_ext
      exact eq_of_respects_total X.obj.right_total Y.obj.right_total
        ((total_iff _).mp f.property).1 f.hom.natural_right)
  map_id X := by ext j; rcases j with _ | (_ | _) <;> rfl
  map_comp f g := by ext j; rcases j with _ | (_ | _) <;> rfl

def fromDiagram (F : WalkingSpan ⥤ EnumerableCarriers.Total) : Object where
  center := (F.obj .zero).obj
  left := (F.obj .left).obj
  right := (F.obj .right).obj
  leftMap := (F.map WalkingSpan.Hom.fst).hom
  rightMap := (F.map WalkingSpan.Hom.snd).hom
  left_total := (F.map WalkingSpan.Hom.fst).property
  right_total := (F.map WalkingSpan.Hom.snd).property

def fromNatural {F G : WalkingSpan ⥤ EnumerableCarriers.Total} (f : F ⟶ G) :
    fromDiagram F ⟶ fromDiagram G where
  center := (f.app .zero).hom
  left := (f.app .left).hom
  right := (f.app .right).hom
  natural_left := respects_of_eq (congrArg (fun k => k.hom) (f.naturality WalkingSpan.Hom.fst))
  natural_right := respects_of_eq (congrArg (fun k => k.hom) (f.naturality WalkingSpan.Hom.snd))

def fromFunctor : (WalkingSpan ⥤ EnumerableCarriers.Total) ⥤ Total where
  obj F := ⟨fromDiagram F⟩
  map f := ⟨fromNatural f, (total_iff _).mpr
    ⟨(f.app .zero).property, (f.app .left).property, (f.app .right).property⟩⟩
  map_id F := by apply WideSubcategory.hom_ext; apply Hom.ext <;> rfl
  map_comp f g := by apply WideSubcategory.hom_ext; apply Hom.ext <;> rfl

/-- The total arrows form the paper's functor category `C_rec^J`. -/
def totalEquivalence : Total ≌ (WalkingSpan ⥤ EnumerableCarriers.Total) where
  functor := totalFunctor
  inverse := fromFunctor
  unitIso := NatIso.ofComponents (fun X => Iso.refl X) (by
    intro X Y f
    apply WideSubcategory.hom_ext
    apply Hom.ext
    · change f.hom.center ≫ 𝟙 _ = 𝟙 _ ≫ f.hom.center
      simp
    · change f.hom.left ≫ 𝟙 _ = 𝟙 _ ≫ f.hom.left
      simp
    · change f.hom.right ≫ 𝟙 _ = 𝟙 _ ≫ f.hom.right
      simp)
  counitIso := NatIso.ofComponents
    (fun F => spanIsoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (by change (F.map WalkingSpan.Hom.fst) ≫ 𝟙 _ = 𝟙 _ ≫ _; simp)
      (by change (F.map WalkingSpan.Hom.snd) ≫ 𝟙 _ = 𝟙 _ ≫ _; simp))
    (by
      intro F G f
      ext j
      rcases j with _ | (_ | _)
      all_goals simp [totalFunctor, fromFunctor, fromNatural])
  functor_unitIso_comp X := by
    ext j
    rcases j with _ | (_ | _)
    all_goals simp [totalFunctor, fromFunctor, totalDiagram, fromDiagram]

end CategoricalEssentialIncompleteness.LocalConnectedness.EffectiveFork
