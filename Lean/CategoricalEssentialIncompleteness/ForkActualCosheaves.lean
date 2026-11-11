/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.ForkCosheafEquivalence
public import Mathlib.CategoryTheory.ObjectProperty.Equivalence

/-! # Cosheaves on the literal topological open-set category -/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open CategoryTheory CategoryTheory.Limits

namespace CategoricalEssentialIncompleteness.LocalConnectedness.ForkTopology

abbrev ActualOpen := TopologicalSpace.Opens Point

structure ActualCover (U : ActualOpen) (ι : Type) where
  member : ι → ActualOpen
  le : ∀ i,member i ≤ U
  covers : ∀ p ∈ U,∃ i,p ∈ member i

/-- Compatibility on all common subopens, equivalently on intersections. -/
def ActualCompatible (F : ActualOpen ⥤ Type) {U : ActualOpen} {ι : Type}
    (C : ActualCover U ι) {B : Type} (f : ∀ i,F.obj (C.member i) ⟶ B) : Prop :=
  ∀ i j (V : ActualOpen) (hi : V ≤ C.member i) (hj : V ≤ C.member j),
    F.map (homOfLE hi) ≫ f i=F.map (homOfLE hj) ≫ f j

def ActualIsCosheaf (F : ActualOpen ⥤ Type) : Prop :=
  ∀ (U : ActualOpen) (ι : Type) (C : ActualCover U ι) (B : Type)
    (f : ∀ i,F.obj (C.member i) ⟶ B),ActualCompatible F C f →
      ∃! h : F.obj U ⟶ B,∀ i,F.map (homOfLE (C.le i)) ≫ h=f i

theorem actualCompatible_iff_intersections (F : ActualOpen ⥤ Type)
    {U : ActualOpen} {ι : Type} (C : ActualCover U ι) {B : Type}
    (f : ∀ i,F.obj (C.member i) ⟶ B) :
    ActualCompatible F C f ↔ ∀ i j,
      F.map (homOfLE (inf_le_left : C.member i ⊓ C.member j ≤ C.member i)) ≫ f i=
      F.map (homOfLE (inf_le_right : C.member i ⊓ C.member j ≤ C.member j)) ≫ f j := by
  constructor
  · intro h i j
    exact h i j _ inf_le_left inf_le_right
  · intro h i j V hi hj
    have hv := le_inf hi hj
    calc
      _ = F.map (homOfLE hv) ≫ F.map (homOfLE inf_le_left) ≫ f i := by
        rw [← F.map_comp_assoc]; rfl
      _ = F.map (homOfLE hv) ≫ F.map (homOfLE inf_le_right) ≫ f j :=
        congrArg (fun k => F.map (homOfLE hv) ≫ k) (h i j)
      _ = _ := by rw [← F.map_comp_assoc]; rfl

theorem actualIsCosheaf_iff (F : ActualOpen ⥤ Type) :
    ActualIsCosheaf F ↔ IsCosheaf (Open.actualOrderIso.equivalence.functor ⋙ F) := by
  constructor
  · intro h U ι C B f hf
    let C' : ActualCover (Open.toActual U) ι :=
      ⟨fun i => Open.toActual (C.member i),C.le,C.covers⟩
    apply h (Open.toActual U) ι C' B f
    intro i j V hi hj
    obtain ⟨W,rfl⟩ := Open.toActual_surjective V
    exact hf.below i j W hi hj
  · intro h U ι C B f hf
    obtain ⟨U,rfl⟩ := Open.toActual_surjective U
    rcases C with ⟨member,hle,hcovers⟩
    have hm : ∃ m : ι → Open,(fun i => Open.toActual (m i))=member := by
      choose m hm using fun i => Open.toActual_surjective (member i)
      exact ⟨m,funext hm⟩
    obtain ⟨m,rfl⟩ := hm
    let C' : Cover U ι := ⟨m,hle,hcovers⟩
    apply h U ι C' B f
    intro i j
    exact hf i j (Open.toActual (m i ⊓ m j))
      (Open.actualOrderIso.monotone inf_le_left) (Open.actualOrderIso.monotone inf_le_right)

theorem cosheaf_of_iso {F G : Open ⥤ Type} (e : F ≅ G) (h : IsCosheaf F) :
    IsCosheaf G :=
  cosheaf_of_pushout G ((cosheaf_empty_initial h).ofIso (e.app .empty))
    ((cosheaf_pushout h).of_iso (e.app .D) (e.app .L) (e.app .R) (e.app .whole)
      (e.hom.naturality _) (e.hom.naturality _)
      (e.hom.naturality _) (e.hom.naturality _))

instance : cosheafProperty.IsClosedUnderIsomorphisms where
  of_iso := cosheaf_of_iso

def actualCosheafProperty : ObjectProperty (ActualOpen ⥤ Type) := ActualIsCosheaf

abbrev ActualCoSh := ObjectProperty.FullSubcategory actualCosheafProperty

/-- Reindexing along the proved order isomorphism preserves the full cover axiom. -/
def actualPresentationEquivalence : ActualCoSh ≌ CoSh :=
  Open.actualOrderIso.equivalence.symm.congrLeft.congrFullSubcategory (by
    funext F
    exact propext (actualIsCosheaf_iff F).symm)

/-- Proposition A.1 on the actual category of opens of the three-point space. -/
def actualCosheafEquivalence : ActualCoSh ≌ (WalkingSpan ⥤ Type) :=
  actualPresentationEquivalence.trans cosheafEquivalence

theorem actual_inverse_whole (Y : WalkingSpan ⥤ Type) :
    (actualCosheafEquivalence.inverse.obj Y).obj.obj ⊤=
      pushout (Y.map WalkingSpan.Hom.fst) (Y.map WalkingSpan.Hom.snd) := by
  change extensionValue Y (Open.actualOrderIso.symm ⊤)=_
  rw [Open.actualOrderIso.symm.map_top]
  rfl

theorem actual_restriction (F : ActualCoSh) :
    actualCosheafEquivalence.functor.obj F=
      (basisFunctor ⋙ Open.actualOrderIso.equivalence.functor) ⋙ F.obj := rfl

end CategoricalEssentialIncompleteness.LocalConnectedness.ForkTopology
