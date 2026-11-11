/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.ForkTopology
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-! # Arbitrary open covers and the exact cosheaf gluing property -/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open CategoryTheory CategoryTheory.Limits

namespace CategoricalEssentialIncompleteness.LocalConnectedness.ForkTopology

structure Cover (U : Open) (ι : Type) where
  member : ι → Open
  le : ∀ i,member i ≤ U
  covers : ∀ p ∈ U,∃ i,p ∈ member i

namespace Open

theorem proper_witness : ∀ U : Open,U≠empty → U≠whole →
    ∃ p : Point,p ∈ U ∧ ∀ V : Open,V ≤ U → p ∈ V → V=U := by decide

theorem containing_a : ∀ U : Open,Point.a ∈ U → U=L ∨ U=whole := by decide
theorem containing_b : ∀ U : Open,Point.b ∈ U → U=R ∨ U=whole := by decide
theorem proper_below_side : ∀ U : Open,U≠whole → U ≤ L ∨ U ≤ R := by decide

end Open

namespace Cover

variable {U : Open} {ι : Type}

theorem contains_proper (C : Cover U ι) (hne : U≠.empty) (ht : U≠.whole) :
    ∃ i,C.member i=U := by
  obtain ⟨p,hp,h⟩ := Open.proper_witness U hne ht
  obtain ⟨i,hi⟩ := C.covers p hp
  exact ⟨i,h _ (C.le i) hi⟩

theorem contains_sides (C : Cover .whole ι) (ht : ∀ i,C.member i≠.whole) :
    (∃ i,C.member i=.L) ∧ (∃ i,C.member i=.R) := by
  obtain ⟨i,hi⟩ := C.covers .a (by decide)
  obtain ⟨j,hj⟩ := C.covers .b (by decide)
  exact ⟨⟨i,(Open.containing_a _ hi).resolve_right (ht i)⟩,
    ⟨j,(Open.containing_b _ hj).resolve_right (ht j)⟩⟩

theorem empty_member (C : Cover .empty ι) (i : ι) : C.member i=.empty :=
  bot_unique (C.le i)

def emptyCover : Cover .empty Empty where
  member := Empty.elim
  le i := Empty.elim i
  covers p hp := False.elim (by simpa [Open.members] using hp)

def wholeCover : Cover .whole Bool where
  member i := if i then .L else .R
  le _ := le_top
  covers p _ := by
    cases p
    · exact ⟨true,by decide⟩
    · exact ⟨false,by decide⟩
    · exact ⟨true,by decide⟩

end Cover

@[reassoc (attr := simp)] theorem map_comp_le (F : Open ⥤ Type) {U V W : Open}
    (h : U ≤ V) (k : V ≤ W) :
    F.map (homOfLE h) ≫ F.map (homOfLE k)=F.map (homOfLE (h.trans k)) :=
  (F.map_comp _ _).symm

@[simp] theorem map_self_le (F : Open ⥤ Type) (U : Open) (h : U ≤ U) :
    F.map (homOfLE h)=𝟙 (F.obj U) := F.map_id U

def Compatible (F : Open ⥤ Type) {U : Open} {ι : Type} (C : Cover U ι)
    {B : Type} (f : ∀ i,F.obj (C.member i) ⟶ B) : Prop :=
  ∀ i j,F.map (homOfLE (inf_le_left : C.member i ⊓ C.member j ≤ C.member i)) ≫ f i=
    F.map (homOfLE (inf_le_right : C.member i ⊓ C.member j ≤ C.member j)) ≫ f j

theorem Compatible.below {F : Open ⥤ Type} {U : Open} {ι : Type} {C : Cover U ι}
    {B : Type} {f : ∀ i,F.obj (C.member i) ⟶ B} (h : Compatible F C f)
    (i j : ι) (V : Open) (hi : V ≤ C.member i) (hj : V ≤ C.member j) :
    F.map (homOfLE hi) ≫ f i=F.map (homOfLE hj) ≫ f j := by
  have hv := le_inf hi hj
  calc
    _ = F.map (homOfLE hv) ≫ F.map (homOfLE inf_le_left) ≫ f i := by simp
    _ = F.map (homOfLE hv) ≫ F.map (homOfLE inf_le_right) ≫ f j :=
      congrArg (fun k => F.map (homOfLE hv) ≫ k) (h i j)
    _ = _ := by simp

/-- The universal property of the manuscript's cover coequalizer, stated
directly as existence and uniqueness of the compatible cocone's descent. -/
def IsCosheaf (F : Open ⥤ Type) : Prop :=
  ∀ (U : Open) (ι : Type) (C : Cover U ι) (B : Type)
    (f : ∀ i,F.obj (C.member i) ⟶ B),Compatible F C f →
      ∃! h : F.obj U ⟶ B,∀ i,F.map (homOfLE (C.le i)) ≫ h=f i

theorem descent_of_member {F : Open ⥤ Type} {U : Open} {ι : Type} (C : Cover U ι)
    {B : Type} (f : ∀ i,F.obj (C.member i) ⟶ B) (hf : Compatible F C f)
    (i₀ : ι) (he : C.member i₀=U) :
    ∃! h : F.obj U ⟶ B,∀ i,F.map (homOfLE (C.le i)) ≫ h=f i := by
  have back : U ≤ C.member i₀ := by rw [he]
  let h := F.map (homOfLE back) ≫ f i₀
  refine ⟨h,?_,?_⟩
  · intro i
    change F.map (homOfLE (C.le i)) ≫ F.map (homOfLE back) ≫ f i₀=f i
    rw [map_comp_le_assoc]
    simpa only [map_self_le,Category.id_comp] using
      hf.below i₀ i (C.member i) ((C.le i).trans back) le_rfl
  · intro m hm
    calc
      m = F.map (homOfLE back) ≫ F.map (homOfLE (C.le i₀)) ≫ m := by simp
      _ = h := by rw [hm i₀]

end CategoricalEssentialIncompleteness.LocalConnectedness.ForkTopology
