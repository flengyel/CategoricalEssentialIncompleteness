/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.ForkCovers
public import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal

/-! # Empty value and the whole-space pushout imply all cosheaf cover axioms -/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open CategoryTheory CategoryTheory.Limits

namespace CategoricalEssentialIncompleteness.LocalConnectedness.ForkTopology

namespace Open
theorem d_le_l : D ≤ L := by decide
theorem d_le_r : D ≤ R := by decide
theorem l_le_whole : L ≤ whole := le_top
theorem r_le_whole : R ≤ whole := le_top
end Open

def PushoutCondition (F : Open ⥤ Type) : Prop :=
  IsPushout (F.map (homOfLE Open.d_le_l)) (F.map (homOfLE Open.d_le_r))
    (F.map (homOfLE Open.l_le_whole)) (F.map (homOfLE Open.r_le_whole))

theorem descent_of_sides {F : Open ⥤ Type} {ι : Type} (C : Cover .whole ι)
    {B : Type} (f : ∀ i,F.obj (C.member i) ⟶ B) (hf : Compatible F C f)
    (hp : PushoutCondition F) (ht : ∀ i,C.member i≠.whole) :
    ∃! h : F.obj .whole ⟶ B,∀ i,F.map (homOfLE (C.le i)) ≫ h=f i := by
  obtain ⟨⟨iL,hL⟩,⟨iR,hR⟩⟩ := C.contains_sides ht
  have bL : Open.L ≤ C.member iL := by rw [hL]
  have bR : Open.R ≤ C.member iR := by rw [hR]
  let fL := F.map (homOfLE bL) ≫ f iL
  let fR := F.map (homOfLE bR) ≫ f iR
  have hw : F.map (homOfLE Open.d_le_l) ≫ fL=F.map (homOfLE Open.d_le_r) ≫ fR := by
    simpa only [fL,fR,map_comp_le_assoc] using
      hf.below iL iR .D (Open.d_le_l.trans bL) (Open.d_le_r.trans bR)
  let h := hp.desc fL fR hw
  have hl : F.map (homOfLE Open.l_le_whole) ≫ h=fL := hp.inl_desc fL fR hw
  have hr : F.map (homOfLE Open.r_le_whole) ≫ h=fR := hp.inr_desc fL fR hw
  refine ⟨h,?_,?_⟩
  · intro i
    rcases Open.proper_below_side (C.member i) (ht i) with hi | hi
    · calc
        _ = F.map (homOfLE hi) ≫ F.map (homOfLE Open.l_le_whole) ≫ h := by simp
        _ = F.map (homOfLE hi) ≫ fL := by rw [hl]
        _ = f i := by
          dsimp only [fL]
          rw [map_comp_le_assoc]
          simpa only [map_self_le,Category.id_comp] using
            hf.below iL i (C.member i) (hi.trans bL) le_rfl
    · calc
        _ = F.map (homOfLE hi) ≫ F.map (homOfLE Open.r_le_whole) ≫ h := by simp
        _ = F.map (homOfLE hi) ≫ fR := by rw [hr]
        _ = f i := by
          dsimp only [fR]
          rw [map_comp_le_assoc]
          simpa only [map_self_le,Category.id_comp] using
            hf.below iR i (C.member i) (hi.trans bR) le_rfl
  · intro m hm
    apply hp.hom_ext
    · calc
        _ = F.map (homOfLE bL) ≫ F.map (homOfLE (C.le iL)) ≫ m := by simp
        _ = fL := by rw [hm iL]
        _ = _ := hl.symm
    · calc
        _ = F.map (homOfLE bR) ≫ F.map (homOfLE (C.le iR)) ≫ m := by simp
        _ = fR := by rw [hm iR]
        _ = _ := hr.symm

/-- This implication treats arbitrary indexed open covers, including the
empty cover. It does not assume covers have finitely many members. -/
theorem cosheaf_of_pushout (F : Open ⥤ Type) (h0 : IsInitial (F.obj .empty))
    (hp : PushoutCondition F) : IsCosheaf F := by
  classical
  intro U ι C B f hf
  by_cases he : U=.empty
  · subst U
    refine ⟨h0.to B,?_,?_⟩
    · intro i
      have hi : IsInitial (F.obj (C.member i)) :=
        h0.ofIso (F.mapIso (eqToIso (C.empty_member i))).symm
      exact hi.hom_ext _ _
    · intro m _
      exact h0.hom_ext _ _
  · by_cases ht : U=.whole
    · subst U
      by_cases hm : ∃ i,C.member i=.whole
      · obtain ⟨i,hi⟩ := hm
        exact descent_of_member C f hf i hi
      · exact descent_of_sides C f hf hp (fun i hi => hm ⟨i,hi⟩)
    · obtain ⟨i,hi⟩ := C.contains_proper he ht
      exact descent_of_member C f hf i hi

def cosheaf_empty_initial {F : Open ⥤ Type} (hF : IsCosheaf F) : IsInitial (F.obj .empty) := by
  let E (B : Type) := hF .empty Empty Cover.emptyCover B
    (fun i => Empty.elim i) (fun i => Empty.elim i)
  exact IsInitial.ofUniqueHom (fun B => Classical.choose (E B))
    (fun B m => (Classical.choose_spec (E B)).2 m (fun i => Empty.elim i))

end CategoricalEssentialIncompleteness.LocalConnectedness.ForkTopology
