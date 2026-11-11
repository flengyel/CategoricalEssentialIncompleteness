/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.ForkCosheafCondition

/-! # The cosheaf axiom is exactly the empty value and whole-space pushout -/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open CategoryTheory CategoryTheory.Limits

namespace CategoricalEssentialIncompleteness.LocalConnectedness.ForkTopology

def wholeFamily {F : Open ⥤ Type}
    (s : PushoutCocone (F.map (homOfLE Open.d_le_l)) (F.map (homOfLE Open.d_le_r))) :
    ∀ i : Bool,F.obj (Cover.wholeCover.member i) ⟶ s.pt
  | false => s.inr
  | true => s.inl

theorem wholeFamily_compatible {F : Open ⥤ Type}
    (s : PushoutCocone (F.map (homOfLE Open.d_le_l)) (F.map (homOfLE Open.d_le_r))) :
    Compatible F Cover.wholeCover (wholeFamily s) := by
  intro i j
  cases i <;> cases j
  · rfl
  · exact s.condition.symm
  · exact s.condition
  · rfl

theorem cosheaf_pushout {F : Open ⥤ Type} (hF : IsCosheaf F) : PushoutCondition F := by
  let E (s : PushoutCocone (F.map (homOfLE Open.d_le_l)) (F.map (homOfLE Open.d_le_r))) :=
    hF .whole Bool Cover.wholeCover s.pt (wholeFamily s) (wholeFamily_compatible s)
  have w : F.map (homOfLE Open.d_le_l) ≫ F.map (homOfLE Open.l_le_whole)=
      F.map (homOfLE Open.d_le_r) ≫ F.map (homOfLE Open.r_le_whole) := by simp
  refine IsPushout.of_isColimit (c := PushoutCocone.mk
    (F.map (homOfLE Open.l_le_whole)) (F.map (homOfLE Open.r_le_whole)) w) ?_
  refine PushoutCocone.IsColimit.mk w (fun s => Classical.choose (E s)) ?_ ?_ ?_
  · intro s
    exact (Classical.choose_spec (E s)).1 true
  · intro s
    exact (Classical.choose_spec (E s)).1 false
  · intro s m hl hr
    apply (Classical.choose_spec (E s)).2 m
    intro i
    cases i
    · exact hr
    · exact hl

/-- All indexed cover coequalizer axioms, with the empty cover, are equivalent
to precisely the conditions used by the manuscript's construction. -/
theorem cosheaf_iff_initial_pushout (F : Open ⥤ Type) :
    IsCosheaf F ↔ Nonempty (IsInitial (F.obj .empty)) ∧ PushoutCondition F := by
  constructor
  · intro h
    exact ⟨⟨cosheaf_empty_initial h⟩,cosheaf_pushout h⟩
  · rintro ⟨⟨h0⟩,hp⟩
    exact cosheaf_of_pushout F h0 hp

end CategoricalEssentialIncompleteness.LocalConnectedness.ForkTopology
