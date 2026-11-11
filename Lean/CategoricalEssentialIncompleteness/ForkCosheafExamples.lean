/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.ForkCosheafQuotient
public import CategoricalEssentialIncompleteness.EffectiveForkLimits
public import Mathlib.CategoryTheory.Subterminal
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Terminal
public import Mathlib.SetTheory.Cardinal.Finite

/-! # Products and monomorphisms of cosheaves are not computed at every open -/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.RestrictionCategory

namespace CategoricalEssentialIncompleteness.LocalConnectedness.ForkTopology

namespace Examples

open EnumerableCarriers

abbrev E := WalkingSpan ⥤ EnumerableCarriers.Total
def one : EnumerableCarriers.Total := ⟨terminalCarrier⟩
def zero : EnumerableCarriers.Total := ⟨emptyCarrier⟩

def H : E := span (initialArrow one) (initialArrow one)
def T : E := span (𝟙 one) (𝟙 one)

theorem empty_subterminal : IsSubterminal zero := by
  intro Z f g
  apply WideSubcategory.hom_ext
  apply val_ext_on_source
  intro x hx
  obtain ⟨y,hy⟩ := Part.dom_iff_mem.mp ((EnumerableCarriers.total_iff f.hom).mp f.property x hx)
  exact False.elim (val_target f.hom x y hy)

theorem H_subterminal : IsSubterminal H := by
  intro Z f g
  apply NatTrans.ext
  funext j
  rcases j with _ | (_ | _)
  · exact empty_subterminal _ _
  · exact terminalIsTerminal.hom_ext _ _
  · exact terminalIsTerminal.hom_ext _ _

def H_product_iso : H ⨯ H ≅ H := by
  letI := H_subterminal.isIso_diag
  exact (asIso (diag H)).symm

def T_terminal : IsTerminal T := Functor.isTerminal (by
  intro j
  rcases j with _ | (_ | _)
  all_goals exact terminalIsTerminal)

def H_to_T : H ⟶ T := T_terminal.from H

instance H_to_T_mono : Mono H_to_T := H_subterminal.mono_isTerminal_from T_terminal

def setDiagramFunctor : E ⥤ (WalkingSpan ⥤ Type) :=
  (Functor.whiskeringRight _ _ _).obj underlying

def wholeFunctor : E ⥤ Type := setDiagramFunctor ⋙ actualCosheafEquivalence.inverse ⋙
  actualCosheafProperty.ι ⋙ (evaluation _ _).obj ⊤

def oneElement : underlying.obj one := ⟨0,rfl⟩

theorem one_eq (x : underlying.obj one) : x=oneElement := by
  apply Subtype.ext
  exact x.property

theorem H_bool_condition :
    (setDiagramFunctor.obj H).map WalkingSpan.Hom.fst ≫ (↾fun _ => false) =
      (setDiagramFunctor.obj H).map WalkingSpan.Hom.snd ≫ (↾fun _ => true) := by
  apply ConcreteCategory.hom_ext
  intro x
  exact False.elim x.property

def H_bool_cocone : PushoutCocone
    ((setDiagramFunctor.obj H).map WalkingSpan.Hom.fst)
    ((setDiagramFunctor.obj H).map WalkingSpan.Hom.snd) :=
  PushoutCocone.mk (↾fun _ => false) (↾fun _ => true) H_bool_condition

def H_bool_isColimit : IsColimit H_bool_cocone :=
  PushoutCocone.IsColimit.mk H_bool_condition
    (fun s => ↾fun b : Bool => if b then s.inr oneElement else s.inl oneElement)
    (by
      intro s
      apply ConcreteCategory.hom_ext
      intro x
      change s.inl oneElement=s.inl x
      rw [one_eq x])
    (by
      intro s
      apply ConcreteCategory.hom_ext
      intro x
      change s.inr oneElement=s.inr x
      rw [one_eq x])
    (by
      intro s m hl hr
      apply ConcreteCategory.hom_ext
      intro b
      cases b
      · exact ConcreteCategory.congr_hom hl oneElement
      · exact ConcreteCategory.congr_hom hr oneElement)

def H_whole_iso : wholeFunctor.obj H ≅ Bool :=
  eqToIso (actual_inverse_whole _) ≪≫
    (IsPushout.of_isColimit (c := H_bool_cocone) H_bool_isColimit).isoPushout.symm

theorem H_whole_card : Nat.card (wholeFunctor.obj H)=2 :=
  (Nat.card_congr H_whole_iso.toEquiv).trans (by simp [Nat.card_eq_fintype_card])

theorem H_product_whole_card : Nat.card (wholeFunctor.obj (H ⨯ H))=2 :=
  (Nat.card_congr (wholeFunctor.mapIso H_product_iso).toEquiv).trans H_whole_card

theorem H_whole_square_card : Nat.card (wholeFunctor.obj H × wholeFunctor.obj H)=4 := by
  rw [Nat.card_prod,H_whole_card]

theorem H_product_whole_not_equiv_square :
    ¬ Nonempty (wholeFunctor.obj (H ⨯ H) ≃ (wholeFunctor.obj H × wholeFunctor.obj H)) := by
  rintro ⟨e⟩
  have h := Nat.card_congr e
  rw [H_product_whole_card,H_whole_square_card] at h
  norm_num at h

theorem T_whole_subsingleton : Subsingleton (wholeFunctor.obj T) := by
  let F := setDiagramFunctor.obj T
  let r := F.map WalkingSpan.Hom.fst
  let s := F.map WalkingSpan.Hom.snd
  have hr : r=𝟙 (underlying.obj one) := by simp [r,F,setDiagramFunctor,T]
  have hs : s=𝟙 (underlying.obj one) := by simp [s,F,setDiagramFunctor,T]
  have hi : IsIso (pushout.inl r s) := by
    letI : IsIso s := by
      rw [hs]
      exact (Iso.refl (underlying.obj one : Type)).isIso_hom
    exact (IsPushout.of_hasPushout r s).isIso_inl_of_isIso
  letI := hi
  let e : wholeFunctor.obj T ≅ underlying.obj one :=
    eqToIso (actual_inverse_whole _) ≪≫ (asIso (pushout.inl r s)).symm
  refine ⟨fun x y => e.toEquiv.injective ?_⟩
  exact (one_eq (e.hom x)).trans (one_eq (e.hom y)).symm

/-- The same actual monomorphism has a noninjective whole-space component. -/
theorem H_to_T_whole_not_injective : ¬ Function.Injective (wholeFunctor.map H_to_T) := by
  intro hi
  letI := T_whole_subsingleton
  have he : H_whole_iso.inv false=H_whole_iso.inv true :=
    hi (Subsingleton.elim _ _)
  have h := H_whole_iso.toEquiv.symm.injective he
  exact Bool.false_ne_true h

end Examples
end CategoricalEssentialIncompleteness.LocalConnectedness.ForkTopology
