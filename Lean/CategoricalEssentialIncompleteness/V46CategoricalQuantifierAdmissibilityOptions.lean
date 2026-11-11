/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46CategoricalSubstitution
public import CategoricalEssentialIncompleteness.ComplementedSubobjects

/-! Success subobjects of the actual option operations and Boolean branches. -/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u
open CategoryTheory CategoryTheory.Limits

namespace CategoricalEssentialIncompleteness.V46

variable {D : Type u} [Category.{v} D] [Regular D] [FinitaryExtensive D]

namespace SubobjectLaws

omit [FinitaryExtensive D] in
theorem mk_inf_eq_map_pullback {A X : D} (m : A ⟶ X) [Mono m] (B : Subobject X) :
    Subobject.mk m ⊓ B = (Subobject.map m).obj ((Subobject.pullback m).obj B) := by
  exact Subobject.inf_eq_map_pullback' (MonoOver.mk m) B

end SubobjectLaws

namespace Two

def fiberSubobject {X : D} (b : X ⟶ Two D) (c : Bool) : Subobject X :=
  Subobject.mk (Two.fiberι b c)

theorem fiberSubobject_sup {X : D} (b : X ⟶ Two D) :
    fiberSubobject b false ⊔ fiberSubobject b true = ⊤ :=
  (Two.boundFibers_isCompl b).sup_eq_top

theorem fiberSubobject_comp {X Y : D} (k : X ⟶ Y) (b : Y ⟶ Two D) (c : Bool) :
    fiberSubobject (k ≫ b) c = (Subobject.pullback k).obj (fiberSubobject b c) := by
  change boundFiber (k ≫ b) (Two.point c) =
    (Subobject.pullback k).obj (boundFiber b (Two.point c))
  rw [PresentationLemmas.boundFiber_eq_pullback, PresentationLemmas.boundFiber_eq_pullback,
    Subobject.pullback_comp]

end Two

namespace OptionSyntax

/-- The actual success subobject is the inverse image of the success injection. -/
def success {X Y : D} (f : X ⟶ obj Y) : Subobject X :=
  (Subobject.pullback f).obj (Subobject.mk (coprod.inr : Y ⟶ obj Y))

theorem success_eq_mk {X Y : D} (f : X ⟶ obj Y) :
    success f = Subobject.mk (pullback.fst f coprod.inr) :=
  Subobject.pullback_obj_mk (IsPullback.of_hasPullback f coprod.inr).flip

theorem success_comp {X Y Z : D} (k : X ⟶ Y) (f : Y ⟶ obj Z) :
    success (k ≫ f) = (Subobject.pullback k).obj (success f) :=
  Subobject.pullback_comp k f _

@[simp] theorem success_ok {X Y : D} (f : X ⟶ Y) :
    success (f ≫ (coprod.inr : Y ⟶ obj Y)) = ⊤ := by
  unfold success
  rw [Subobject.pullback_comp, Subobject.pullback_self, Subobject.pullback_top]

@[simp] theorem success_fail {X Y : D} : success (fail : X ⟶ obj Y) = ⊥ := by
  have h : IsPullback (initial.to (⊤_ D)) (initial.to Y)
      (coprod.inl : ⊤_ D ⟶ obj Y) coprod.inr :=
    FinitaryExtensive.isPullback_initial_to_binaryCofan
      (c := BinaryCofan.mk (coprod.inl : ⊤_ D ⟶ obj Y) coprod.inr)
      (coprodIsCoprod (⊤_ D) Y)
  unfold fail success
  rw [Subobject.pullback_comp, Subobject.pullback_obj_mk h.flip,
    ← Subobject.bot_eq_initial_to, PresentationLemmas.pullback_bot]

/-- A coproduct case with failure on the first fiber and success on the second
has exactly the second input fiber as its success subobject. -/
theorem success_caseOf {X A B Y : D} (f : X ⟶ A ⨿ B)
    (a : pullback f coprod.inl ⟶ ⊤_ D) (b : pullback f coprod.inr ⟶ Y) :
    success (SumFibers.caseOf f (a ≫ coprod.inl) (b ≫ coprod.inr)) =
      Subobject.mk (pullback.fst f coprod.inr) := by
  let r := SumFibers.caseOf f (a ≫ coprod.inl) (b ≫ coprod.inr)
  have hv := (BinaryCofan.isVanKampen_iff _).mp
    (FinitaryExtensive.vanKampen _ (coprodIsCoprod (⊤_ D) Y))
    (BinaryCofan.mk (pullback.fst f coprod.inl) (pullback.fst f coprod.inr))
  have hp : IsPullback (pullback.fst f coprod.inr) b r coprod.inr :=
    ((hv a b r (SumFibers.inl_caseOf f _ _).symm
      (SumFibers.inr_caseOf f _ _).symm).mp ⟨SumFibers.isColimit f⟩).2
  exact Subobject.pullback_obj_mk hp.flip

/-- Mapping a successful option changes only its value, and never its success
subobject; no injectivity of the value map is required. -/
theorem success_map {Y Z : D} (f : Y ⟶ Z) :
    success (map f) = Subobject.mk (coprod.inr : Y ⟶ obj Y) := by
  have hv := (BinaryCofan.isVanKampen_iff _).mp
    (FinitaryExtensive.vanKampen _ (coprodIsCoprod (⊤_ D) Z))
    (BinaryCofan.mk (coprod.inl : ⊤_ D ⟶ obj Y) coprod.inr)
  have hp : IsPullback (coprod.inr : Y ⟶ obj Y) f (map f) coprod.inr :=
    ((hv (𝟙 _) f (map f) (by simp [map]) (by simp [map])).mp
      ⟨coprodIsCoprod (⊤_ D) Y⟩).2
  exact Subobject.pullback_obj_mk hp.flip

theorem success_map_comp {X Y Z : D} (k : X ⟶ obj Y) (f : Y ⟶ Z) :
    success (k ≫ map f) = success k := by
  rw [success_comp, success_map]
  rfl

/-- The lifted coefficient constructor succeeds exactly when its recursive
formula input succeeds; the constructor itself need not be injective. -/
theorem success_coefficient {V Y Z : D} (h : V ⨯ Y ⟶ Z) :
    success (coefficient h) = success (prod.snd : V ⨯ obj Y ⟶ obj Y) := by
  rw [success_eq_mk (prod.snd : V ⨯ obj Y ⟶ obj Y)]
  simpa only [coefficient, fail, Category.assoc] using
    success_caseOf (prod.snd : V ⨯ obj Y ⟶ obj Y) (terminal.from _)
      (prod.lift (pullback.fst _ coprod.inr ≫ prod.fst)
        (pullback.snd _ coprod.inr) ≫ h)

theorem success_coefficient_comp {X V Y Z : D} (h : V ⨯ Y ⟶ Z)
    (k : X ⟶ V ⨯ obj Y) :
    success (k ≫ coefficient h) = success (k ≫ prod.snd) := by
  rw [success_comp, success_coefficient, ← success_comp]

/-- Success of a Boolean branch is the disjoint union of the two restricted
success subobjects, proved on the source fibers. -/
theorem success_branch {X Y : D} (b : X ⟶ Two D) (f g : X ⟶ obj Y) :
    success (Two.branch b f g) =
      (Two.fiberSubobject b false ⊓ success f) ⊔
        (Two.fiberSubobject b true ⊓ success g) := by
  have hf (c : Bool) : Two.fiberSubobject b c ⊓ success (Two.branch b f g) =
      Two.fiberSubobject b c ⊓ success (if c then g else f) := by
    unfold Two.fiberSubobject
    rw [SubobjectLaws.mk_inf_eq_map_pullback, SubobjectLaws.mk_inf_eq_map_pullback]
    congr 1
    rw [← success_comp, ← success_comp, Two.fiberι_branch]
  calc
    _ = (Two.fiberSubobject b false ⊔ Two.fiberSubobject b true) ⊓
        success (Two.branch b f g) := by rw [Two.fiberSubobject_sup, top_inf_eq]
    _ = (Two.fiberSubobject b false ⊓ success (Two.branch b f g)) ⊔
        (Two.fiberSubobject b true ⊓ success (Two.branch b f g)) := inf_sup_right _ _ _
    _ = _ := by rw [hf false, hf true]; rfl

end OptionSyntax
end CategoricalEssentialIncompleteness.V46
