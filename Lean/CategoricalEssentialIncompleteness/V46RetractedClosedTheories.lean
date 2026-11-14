/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46RetractedRuleComparison

/-! # Closed arbitrary slice theories evaluated into the original calculus -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v₁ v₂ u₁ u₂
open CategoryTheory CategoryTheory.Limits

namespace CategoricalEssentialIncompleteness.V46.RetractedClosedTheories

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
variable [Regular C] [Regular D] [HasFiniteCoproducts C] [HasFiniteCoproducts D]
variable (B : C ⥤ D) (E : D ⥤ C) [PreservesFiniteLimits B] [PreservesFiniteLimits E]
variable (e : B ⋙ E ≅ 𝟭 C)

def backObject {S : C} (W : Subobject (B.obj S)) : Subobject S :=
  (Subobject.pullback (e.inv.app S)).obj (FiniteLimitSubobjects.object E W)

def axiomMap {S : C} (W : Subobject (B.obj S)) :
    (backObject B E e W : C) ⟶ E.obj (W : D) :=
  Subobject.pullbackπ (e.inv.app S) (FiniteLimitSubobjects.object E W) ≫
    (Subobject.underlyingIso (E.map W.arrow)).hom

omit [Regular D] [HasFiniteCoproducts C] [HasFiniteCoproducts D]
    [PreservesFiniteLimits B] in
theorem axiomMap_law {S : C} (W : Subobject (B.obj S)) :
    axiomMap B E e W ≫ E.map W.arrow = (backObject B E e W).arrow ≫ e.inv.app S := by
  rw [axiomMap, Category.assoc, Subobject.underlyingIso_hom_comp_eq_mk]
  exact (Subobject.isPullback (e.inv.app S) (FiniteLimitSubobjects.object E W)).w

variable {V F L S : C} {logical : L ⟶ F} {sentence : S ⟶ F}
variable {all : V ⨯ F ⟶ F} {imp : F ⨯ F ⟶ F}
variable (proofs : (A : Subobject S) →
  Endofunctor.Algebra (firstOrderRules logical sentence A.arrow all imp).inference)
variable (proofInitial : ∀ A, IsInitial (proofs A))
variable (sliceProofs : (W : Subobject (B.obj S)) →
  Endofunctor.Algebra (firstOrderRules (B.map logical) (B.map sentence) W.arrow
    (FirstOrderRuleTransport.mappedAll B all) (FirstOrderRuleTransport.mappedImp B imp)).inference)
variable (sliceInitial : ∀ W, IsInitial (sliceProofs W))

include proofInitial sliceInitial in
theorem closed_back (W : Subobject (B.obj S))
    (hW : FirstOrderReflection.generated sliceProofs W = W) :
    FirstOrderReflection.generated proofs (backObject B E e W) = backObject B E e W := by
  let A := backObject B E e W
  let m := image.ι (sliceProofs W).a.hom
  let τ := RetractedRuleComparison.translation B E e logical sentence all imp W A
    (axiomMap B E e W) (axiomMap_law B E e W)
  have hc := FirstOrderReflection.formula_closed sliceProofs sliceInitial W
  have he := FiniteRuleTransport.map_closed E
    (firstOrderRules (B.map logical) (B.map sentence) W.arrow
      (FirstOrderRuleTransport.mappedAll B all) (FirstOrderRuleTransport.mappedImp B imp)) m hc
  have hr := τ.closed_pullback (E.map m) he
  obtain ⟨w, hw⟩ := (firstOrder_least_image logical sentence A.arrow all imp
    (proofs A) (proofInitial A)).2 (pullback.snd (E.map m) (e.inv.app F)) hr
  have hg : FirstOrderReflection.generated proofs A ≤
      (Subobject.pullback sentence).obj
        (Subobject.mk (pullback.snd (E.map m) (e.inv.app F))) := by
    rw [FirstOrderReflection.generated_eq_pullback]
    exact (Subobject.pullback sentence).monotone (Subobject.mk_le_mk_of_comm w hw)
  have hs : sentence ≫ e.inv.app F = e.inv.app S ≫ E.map (B.map sentence) :=
    e.inv.naturality sentence
  have hws : (Subobject.pullback (B.map sentence)).obj
      (FirstOrderReflection.formulaTheory sliceProofs W) = W :=
    (FirstOrderReflection.generated_eq_pullback sliceProofs W).symm.trans hW
  have ha : A = (Subobject.pullback sentence).obj
      (Subobject.mk (pullback.snd (E.map m) (e.inv.app F))) := by
    calc
      A = (Subobject.pullback (e.inv.app S)).obj
          (FiniteLimitSubobjects.object E ((Subobject.pullback (B.map sentence)).obj
            (FirstOrderReflection.formulaTheory sliceProofs W))) :=
        congrArg (fun T => (Subobject.pullback (e.inv.app S)).obj
          (FiniteLimitSubobjects.object E T)) hws.symm
      _ = _ := by
        rw [FiniteLimitSubobjects.object_pullback, ← Subobject.pullback_comp,
          ← hs, Subobject.pullback_comp]
        change (Subobject.pullback sentence).obj
          ((Subobject.pullback (e.inv.app F)).obj
            (FiniteLimitSubobjects.object E (Subobject.mk m))) = _
        rw [FiniteLimitSubobjects.object_mk,
          Subobject.pullback_obj_mk (IsPullback.of_hasPullback (E.map m) (e.inv.app F))]
  exact le_antisymm (hg.trans_eq ha.symm) (FirstOrderReflection.extensive proofs A)

end CategoricalEssentialIncompleteness.V46.RetractedClosedTheories
