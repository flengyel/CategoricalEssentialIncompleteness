/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SliceClosedTheories
public import CategoricalEssentialIncompleteness.SubobjectPredicates

/-! # Predicate lattices in ordinary slices -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u
open CategoryTheory CategoryTheory.Limits

namespace CategoricalEssentialIncompleteness.V46.SliceSubobjectPredicates

variable {C : Type u} [Category.{v} C] {U : C}

def underlying {A : Over U} : Subobject A → Subobject A.left :=
  Subobject.lift (fun _ m _ => Subobject.mk m.left) (by
    intro X Y m n _ _ i hi
    exact Subobject.mk_eq_mk_of_comm _ _ ((Over.forget U).mapIso i)
      (congrArg Over.Hom.left hi))

@[simp] theorem underlying_mk {A X : Over U} (m : X ⟶ A) [Mono m] :
    underlying (Subobject.mk m) = Subobject.mk m.left := rfl

def lift (A : Over U) (T : Subobject A.left) : Subobject A :=
  Subobject.mk (Over.homMk T.arrow : Over.mk (T.arrow ≫ A.hom) ⟶ A)

@[simp] theorem underlying_lift (A : Over U) (T : Subobject A.left) :
    underlying (lift A T) = T := by
  simp [lift]

@[simp] theorem lift_underlying {A : Over U} (T : Subobject A) :
    lift A (underlying T) = T := by
  revert T
  apply Subobject.ind
  intro X m hm
  change lift A (Subobject.mk m.left) = Subobject.mk m
  let i : Over.mk ((Subobject.mk m.left).arrow ≫ A.hom) ≅ X := by
    refine Over.isoMk (Subobject.underlyingIso m.left) ?_
    change (Subobject.underlyingIso m.left).hom ≫ X.hom = _
    rw [← Over.w m, ← Category.assoc, Subobject.underlyingIso_hom_comp_eq_mk]
    rfl
  apply Subobject.mk_eq_mk_of_comm _ _ i
  apply Over.OverMorphism.ext
  change (Subobject.underlyingIso m.left).hom ≫ m.left = _
  exact Subobject.underlyingIso_hom_comp_eq_mk m.left

def orderIso (A : Over U) : Subobject A ≃o Subobject A.left where
  toFun := underlying
  invFun := lift A
  left_inv := lift_underlying
  right_inv := underlying_lift A
  map_rel_iff' := by
    apply Subobject.ind₂
    intro X Y m n hm hn
    change Subobject.mk m.left ≤ Subobject.mk n.left ↔ Subobject.mk m ≤ Subobject.mk n
    constructor
    · intro h
      let k := Subobject.ofMkLEMk m.left n.left h
      have hk : k ≫ Y.hom = X.hom := by
        rw [← Over.w n, ← Category.assoc, Subobject.ofMkLEMk_comp, Over.w m]
      exact Subobject.mk_le_mk_of_comm (Over.homMk k hk)
        (Over.OverMorphism.ext (Subobject.ofMkLEMk_comp h))
    · intro h
      exact Subobject.mk_le_mk_of_comm (Subobject.ofMkLEMk m n h).left
        (congrArg Over.Hom.left (Subobject.ofMkLEMk_comp h))

@[simp] theorem underlying_top (A : Over U) : underlying (⊤ : Subobject A) = ⊤ :=
  (orderIso A).map_top


theorem underlying_injective (A : Over U) : Function.Injective (underlying (A := A)) :=
  (orderIso A).injective

variable [Regular C]
local instance sliceRegular (P : C) : Regular (Over P) := RegularSlices.regular P

theorem underlying_pullback {A B : Over U} (f : A ⟶ B) (W : Subobject B) :
    underlying ((Subobject.pullback f).obj W) =
      (Subobject.pullback f.left).obj (underlying W) := by
  have hW : underlying W = Subobject.mk W.arrow.left :=
    (congrArg underlying (Subobject.mk_arrow W)).symm
  rw [hW, Subobject.pullback_obj]
  simp only [underlying_mk]
  exact (Subobject.pullback_obj_mk
    ((IsPullback.of_hasPullback W.arrow f).map (Over.forget U))).symm

local instance constantLimits (P : C) : PreservesFiniteLimits (constantFamilyFunctor P) :=
  SliceBaseChangeGeometry.constant_preservesFiniteLimits P

theorem underlying_constant {S : C} (U : C) (T : Subobject S) :
    underlying (FiniteLimitSubobjects.object (constantFamilyFunctor U) T) =
      (Subobject.pullback (prod.snd : U ⨯ S ⟶ S)).obj T := by
  change Subobject.mk (prod.map (𝟙 U) T.arrow) = _
  have hp : IsPullback (prod.map (𝟙 U) T.arrow) prod.snd
      (prod.snd : U ⨯ S ⟶ S) T.arrow := by
    apply IsPullback.mk' (by simp)
    · intro R f g h₁ h₂
      apply prod.hom_ext
      · simpa using congrArg (fun k => k ≫ prod.fst) h₁
      · exact h₂
    · intro R f g h
      refine ⟨prod.lift (f ≫ prod.fst) g, ?_, by simp⟩
      apply prod.hom_ext
      · simp
      · simpa using h.symm
  simpa only [Subobject.mk_arrow] using (Subobject.pullback_obj_mk hp.flip).symm

@[simp] theorem underlying_inf {A : Over U} (T W : Subobject A) :
    underlying (T ⊓ W) = underlying T ⊓ underlying W := (orderIso A).map_inf T W


variable [FinitaryExtensive C]
local instance sliceExtensive (P : C) : FinitaryExtensive (Over P) :=
  RegularSlices.finitaryExtensive P

@[simp] theorem underlying_sup {A : Over U} (T W : Subobject A) :
    underlying (T ⊔ W) = underlying T ⊔ underlying W := (orderIso A).map_sup T W

@[simp] theorem underlying_bot (A : Over U) : underlying (⊥ : Subobject A) = ⊥ :=
  (orderIso A).map_bot



omit [FinitaryExtensive C] in
theorem constant_inf {S : C} (U : C) (T W : Subobject S) :
    FiniteLimitSubobjects.object (constantFamilyFunctor U) (T ⊓ W) =
      FiniteLimitSubobjects.object (constantFamilyFunctor U) T ⊓
        FiniteLimitSubobjects.object (constantFamilyFunctor U) W := by
  apply underlying_injective (constantFamily U S)
  rw [underlying_inf, underlying_constant, underlying_constant, underlying_constant,
    Subobject.inf_pullback]

theorem constant_sup {S : C} (U : C) (T W : Subobject S) :
    FiniteLimitSubobjects.object (constantFamilyFunctor U) (T ⊔ W) =
      FiniteLimitSubobjects.object (constantFamilyFunctor U) T ⊔
        FiniteLimitSubobjects.object (constantFamilyFunctor U) W := by
  apply underlying_injective (constantFamily U S)
  rw [underlying_sup, underlying_constant, underlying_constant, underlying_constant,
    SubobjectPredicates.pullback_sup]

theorem constant_bot {S : C} (U : C) :
    FiniteLimitSubobjects.object (constantFamilyFunctor U) (⊥ : Subobject S) = ⊥ := by
  apply underlying_injective (constantFamily U S)
  rw [underlying_bot, underlying_constant, PresentationLemmas.pullback_bot]

omit [FinitaryExtensive C] in
theorem constant_top {S : C} (U : C) :
    FiniteLimitSubobjects.object (constantFamilyFunctor U) (⊤ : Subobject S) = ⊤ := by
  apply underlying_injective (constantFamily U S)
  rw [underlying_top, underlying_constant, Subobject.pullback_top]

theorem constant_consistency {S : C} (U : C) (ν : S ⟶ S) (T : Subobject S)
    (h : T ⊓ (Subobject.pullback ν).obj T = ⊥) :
    FiniteLimitSubobjects.object (constantFamilyFunctor U) T ⊓
      (Subobject.pullback ((constantFamilyFunctor U).map ν)).obj
        (FiniteLimitSubobjects.object (constantFamilyFunctor U) T) = ⊥ := by
  rw [← FiniteLimitSubobjects.object_pullback, ← constant_inf, h, constant_bot]

theorem constant_completeness {S : C} (U : C) (ν : S ⟶ S) (T : Subobject S)
    (h : T ⊔ (Subobject.pullback ν).obj T = ⊤) :
    FiniteLimitSubobjects.object (constantFamilyFunctor U) T ⊔
      (Subobject.pullback ((constantFamilyFunctor U).map ν)).obj
        (FiniteLimitSubobjects.object (constantFamilyFunctor U) T) = ⊤ := by
  rw [← FiniteLimitSubobjects.object_pullback, ← constant_sup, h, constant_top]

variable {Z : C} (point : Z ⟶ U) (hZ : IsTerminal Z)

def fiber (S : C) : S ⟶ U ⨯ S := prod.lift (hZ.from S ≫ point) (𝟙 S)

/-- Evaluation of any slice predicate, without a constant-family hypothesis. -/
def evaluate {S : C} (W : Subobject (constantFamily U S)) : Subobject S :=
  (Subobject.pullback (fiber point hZ S)).obj (underlying W)

omit [FinitaryExtensive C] in
theorem fiber_naturality {S T : C} (f : S ⟶ T) :
    fiber point hZ S ≫ prod.map (𝟙 U) f = f ≫ fiber point hZ T := by
  apply prod.hom_ext
  · simp only [fiber, Category.assoc, prod.map_fst, Category.comp_id,
      prod.lift_fst]
    rw [← Category.assoc, hZ.hom_ext (hZ.from S) (f ≫ hZ.from T)]
  · simp [fiber]

omit [FinitaryExtensive C] in
theorem evaluate_refutation {S : C} (ν : S ⟶ S)
    (W : Subobject (constantFamily U S)) :
    evaluate point hZ ((Subobject.pullback ((constantFamilyFunctor U).map ν)).obj W) =
      (Subobject.pullback ν).obj (evaluate point hZ W) := by
  unfold evaluate
  rw [underlying_pullback, ← Subobject.pullback_comp, ← Subobject.pullback_comp]
  exact congrArg (fun f => (Subobject.pullback f).obj (underlying W))
    (fiber_naturality point hZ ν)

theorem evaluate_consistency {S : C} (ν : S ⟶ S)
    (W : Subobject (constantFamily U S))
    (h : W ⊓ (Subobject.pullback ((constantFamilyFunctor U).map ν)).obj W = ⊥) :
    evaluate point hZ W ⊓ (Subobject.pullback ν).obj (evaluate point hZ W) = ⊥ := by
  rw [← evaluate_refutation]
  change (Subobject.pullback _).obj _ ⊓ (Subobject.pullback _).obj _ = _
  rw [← Subobject.inf_pullback, ← underlying_inf, h, underlying_bot,
    PresentationLemmas.pullback_bot]

theorem evaluate_completeness {S : C} (ν : S ⟶ S)
    (W : Subobject (constantFamily U S))
    (h : W ⊔ (Subobject.pullback ((constantFamilyFunctor U).map ν)).obj W = ⊤) :
    evaluate point hZ W ⊔ (Subobject.pullback ν).obj (evaluate point hZ W) = ⊤ := by
  rw [← evaluate_refutation]
  change (Subobject.pullback _).obj _ ⊔ (Subobject.pullback _).obj _ = _
  rw [← SubobjectPredicates.pullback_sup, ← underlying_sup, h, underlying_top,
    Subobject.pullback_top]

omit [FinitaryExtensive C] in
theorem evaluate_constant {S : C} (T : Subobject S) :
    evaluate point hZ (FiniteLimitSubobjects.object (constantFamilyFunctor U) T) = T := by
  unfold evaluate
  rw [underlying_constant, ← Subobject.pullback_comp]
  simp [fiber, Subobject.pullback_id]

end CategoricalEssentialIncompleteness.V46.SliceSubobjectPredicates
