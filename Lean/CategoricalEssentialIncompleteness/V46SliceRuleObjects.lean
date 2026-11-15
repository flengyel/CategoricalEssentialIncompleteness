/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module
public import CategoricalEssentialIncompleteness.V46SliceFinitePowers

/-! # Rule-instance pullbacks after forgetting the common parameter -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v u
open CategoryTheory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness.V46.SliceRuleObjects
variable {D : Type u} [Category.{v} D] [Regular D] {P : D}
local instance : Regular (Over P) := RegularSlices.regular P
variable {F : Over P} {N : ℕ} (R : RulePresentation F N)

def rules : RulePresentation F.left N where
  instances i := (R.instances i).left
  premises i := (R.premises i).left ≫ SliceFinitePowers.comparison F i.val
  conclusion i := (R.conclusion i).left

variable (Q : Over F) (i : Fin (N + 1))
local notation "Q₀" => Functor.obj (CategoryTheory.Equivalence.functor (Over.iteratedSliceEquiv F)) Q

def forward : (R.ruleObject Q i).left ⟶ (rules R).ruleObject (Q₀) i :=
  pullback.lift (pullback.fst (R.premises i) (finitePowerMap Q.hom i.val)).left
    ((pullback.snd (R.premises i) (finitePowerMap Q.hom i.val)).left ≫
      SliceFinitePowers.comparison Q.left i.val) (by
      change _ ≫ ((R.premises i).left ≫ SliceFinitePowers.comparison F i.val) = _
      rw [← Category.assoc]
      have h := congrArg Over.Hom.left (pullback.condition (f := R.premises i)
        (g := finitePowerMap Q.hom i.val))
      simp only [Over.comp_left] at h
      rw [h, Category.assoc, SliceFinitePowers.naturality]
      simp only [Category.assoc]
      rfl)

def parameterObject : Over P :=
  Over.mk (pullback.fst ((rules R).premises i)
    (finitePowerMap Q.hom.left i.val) ≫ (R.instances i).hom)

def label : parameterObject R Q i ⟶ R.instances i :=
  Over.homMk (pullback.fst _ _) rfl

def children : parameterObject R Q i ⟶ finitePower Q.left i.val :=
  SliceFinitePowers.lift Q.hom i.val (pullback.snd _ _) (label R Q i ≫ R.premises i)
    (by
      change pullback.snd _ _ ≫ finitePowerMap Q.hom.left i.val =
        (pullback.fst _ _ ≫ (R.premises i).left) ≫ SliceFinitePowers.comparison F i.val
      rw [Category.assoc]
      exact (pullback.condition (f := (rules R).premises i)
        (g := finitePowerMap Q.hom.left i.val)).symm)

def backward : parameterObject R Q i ⟶ R.ruleObject Q i :=
  pullback.lift (label R Q i) (children R Q i)
    (SliceFinitePowers.lift_map Q.hom i.val _ _ _).symm

def forwardOver : R.ruleObject Q i ⟶ parameterObject R Q i :=
  Over.homMk (forward R Q i) (by
    change forward R Q i ≫ (pullback.fst _ _ ≫ (R.instances i).hom) = _
    rw [← Category.assoc, forward, pullback.lift_fst]
    exact Over.w (pullback.fst (R.premises i) (finitePowerMap Q.hom i.val)))

theorem forward_backward : forwardOver R Q i ≫ backward R Q i = 𝟙 _ := by
  apply pullback.hom_ext
  · rw [Category.assoc, backward, pullback.lift_fst, Category.id_comp]
    apply Over.OverMorphism.ext
    change forward R Q i ≫ pullback.fst _ _ = _
    exact pullback.lift_fst _ _ _
  · rw [Category.assoc, backward, pullback.lift_snd, Category.id_comp]
    apply SliceFinitePowers.hom_ext i.val
    simp only [Over.comp_left]
    change (forward R Q i ≫ (children R Q i).left) ≫ _ = _
    rw [Category.assoc, children, SliceFinitePowers.lift_value]
    exact pullback.lift_snd _ _ _

theorem backward_forward : backward R Q i ≫ forwardOver R Q i = 𝟙 _ := by
  apply Over.OverMorphism.ext
  simp only [Over.comp_left, Over.id_left]
  apply pullback.hom_ext
  · change ((backward R Q i).left ≫ forward R Q i) ≫ pullback.fst _ _ = _
    rw [Category.assoc, forward, pullback.lift_fst, Category.id_comp]
    exact congrArg Over.Hom.left (pullback.lift_fst _ _ _)
  · change ((backward R Q i).left ≫ forward R Q i) ≫ pullback.snd _ _ = _
    rw [Category.assoc, forward, pullback.lift_snd, ← Category.assoc, Category.id_comp]
    change (backward R Q i ≫ pullback.snd _ _).left ≫ _ = _
    rw [backward, pullback.lift_snd, children, SliceFinitePowers.lift_value]

def relativeIso : R.ruleObject Q i ≅ parameterObject R Q i where
  hom := forwardOver R Q i
  inv := backward R Q i
  hom_inv_id := forward_backward R Q i
  inv_hom_id := backward_forward R Q i

def iso : (R.ruleObject Q i).left ≅ (rules R).ruleObject (Q₀) i :=
  (Over.forget P).mapIso (relativeIso R Q i)

theorem iso_fst : (iso R Q i).hom ≫ pullback.fst _ _ =
    (pullback.fst (R.premises i) (finitePowerMap Q.hom i.val)).left :=
  pullback.lift_fst _ _ _

theorem iso_snd : (iso R Q i).hom ≫ pullback.snd _ _ =
    (pullback.snd (R.premises i) (finitePowerMap Q.hom i.val)).left ≫
      SliceFinitePowers.comparison Q.left i.val := pullback.lift_snd _ _ _

theorem iso_conclusion : (iso R Q i).hom ≫ (rules R).ruleConclusion (Q₀) i =
    (R.ruleConclusion Q i).left := by
  change (iso R Q i).hom ≫ (pullback.fst _ _ ≫ (R.conclusion i).left) = _
  rw [← Category.assoc, iso_fst]
  rfl

theorem inverse_conclusion : (iso R Q i).inv ≫ (R.ruleConclusion Q i).left =
    (rules R).ruleConclusion (Q₀) i := by
  rw [← iso_conclusion R Q i, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

omit Q in
theorem naturality {Q Q' : Over F} (q : Q ⟶ Q') (i : Fin (N + 1)) :
    (R.ruleMap q i).left ≫ (iso R Q' i).hom =
      (iso R Q i).hom ≫ (rules R).ruleMap ((Over.iteratedSliceEquiv F).functor.map q) i := by
  apply pullback.hom_ext
  · simp only [Category.assoc, iso_fst, RulePresentation.ruleMap_fst]
    exact congrArg Over.Hom.left (R.ruleMap_fst q i)
  · simp only [Category.assoc, iso_snd, RulePresentation.ruleMap_snd]
    have h := congrArg Over.Hom.left (R.ruleMap_snd q i)
    simp only [Over.comp_left] at h
    rw [← Category.assoc, h, Category.assoc, SliceFinitePowers.naturality]
    simp only [← Category.assoc, iso_snd]
    rfl

end CategoricalEssentialIncompleteness.V46.SliceRuleObjects
