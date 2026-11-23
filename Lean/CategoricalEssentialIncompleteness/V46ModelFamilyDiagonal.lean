/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.SyntacticFamily
public import CategoricalEssentialIncompleteness.V46RestrictionProductCategory

/-! # The model family's image of the Turing morphism (Appendix D)

In one model coordinate take the partial function that returns the model's
zero precisely where the evaluator is undefined on the diagonal. A parameter
for this function would contradict its domain at the parameter itself.
-/

@[expose] public section
noncomputable section
universe u w
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.RestrictionCategory
open CategoricalEssentialIncompleteness.LocalConnectedness
open PartialFunctions PartialFunctionFamilies

namespace CategoricalEssentialIncompleteness.V46.ModelFamilyDiagonal

/-- Restriction products of sets and partial functions. -/
def partialFunctionProducts : RestrictionProducts.ProductData Pfn.{u} where
  prod X Y := PartialFun.of (X × Y)
  fst _ _ := PFun.lift Prod.fst
  snd _ _ := PFun.lift Prod.snd
  pair := PFun.prodLift
  fst_total _ _ := PFun.ext fun _ _ => by simp [PFun.lift]
  snd_total _ _ := PFun.ext fun _ _ => by simp [PFun.lift]
  pair_fst f g := by
    apply PFun.ext
    intro x y
    constructor
    · intro hy
      obtain ⟨⟨a,b⟩, hab, hy⟩ := Part.mem_bind_iff.mp hy
      obtain ⟨ha, hb⟩ := PFun.mem_prodLift.mp hab
      have he : y = a := Part.mem_some_iff.mp hy
      exact Part.mem_bind_iff.mpr ⟨x, (mem_restriction g x x).mpr ⟨⟨b, hb⟩, rfl⟩, he ▸ ha⟩
    · intro hy
      obtain ⟨z, hz, hf⟩ := Part.mem_bind_iff.mp hy
      obtain ⟨⟨b, hb⟩, rfl⟩ := (mem_restriction g x z).mp hz
      exact Part.mem_bind_iff.mpr ⟨(y,b), PFun.mem_prodLift.mpr ⟨hf,hb⟩, Part.mem_some _⟩
  pair_snd f g := by
    apply PFun.ext
    intro x y
    constructor
    · intro hy
      obtain ⟨⟨a,b⟩, hab, hy⟩ := Part.mem_bind_iff.mp hy
      obtain ⟨ha, hb⟩ := PFun.mem_prodLift.mp hab
      have he : y = b := Part.mem_some_iff.mp hy
      exact Part.mem_bind_iff.mpr ⟨x, (mem_restriction f x x).mpr ⟨⟨a, ha⟩, rfl⟩, he ▸ hb⟩
    · intro hy
      obtain ⟨z, hz, hg⟩ := Part.mem_bind_iff.mp hy
      obtain ⟨⟨a, ha⟩, rfl⟩ := (mem_restriction f x z).mp hz
      exact Part.mem_bind_iff.mpr ⟨(a,y), PFun.mem_prodLift.mpr ⟨ha,hg⟩, Part.mem_some _⟩
  pair_restriction f g := by
    apply PFun.ext
    intro x y
    change y ∈ restriction (PFun.prodLift f g) x ↔ y ∈ (restriction f ≫ restriction g) x
    simp only [mem_restriction, mem_comp, Prod.exists, PFun.mem_prodLift]
    aesop
  pair_proj h := by
    apply PFun.ext
    intro x y
    simp only [PFun.mem_prodLift, mem_comp, PFun.lift, Part.mem_some_iff]
    constructor
    · rintro ⟨⟨a, ha, h₁⟩, b, hb, h₂⟩
      have hab := Part.mem_unique ha hb
      subst b
      exact Prod.ext h₁ h₂ ▸ ha
    · intro hy
      exact ⟨⟨y, hy, rfl⟩, y, hy, rfl⟩

/-- Binary restriction products in the category of families are computed coordinatewise. -/
def familyProducts (I : Type w) : RestrictionProducts.ProductData (Family.{u} I) where
  prod X Y j := PartialFun.of (X j × Y j)
  fst _ _ _ := PFun.lift Prod.fst
  snd _ _ _ := PFun.lift Prod.snd
  pair f g j := (f j).prodLift (g j)
  fst_total X Y := funext fun j => partialFunctionProducts.fst_total (X j) (Y j)
  snd_total X Y := funext fun j => partialFunctionProducts.snd_total (X j) (Y j)
  pair_fst f g := funext fun j => partialFunctionProducts.pair_fst (f j) (g j)
  pair_snd f g := funext fun j => partialFunctionProducts.pair_snd (f j) (g j)
  pair_restriction f g := funext fun j => partialFunctionProducts.pair_restriction (f j) (g j)
  pair_proj h := funext fun j => partialFunctionProducts.pair_proj (h j)

scoped instance familyProductStruct {I : Type w} : PCategoryStruct (Family.{u} I) :=
  (familyProducts I).pcategoryStruct

scoped instance familyProductLaws {I : Type w} : PCategory (Family.{u} I) :=
  (familyProducts I).pcategoryLaws

theorem productMap_apply {I : Type w} {W X Y Z : Family.{u} I} (f : W ⟶ X) (g : Y ⟶ Z) (j : I) :
    PCategoryStruct.nearProd_map f g j = PFun.prodMap (f j) (g j) :=
  PFun.prodLift_fst_comp_snd_comp _ _

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open FailureOfComposition.TypedProgramCategory FailureOfComposition.TypedTuringMorphism
open SyntacticModel PCategoryStruct

/-- The interpreted product morphism is the coordinatewise product of the
interpreted morphisms. The model functor already acts on recursively interpreted types. -/
theorem map_product (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] {Q R B C : CodedProgramCategory T}
    (f : Q ⟶ R) (g : B ⟶ C) :
    (familyFunctor T).map (nearProd_map f g) =
      nearProd_map ((familyFunctor T).map f) ((familyFunctor T).map g) := by
  rw [family_map_product]
  exact funext fun j => (productMap_apply _ _ j).symm

/-- The image of the source Turing morphism fails the Turing property in the
product of the partial-function categories of all countable model coordinates. -/
theorem image_not_turing (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] (hT : Consistent T) :
    ¬ RecursionCategory.IsTuringMorphism (W := (familyFunctor T).obj (omegaObject T))
      (X := (familyFunctor T).obj (omegaObject T)) (Y := (familyFunctor T).obj (omegaObject T))
      ((familyFunctor T).map (typedTau T)) := by
  classical
  obtain ⟨M⟩ := modelIndex_nonempty T hT
  let W := (familyFunctor T).obj (omegaObject T)
  let S : Family (ModelIndex T) := fun _ => PartialFun.of PUnit
  let τ := (familyFunctor T).map (typedTau T)
  let t : ℕ × ℕ → Part ℕ := τ M
  let h : nearProd S W ⟶ W := fun j z =>
    if j = M then Part.assert (¬ (t (z.2, z.2)).Dom) fun _ => Part.some M.val.zero else Part.none
  intro ht
  obtain ⟨g, hg, hfactor⟩ := ht S h
  change PCategoryStruct.rst g = 𝟙 S at hg
  rw [(familyProducts (ModelIndex T)).restriction_eq] at hg
  have hpoint : PUnit.unit ∈ restriction (g M) PUnit.unit := by
    have he := congrArg (fun f : S ⟶ S => f M PUnit.unit) hg
    change restriction (g M) PUnit.unit = Part.some PUnit.unit at he
    rw [he]
    exact Part.mem_some _
  obtain ⟨⟨m, hm⟩, _⟩ := (mem_restriction _ _ _).mp hpoint
  have hp : PFun.prodMap (g M) ((𝟙 W) M) (PUnit.unit, m) = Part.some (m, m) :=
    Part.eq_some_iff.mpr (PFun.mem_prodMap.mpr ⟨hm, Part.mem_some _⟩)
  have hf := congrArg (fun f : nearProd S W ⟶ W => f M (PUnit.unit, m)) hfactor
  change ((nearProd_map g (𝟙 W) M) (PUnit.unit, m)).bind t = h M (PUnit.unit, m) at hf
  rw [productMap_apply, hp, Part.bind_some] at hf
  have hd := congrArg Part.Dom hf
  have hd' : (t (m,m)).Dom ↔ ¬ (t (m,m)).Dom := by
    apply (Iff.of_eq hd).trans
    simp [h, Part.assert, Part.some]
  by_cases hm' : (t (m,m)).Dom
  · exact (hd'.mp hm') hm'
  · exact hm' (hd'.mpr hm')

end CategoricalEssentialIncompleteness.V46.ModelFamilyDiagonal
