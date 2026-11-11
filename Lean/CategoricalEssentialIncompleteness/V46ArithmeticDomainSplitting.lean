/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SplitExtension
public import CategoricalEssentialIncompleteness.PartialFunctions

/-! # The chosen fixed-point splitting of an arbitrary Pfn-valued range functor

Each interpreted restriction idempotent is split through its actual fixed
points. The existing chosen-splitting extension supplies preservation of
restrictions, ranges, zeros and binary coproducts.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory CategoryTheory.RestrictionCategory
open CategoryTheory.Limits (HasZeroMorphisms)
open CategoryTheory.CoprodStruct CategoryTheory.HasCoproducts
open CategoricalEssentialIncompleteness.LocalConnectedness
open CategoricalEssentialIncompleteness.LocalConnectedness.PartialFunctions

namespace CategoricalEssentialIncompleteness.V46.ArithmeticDomainExtension

section Domains
variable {C : Type u} [Category.{v} C] [RestrictionCategory C] [Ranges C]
  [HasZeroMorphisms C] [CoprodStruct C] [CategoryTheory.HasCoproducts C]
variable (F : RangeFunctor C Pfn.{w})

def Domain (X : SplitObject C) : Type w :=
  {x : F.toFunctor.obj X.base // x ∈ F.toFunctor.map X.domain.hom x}

def inclusion (X : SplitObject C) : PartialFun.of (Domain F X) ⟶ F.toFunctor.obj X.base :=
  fun x => Part.some x.val

def retraction (X : SplitObject C) : F.toFunctor.obj X.base ⟶ PartialFun.of (Domain F X) :=
  fun x => ⟨x ∈ F.toFunctor.map X.domain.hom x,fun h => ⟨x,h⟩⟩

theorem mem_retraction (X : SplitObject C) (x : F.toFunctor.obj X.base) (y : Domain F X) :
    y ∈ retraction F X x ↔ y.val = x := by
  change (∃ h, (⟨x,h⟩ : Domain F X) = y) ↔ y.val = x
  constructor
  · rintro ⟨h,he⟩
    exact (congrArg Subtype.val he).symm
  · intro he
    refine ⟨he ▸ y.property,Subtype.ext he.symm⟩

def splitting (X : SplitObject C) : LocalConnectedness.V46.TargetSplitting F X where
  carrier := PartialFun.of (Domain F X)
  inclusion := inclusion F X
  retraction := retraction F X
  total := by
    apply PFun.ext
    intro x y
    simp [inclusion]
  section_eq := by
    apply PFun.ext
    intro x y
    simp only [mem_comp,inclusion,Part.mem_some_iff,exists_eq_left,mem_retraction F X,mem_id]
    exact Subtype.coe_inj
  support_eq := by
    apply PFun.ext
    intro x y
    simp only [mem_comp,inclusion,Part.mem_some_iff,mem_retraction F X]
    constructor
    · rintro ⟨z,hz,hy⟩
      have h := z.property
      have hyx := hy.trans hz
      simpa only [hz,hyx] using h
    · intro h
      obtain ⟨hd,hy⟩ := (mem_idem (F.mapIdem X.domain) x y).mp h
      have hx : x ∈ F.toFunctor.map X.domain.hom x :=
        (mem_idem (F.mapIdem X.domain) x x).mpr ⟨hd,rfl⟩
      exact ⟨⟨x,hx⟩,rfl,hy⟩

variable [RestrictionCoproducts C]

def extension : RangeFunctor (SplitObject C) Pfn :=
  LocalConnectedness.V46.chosenSplitRangeFunctor F (splitting F)

theorem mem_extension {X Y : SplitObject C} (f : X ⟶ Y)
    (x : Domain F X) (y : Domain F Y) :
    y ∈ (extension F).toFunctor.map f x ↔
      y.val ∈ F.toFunctor.map f.hom x.val := by
  change y ∈ (inclusion F X ≫ F.toFunctor.map f.hom ≫ retraction F Y) x ↔ _
  simp only [mem_comp,inclusion,Part.mem_some_iff,mem_retraction F Y,exists_eq_left]
  exact ⟨fun ⟨_,hf,he⟩ => he ▸ hf,fun h => ⟨y.val,h,rfl⟩⟩

end Domains

end CategoricalEssentialIncompleteness.V46.ArithmeticDomainExtension
