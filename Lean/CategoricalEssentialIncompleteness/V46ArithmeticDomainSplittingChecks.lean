/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ArithmeticDomainSplitting

/-! # Generic fixed-point splitting and extension statement checks -/

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
open CategoricalEssentialIncompleteness.V46.ArithmeticDomainExtension

variable {C : Type u} [Category.{v} C] [RestrictionCategory C] [Ranges C]
  [HasZeroMorphisms C] [CoprodStruct C] [CategoryTheory.HasCoproducts C]
  [RestrictionCoproducts C]
variable (F : RangeFunctor C Pfn.{w})

example (X : SplitObject C) :
    inclusion F X ≫ retraction F X = 𝟙 (PartialFun.of (Domain F X)) :=
  (splitting F X).section_eq

example (X : SplitObject C) :
    retraction F X ≫ inclusion F X = F.toFunctor.map X.domain.hom :=
  (splitting F X).support_eq

example {X Y : SplitObject C} (f : X ⟶ Y)
    (x : {a : F.toFunctor.obj X.base // a ∈ F.toFunctor.map X.domain.hom a})
    (y : {b : F.toFunctor.obj Y.base // b ∈ F.toFunctor.map Y.domain.hom b}) :
    y ∈ (extension F).toFunctor.map f x ↔ y.val ∈ F.toFunctor.map f.hom x.val :=
  mem_extension F f x y

example {X Y : SplitObject C} (f : X ⟶ Y) :
    (extension F).toFunctor.map (Ranges.range f).hom =
      (Ranges.range ((extension F).toFunctor.map f)).hom :=
  (extension F).map_range f

example {X Y : SplitObject C} (f : X ⟶ Y) :
    (extension F).toFunctor.map (rst f) = rst ((extension F).toFunctor.map f) :=
  (extension F).map_restrict f
