/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.ForkCosheafCriterion
public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers

/-! # The actual coproduct/coequalizer form of every cover axiom -/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open CategoryTheory CategoryTheory.Limits

namespace CategoricalEssentialIncompleteness.LocalConnectedness.ForkTopology

variable (F : Open ⥤ Type) {U : Open} {ι : Type} (C : Cover U ι)

def CoverSum := Σ i : ι,F.obj (C.member i)
def OverlapSum := Σ p : ι × ι,F.obj (C.member p.1 ⊓ C.member p.2)

def coverFirst : OverlapSum F C ⟶ CoverSum F C :=
  ↾fun z => ⟨z.1.1,F.map (homOfLE inf_le_left) z.2⟩
def coverSecond : OverlapSum F C ⟶ CoverSum F C :=
  ↾fun z => ⟨z.1.2,F.map (homOfLE inf_le_right) z.2⟩
def coverToWhole : CoverSum F C ⟶ F.obj U :=
  ↾fun z => F.map (homOfLE (C.le z.1)) z.2

theorem cover_condition : coverFirst F C ≫ coverToWhole F C=coverSecond F C ≫ coverToWhole F C := by
  apply ConcreteCategory.hom_ext
  rintro ⟨⟨i,j⟩,x⟩
  have he : F.map (homOfLE (inf_le_left : C.member i ⊓ C.member j ≤ C.member i)) ≫
      F.map (homOfLE (C.le i))=
      F.map (homOfLE (inf_le_right : C.member i ⊓ C.member j ≤ C.member j)) ≫
      F.map (homOfLE (C.le j)) := by simp
  exact ConcreteCategory.congr_hom he x

def coverCofork : Cofork (coverFirst F C) (coverSecond F C) :=
  Cofork.ofπ (coverToWhole F C) (cover_condition F C)

def sumMap {B : Type} (f : ∀ i,F.obj (C.member i) ⟶ B) : CoverSum F C ⟶ B :=
  ↾fun z => f z.1 z.2

def fromSumMap {B : Type} (k : CoverSum F C ⟶ B) (i : ι) : F.obj (C.member i) ⟶ B :=
  ↾fun x => k ⟨i,x⟩

@[simp] theorem sumMap_fromSumMap {B : Type} (k : CoverSum F C ⟶ B) :
    sumMap F C (fromSumMap F C k)=k := by
  apply ConcreteCategory.hom_ext
  rintro ⟨i,x⟩
  rfl

theorem compatible_iff_equalizes {B : Type} (f : ∀ i,F.obj (C.member i) ⟶ B) :
    Compatible F C f ↔ coverFirst F C ≫ sumMap F C f=coverSecond F C ≫ sumMap F C f := by
  constructor
  · intro h
    apply ConcreteCategory.hom_ext
    rintro ⟨⟨i,j⟩,x⟩
    exact ConcreteCategory.congr_hom (h i j) x
  · intro h i j
    apply ConcreteCategory.hom_ext
    intro x
    exact ConcreteCategory.congr_hom h ⟨(i,j),x⟩

def coverCofork_isColimit (hg : ∀ (B : Type) (f : ∀ i,F.obj (C.member i) ⟶ B),
    Compatible F C f → ∃! h : F.obj U ⟶ B,∀ i,F.map (homOfLE (C.le i)) ≫ h=f i) :
    IsColimit (coverCofork F C) := by
  apply Cofork.IsColimit.ofExistsUnique
  intro s
  let f := fromSumMap F C s.π
  have hf : Compatible F C f := by
    apply (compatible_iff_equalizes F C f).mpr
    simpa only [f,sumMap_fromSumMap] using s.condition
  obtain ⟨d,hd,hu⟩ := hg s.pt f hf
  refine ⟨d,?_,?_⟩
  · apply ConcreteCategory.hom_ext
    rintro ⟨i,x⟩
    exact ConcreteCategory.congr_hom (hd i) x
  · intro m hm
    apply hu m
    intro i
    apply ConcreteCategory.hom_ext
    intro x
    exact ConcreteCategory.congr_hom hm ⟨i,x⟩

theorem gluing_of_coverCofork (hc : IsColimit (coverCofork F C))
    (B : Type) (f : ∀ i,F.obj (C.member i) ⟶ B) (hf : Compatible F C f) :
    ∃! h : F.obj U ⟶ B,∀ i,F.map (homOfLE (C.le i)) ≫ h=f i := by
  let s := Cofork.ofπ (sumMap F C f) ((compatible_iff_equalizes F C f).mp hf)
  let d := hc.desc s
  have hd : coverToWhole F C ≫ d=sumMap F C f := Cofork.IsColimit.π_desc hc
  refine ⟨d,?_,?_⟩
  · intro i
    apply ConcreteCategory.hom_ext
    intro x
    exact ConcreteCategory.congr_hom hd ⟨i,x⟩
  · intro m hm
    apply Cofork.IsColimit.hom_ext hc
    apply ConcreteCategory.hom_ext
    rintro ⟨i,x⟩
    exact (ConcreteCategory.congr_hom (hm i) x).trans
      (ConcreteCategory.congr_hom hd ⟨i,x⟩).symm

/-- Exact equivalence with the displayed arbitrary-cover coequalizer axiom. -/
theorem cosheaf_iff_coverCoequalizers :
    IsCosheaf F ↔ ∀ (U : Open) (ι : Type) (C : Cover U ι),Nonempty (IsColimit (coverCofork F C)) := by
  constructor
  · intro h U ι C
    exact ⟨coverCofork_isColimit F C (h U ι C)⟩
  · intro h U ι C B f hf
    exact gluing_of_coverCofork F C (Classical.choice (h U ι C)) B f hf

end CategoricalEssentialIncompleteness.LocalConnectedness.ForkTopology
