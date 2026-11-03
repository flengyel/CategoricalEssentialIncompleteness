/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46PredicateInterpretation
import Mathlib.CategoryTheory.Whiskering

/-! # The comparison with the canonical domain-split model interpretation -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.RestrictionCategory
open FailureOfComposition FailureOfComposition.ProofSearch
open FailureOfComposition.TypedProgramCategory FailureOfComposition.TypedNearProduct
open CategoricalEssentialIncompleteness.LocalConnectedness
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates

namespace CategoricalEssentialIncompleteness.V46.PredicateInterpretation

variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
variable (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T]

/-- The fixed points of the interpreted restriction idempotent. -/
abbrev Domain (X : TotalSplit T) : Type :=
  {x : M // SyntacticModel.programRelation T M X.obj.domain.hom.val x x}

theorem domain_graph (X : TotalSplit T) (x y : M) :
    SyntacticModel.programRelation T M X.obj.domain.hom.val x y ↔
      SyntacticModel.programRelation T M X.obj.domain.hom.val x x ∧ y = x := by
  have he := congrArg (fun k : X.obj.base ⟶ X.obj.base => k.val) X.obj.domain.restriction
  rw [restriction_val] at he
  have h := domainClass_model T X.obj.domain.hom.val M x y
  rw [he] at h
  constructor
  · intro hxy
    have hy := (h.mp hxy).1
    exact ⟨by simpa only [hy] using hxy, hy⟩
  · rintro ⟨hx, rfl⟩
    exact hx

/-- This is exactly the domain chosen to split the partial identity
`F_M(e)`, expressed in the already-existing partial-function interpretation. -/
abbrev CanonicalDomain (X : TotalSplit T) : Type :=
  {x : SyntacticModel.carrier M (objectCode X.obj.base) //
    x ∈ SyntacticModel.arrow T M X.obj.domain.hom x}

def canonicalDomainEquiv (X : TotalSplit T) : Domain T M X ≃ CanonicalDomain T M X where
  toFun x :=
    ⟨⟨x.val, SyntacticModel.arrow_source T M X.obj.domain.hom x.property⟩,
      (SyntacticModel.mem_arrow T M X.obj.domain.hom _ _).mpr x.property⟩
  invFun x := ⟨x.val.val, (SyntacticModel.mem_arrow T M X.obj.domain.hom _ _).mp x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem total_domain_class {X Y : TotalSplit T} (f : X ⟶ Y) :
    domainClass T f.hom.hom.val = X.obj.domain.hom.val := by
  have h := congrArg (fun k : X.obj ⟶ X.obj => k.hom.val) f.property
  change (rst f.hom.hom).val = X.obj.domain.hom.val at h
  rwa [restriction_val] at h

theorem total_domain_exists {X Y : TotalSplit T} (f : X ⟶ Y) (x : Domain T M X) :
    ∃! y : M, SyntacticModel.programRelation T M f.hom.hom.val x.val y := by
  have hx : SyntacticModel.programRelation T M (domainClass T f.hom.hom.val)
      x.val x.val := by
    rw [total_domain_class T f]
    exact x.property
  obtain ⟨_, y, hy⟩ := (domainClass_model T f.hom.hom.val M x.val x.val).mp hx
  exact ⟨y, hy, fun z hz =>
    SyntacticModel.programRelation_functional T M _ _ _ _ hz hy⟩

theorem total_target_fixed {X Y : TotalSplit T} (f : X ⟶ Y) (x y : M)
    (hxy : SyntacticModel.programRelation T M f.hom.hom.val x y) :
    SyntacticModel.programRelation T M Y.obj.domain.hom.val y y := by
  have ht := congrArg (fun k : X.obj.base ⟶ Y.obj.base => k.val) f.hom.target
  change Y.obj.domain.hom.val * f.hom.hom.val = f.hom.hom.val at ht
  have h : SyntacticModel.programRelation T M
      (Y.obj.domain.hom.val * f.hom.hom.val) x y := by
    rw [ht]
    exact hxy
  obtain ⟨z, _, hz⟩ := (SyntacticModel.programRelation_mul T M _ _ x y).mp h
  obtain ⟨hf, he⟩ := (domain_graph T M Y z y).mp hz
  simpa only [he] using hf

/-- The total arrow obtained by restricting the original interpreted
partial graph to the two chosen splitting domains. -/
def domainValue {X Y : TotalSplit T} (f : X ⟶ Y) (x : Domain T M X) : Domain T M Y :=
  ⟨Classical.choose (total_domain_exists T M f x),
    total_target_fixed T M f x.val _ (Classical.choose_spec (total_domain_exists T M f x)).1⟩

theorem domainValue_graph {X Y : TotalSplit T} (f : X ⟶ Y) (x : Domain T M X) :
    SyntacticModel.programRelation T M f.hom.hom.val x.val (domainValue T M f x).val :=
  (Classical.choose_spec (total_domain_exists T M f x)).1

theorem domainValue_eq_iff {X Y : TotalSplit T} (f : X ⟶ Y)
    (x : Domain T M X) (y : Domain T M Y) :
    domainValue T M f x = y ↔ SyntacticModel.programRelation T M f.hom.hom.val x.val y.val := by
  constructor
  · rintro rfl
    exact domainValue_graph T M f x
  · intro hy
    apply Subtype.ext
    exact SyntacticModel.programRelation_functional T M _ _ _ _ (domainValue_graph T M f x) hy

/-- The canonical total functor of the domain-split original model
interpretation, on every object and morphism of the total splitting. -/
def domainFunctor : TotalSplit T ⥤ Type where
  obj X := Domain T M X
  map f := ↾(domainValue T M f)
  map_id X := by
    apply ConcreteCategory.hom_ext
    intro x
    apply (domainValue_eq_iff T M (𝟙 X) x x).mpr
    exact x.property
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro x
    apply (domainValue_eq_iff T M (f ≫ g) x _).mpr
    change SyntacticModel.programRelation T M (g.hom.hom.val * f.hom.hom.val) _ _
    exact (SyntacticModel.programRelation_mul T M _ _ _ _).mpr
      ⟨(domainValue T M f x).val, domainValue_graph T M f x,
        domainValue_graph T M g (domainValue T M f x)⟩

@[simp] theorem domainFunctor_graph {X Y : TotalSplit T} (f : X ⟶ Y)
    (x : Domain T M X) (y : Domain T M Y) :
    (domainFunctor T M).map f x = y ↔
      SyntacticModel.programRelation T M f.hom.hom.val x.val y.val :=
  domainValue_eq_iff T M f x y

/-- Predicate fixed points are exactly the interpreted carrier formula. -/
def realizedDomainEquiv (C : PredicateCategory T) :
    Domain T M (interpretedObject T C) ≃ Obj M C where
  toFun x := ⟨x.val, ((predicateClass_model T C M x.val x.val).mp x.property).1⟩
  invFun x := ⟨x.val, (predicateClass_model T C M x.val x.val).mpr ⟨x.property, rfl⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

def realizedDomainComparison : realization T ⋙ domainFunctor T M ≅ functor T M :=
  NatIso.ofComponents (fun C => (realizedDomainEquiv T M C).toIso) (by
    intro C D f
    induction f using Quotient.inductionOn with
    | _ f =>
      apply ConcreteCategory.hom_ext
      intro x
      symm
      apply (value_eq_iff T M f _ _).mpr
      exact (f.programClass_model M _ _).mp (domainValue_graph T M f.toTotal x))

/-- The equivalence-defined total model functor is naturally isomorphic
to the canonical domain-split interpretation of the existing partial functor. -/
def totalDomainComparison : totalFunctor T M ≅ domainFunctor T M := by
  let E := predicateEquivalence T
  have ε : E.inverse ⋙ realization T ≅ 𝟭 (TotalSplit T) := by
    simpa only [E, predicateEquivalence, Functor.asEquivalence_functor] using E.counitIso
  exact Functor.isoWhiskerLeft E.inverse (realizedDomainComparison T M).symm ≪≫
    (Functor.associator E.inverse (realization T) (domainFunctor T M)).symm ≪≫
    Functor.isoWhiskerRight ε (domainFunctor T M) ≪≫ Functor.leftUnitor (domainFunctor T M)

/-- The same functor on the literal domains used to split `F_M(e)`. -/
def canonicalDomainFunctor : TotalSplit T ⥤ Type where
  obj X := CanonicalDomain T M X
  map {X Y} f := (canonicalDomainEquiv T M X).symm.toIso.hom ≫
    (domainFunctor T M).map f ≫ (canonicalDomainEquiv T M Y).toIso.hom
  map_id X := by
    apply ConcreteCategory.hom_ext
    intro x
    change canonicalDomainEquiv T M X
      (domainValue T M (𝟙 X) ((canonicalDomainEquiv T M X).symm x)) = x
    have hi : domainValue T M (𝟙 X) ((canonicalDomainEquiv T M X).symm x) =
        (canonicalDomainEquiv T M X).symm x := by
      apply (domainValue_eq_iff T M _ _ _).mpr
      exact ((canonicalDomainEquiv T M X).symm x).property
    rw [hi]
    exact (canonicalDomainEquiv T M X).apply_symm_apply x
  map_comp {X Y Z} f g := by
    apply ConcreteCategory.hom_ext
    intro x
    change canonicalDomainEquiv T M Z
      (domainValue T M (f ≫ g) ((canonicalDomainEquiv T M X).symm x)) =
      canonicalDomainEquiv T M Z (domainValue T M g
        ((canonicalDomainEquiv T M Y).symm
          (canonicalDomainEquiv T M Y
            (domainValue T M f ((canonicalDomainEquiv T M X).symm x)))))
    rw [(canonicalDomainEquiv T M Y).symm_apply_apply]
    apply congrArg (canonicalDomainEquiv T M Z)
    exact ConcreteCategory.congr_hom ((domainFunctor T M).map_comp f g) _

/-- The objectwise identification with the actual splitting domains is
natural on all total arrows. -/
def domainCanonicalComparison : domainFunctor T M ≅ canonicalDomainFunctor T M :=
  NatIso.ofComponents (fun X => (canonicalDomainEquiv T M X).toIso) (by
    intro X Y f
    apply ConcreteCategory.hom_ext
    intro x
    change canonicalDomainEquiv T M Y (domainValue T M f x) =
      canonicalDomainEquiv T M Y (domainValue T M f
        ((canonicalDomainEquiv T M X).symm (canonicalDomainEquiv T M X x)))
    rw [(canonicalDomainEquiv T M X).symm_apply_apply])

/-- The exact comparison with the canonical chosen domain splitting of
`F_M` used for the manuscript's total interpretation. -/
def totalCanonicalComparison : totalFunctor T M ≅ canonicalDomainFunctor T M :=
  totalDomainComparison T M ≪≫ domainCanonicalComparison T M

@[simp] theorem canonicalDomainFunctor_graph {X Y : TotalSplit T} (f : X ⟶ Y)
    (x : CanonicalDomain T M X) (y : CanonicalDomain T M Y) :
    (canonicalDomainFunctor T M).map f x = y ↔
      SyntacticModel.programRelation T M f.hom.hom.val x.val.val y.val.val := by
  change canonicalDomainEquiv T M Y
    (domainValue T M f ((canonicalDomainEquiv T M X).symm x)) = y ↔ _
  rw [← (canonicalDomainEquiv T M Y).eq_symm_apply]
  exact domainValue_eq_iff T M f _ _

end CategoricalEssentialIncompleteness.V46.PredicateInterpretation
