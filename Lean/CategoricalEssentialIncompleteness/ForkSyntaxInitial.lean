/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.ForkSyntaxEvaluation
public import CategoricalEssentialIncompleteness.ForkNumericalInitial
public import CategoricalEssentialIncompleteness.EffectiveForkCoproducts
public import CategoricalEssentialIncompleteness.RestrictionRanges

/-! # Initiality of the actual finite syntax algebra -/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open CategoryTheory CategoryTheory.RestrictionCategory
open CategoryTheory.PCategoryStruct CategoryTheory.CoprodStruct CategoryTheory.HasCoproducts

namespace CategoricalEssentialIncompleteness.LocalConnectedness.ForkSyntax

open EffectiveFork (Object V)

namespace Algebra

variable {Z : Object}

theorem atom_fold (A : Algebra Z) : theta ≫ A.fold=A.atom :=
  EffectiveFork.Hom.ext A.center.atom_fold A.left.atom_fold A.right.atom_fold

theorem neg_fold (A : Algebra Z) : nu ≫ A.fold=A.fold ≫ A.neg :=
  EffectiveFork.Hom.ext A.center.neg_fold A.left.neg_fold A.right.neg_fold

theorem imp_fold (A : Algebra Z) : implication ≫ A.fold=
    EffectiveFork.productMap A.fold A.fold ≫ A.imp :=
  EffectiveFork.Hom.ext A.center.imp_fold A.left.imp_fold A.right.imp_fold

theorem fold_unique (A : Algebra Z) (u : S ⟶ Z)
    (ha : theta ≫ u=A.atom) (hn : nu ≫ u=u ≫ A.neg)
    (hi : implication ≫ u=EffectiveFork.productMap u u ≫ A.imp) : u=A.fold :=
  EffectiveFork.Hom.ext
    (A.center.fold_unique u.center (congrArg EffectiveFork.Hom.center ha)
      (congrArg EffectiveFork.Hom.center hn) (congrArg EffectiveFork.Hom.center hi))
    (A.left.fold_unique u.left (congrArg EffectiveFork.Hom.left ha)
      (congrArg EffectiveFork.Hom.left hn) (congrArg EffectiveFork.Hom.left hi))
    (A.right.fold_unique u.right (congrArg EffectiveFork.Hom.right ha)
      (congrArg EffectiveFork.Hom.right hn) (congrArg EffectiveFork.Hom.right hi))

end Algebra

/-- The manuscript's polynomial functor, with the displayed three summands. -/
def polynomial : Object ⥤ Object where
  obj Z := coprod (coprod V Z) (nearProd Z Z)
  map f := coprod_map (coprod_map (𝟙 V) f) (nearProd_map f f)
  map_id Z := by rw [coprod_id,PCategory.nearProd_id,coprod_id]
  map_comp f g := by
    rw [coprod_comp,coprod_comp,PCategory.nearProd_comp,Category.id_comp]

def atomInj (Z : Object) : V ⟶ polynomial.obj Z :=
  i0 V Z ≫ i0 (coprod V Z) (nearProd Z Z)
def negInj (Z : Object) : Z ⟶ polynomial.obj Z :=
  i1 V Z ≫ i0 (coprod V Z) (nearProd Z Z)
def impInj (Z : Object) : nearProd Z Z ⟶ polynomial.obj Z :=
  i1 (coprod V Z) (nearProd Z Z)

theorem atomInj_map {X Y : Object} (f : X ⟶ Y) :
    atomInj X ≫ polynomial.map f=atomInj Y := by
  unfold atomInj
  change (i0 V X ≫ i0 _ _) ≫ coprod_map (coprod_map (𝟙 V) f) _=_
  rw [Category.assoc,i0_coprod_map,← Category.assoc,i0_coprod_map,Category.id_comp]

theorem negInj_map {X Y : Object} (f : X ⟶ Y) :
    negInj X ≫ polynomial.map f=f ≫ negInj Y := by
  unfold negInj
  change (i1 V X ≫ i0 _ _) ≫ coprod_map (coprod_map (𝟙 V) f) _=_
  rw [Category.assoc,i0_coprod_map,← Category.assoc,i1_coprod_map,Category.assoc]

theorem impInj_map {X Y : Object} (f : X ⟶ Y) :
    impInj X ≫ polynomial.map f=nearProd_map f f ≫ impInj Y :=
  i1_coprod_map _ _

def iota : polynomial.obj S ⟶ S := copair (copair theta nu) implication

theorem atomInj_iota : atomInj S ≫ iota=theta := by
  unfold atomInj iota
  rw [Category.assoc,i0_copair,i0_copair]
theorem negInj_iota : negInj S ≫ iota=nu := by
  unfold negInj iota
  rw [Category.assoc,i0_copair,i1_copair]
theorem impInj_iota : impInj S ≫ iota=implication := i1_copair _ _

def constructors {Z : Object} (alpha : polynomial.obj Z ⟶ Z) (ht : isTotal alpha) :
    Algebra Z where
  atom := atomInj Z ≫ alpha
  neg := negInj Z ≫ alpha
  imp := impInj Z ≫ alpha
  atom_total := isTotal_comp (isTotal_comp (RestrictionCoproducts.total_i0 _ _)
    (RestrictionCoproducts.total_i0 _ _)) ht
  neg_total := isTotal_comp (isTotal_comp (RestrictionCoproducts.total_i1 _ _)
    (RestrictionCoproducts.total_i0 _ _)) ht
  imp_total := isTotal_comp (RestrictionCoproducts.total_i1 _ _) ht

theorem polynomial_hom_ext {X Y : Object} {f g : polynomial.obj X ⟶ Y}
    (ha : atomInj X ≫ f=atomInj X ≫ g)
    (hn : negInj X ≫ f=negInj X ≫ g)
    (hi : impInj X ≫ f=impInj X ≫ g) : f=g := by
  apply CategoryTheory.HasCoproducts.hom_ext
  · apply CategoryTheory.HasCoproducts.hom_ext
    · simpa only [atomInj,Category.assoc] using ha
    · simpa only [negInj,Category.assoc] using hn
  · exact hi

theorem fold_algebra {Z : Object} (alpha : polynomial.obj Z ⟶ Z) (ht : isTotal alpha) :
    iota ≫ (constructors alpha ht).fold=
      polynomial.map (constructors alpha ht).fold ≫ alpha := by
  apply polynomial_hom_ext
  · rw [← Category.assoc,atomInj_iota,← Category.assoc,atomInj_map]
    exact (constructors alpha ht).atom_fold
  · rw [← Category.assoc,negInj_iota,← Category.assoc,negInj_map,Category.assoc]
    exact (constructors alpha ht).neg_fold
  · rw [← Category.assoc,impInj_iota,← Category.assoc,impInj_map,Category.assoc]
    exact (constructors alpha ht).imp_fold

/-- Proposition B.1: existence and uniqueness of the total algebra morphism.
No extension of the target operations to ambient total recursive functions is
assumed; their actual partial computations were used to construct the fold. -/
theorem syntax_initial {Z : Object} (alpha : polynomial.obj Z ⟶ Z) (ht : isTotal alpha) :
    ∃! u : S ⟶ Z,isTotal u ∧ iota ≫ u=polynomial.map u ≫ alpha := by
  refine ⟨(constructors alpha ht).fold,⟨(constructors alpha ht).fold_total,
    fold_algebra alpha ht⟩,?_⟩
  rintro u ⟨_,hu⟩
  apply (constructors alpha ht).fold_unique u
  · have h := congrArg (fun k => atomInj S ≫ k) hu
    rwa [← Category.assoc,atomInj_iota,← Category.assoc,atomInj_map] at h
  · have h := congrArg (fun k => negInj S ≫ k) hu
    simpa only [← Category.assoc,negInj_iota,negInj_map,constructors] using h
  · have h := congrArg (fun k => impInj S ≫ k) hu
    change implication ≫ u=nearProd_map u u ≫ (impInj Z ≫ alpha)
    simpa only [← Category.assoc,impInj_iota,impInj_map] using h

end CategoricalEssentialIncompleteness.LocalConnectedness.ForkSyntax
