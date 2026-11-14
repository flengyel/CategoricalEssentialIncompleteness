/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46PartialSliceSpanPullback
public import CategoricalEssentialIncompleteness.V46PartialSliceTheorySubobjects
public import CategoricalEssentialIncompleteness.V46PartialSlicePostcomposeProducts

/-! # Intended-statement checks for manuscript v57 Theorem 5.2 -/

@[expose] public section
noncomputable section

universe v u
open CategoryTheory CategoryTheory.Limits CategoryTheory.RestrictionCategory PCategoryStruct
open CategoricalEssentialIncompleteness.LocalConnectedness
open CategoricalEssentialIncompleteness.V46 RestrictionSubobjects
open PartialSliceChangeBase

variable {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C] [Splits C]
variable [HasPullbacks (Tot C)] (inverses : MonoInverses C) {T U V S : Tot C}
variable (i : T ⟶ U) [Mono i]
attribute [local instance] PartialSliceChangeBase.overMapMonos

example {X Y : PartialMaps.Par (Over T)} (s : PartialMaps.Raw X Y) :
    (postcompose i).map (PartialMaps.ofSpan s) =
      PartialMaps.ofSpan (PartialMaps.rawMap (Over.map i) s) := rfl

example : (postcompose i).Full := postcompose_full i inverses
example : (postcompose i).Faithful := postcompose_faithful i inverses
example : PreservesRestriction (postcompose i) := postcompose_restriction i
example : PreservesRestriction (reindex i inverses) := reindex_restriction i inverses

example {X Y : PartialMaps.Par (Over T)} (f : X ⟶ Y) (hf : isTotal f) :
    isTotal ((postcompose i).map f) :=
  PreservesRestriction.total (postcompose_restriction i) f hf

example : reindex i inverses = spanPullback i := reindex_eq_spanPullback i inverses

example (Y : PartialMaps.Par (Over U)) :
    ((reindex i inverses).obj Y).obj.left = pullback Y.obj.hom i :=
  reindex_object_left i inverses Y

example (Y : PartialMaps.Par (Over U)) :
    ((reindex i inverses).obj Y).obj.hom = pullback.snd Y.obj.hom i :=
  reindex_object_hom i inverses Y

example : postcompose i ⊣ reindex i inverses := leftAdjunction i inverses
example : reindex i inverses ⊣ postcompose i := rightAdjunction i inverses

example (X : PartialMaps.Par (Over T)) (Y : PartialMaps.Par (Over U)) :
    ((postcompose i).obj X ⟶ Y) ≃ (X ⟶ (reindex i inverses).obj Y) :=
  leftHomEquiv i inverses X Y

example (X : PartialMaps.Par (Over T)) (Y : PartialMaps.Par (Over U)) :
    ((reindex i inverses).obj Y ⟶ X) ≃ (Y ⟶ (postcompose i).obj X) :=
  rightHomEquiv i inverses Y X

example (Y : PartialMaps.Par (Over U)) :
    (rightAdjunction i inverses).unit.app Y =
      PartialMaps.inverseMono (pullbackInclusion i inverses Y) :=
  right_unit_span i inverses Y

example (proper : ¬ IsIso i) : ¬ (postcompose i).EssSurj := not_essSurj i inverses proper

example (proper : ¬ IsIso i) :
    ¬ isTotal ((rightAdjunction i inverses).unit.app
      (⟨Over.mk (𝟙 U)⟩ : PartialMaps.Par (Over U))) :=
  right_unit_not_total i inverses proper

example (j : U ⟶ V) : postcompose i ⋙ postcompose j = postcompose (i ≫ j) :=
  postcompose_comp i j

example : postcompose (𝟙 T) = 𝟭 (PartialMaps.Par (Over T)) := postcompose_id T

example (X Y : PartialMaps.Par (Over T)) :
    (postcompose i).obj (PartialSliceProducts.product inverses T X Y) ≅
      PartialSliceProducts.product inverses U ((postcompose i).obj X) ((postcompose i).obj Y) :=
  PartialSlicePostcomposeProducts.actualProductIso i inverses X Y

example (X Y : PartialMaps.Par (Over T)) :
    (PartialSlicePostcomposeProducts.actualProductIso i inverses X Y).hom ≫
        PartialSliceProducts.first inverses U ((postcompose i).obj X) ((postcompose i).obj Y) =
      (postcompose i).map (PartialSliceProducts.first inverses T X Y) :=
  PartialSlicePostcomposeProducts.actualProductIso_fst i inverses X Y

example (X Y : PartialMaps.Par (Over T)) :
    (PartialSlicePostcomposeProducts.actualProductIso i inverses X Y).hom ≫
        PartialSliceProducts.second inverses U ((postcompose i).obj X) ((postcompose i).obj Y) =
      (postcompose i).map (PartialSliceProducts.second inverses T X Y) :=
  PartialSlicePostcomposeProducts.actualProductIso_snd i inverses X Y

example (t : T ⟶ S) (u : U ⟶ S) (ht : i ≫ u = t) :
    (postcompose i).map ((PartialSliceTheoryFamilies.constantFunctor inverses T).map t.hom) ≫
        PartialSliceTheoryFamilies.sentenceComparison inverses i S.obj =
      PartialSliceTheoryFamilies.comparison inverses i i.hom ≫
        (PartialSliceTheoryFamilies.constantFunctor inverses U).map u.hom :=
  PartialSliceTheoryFamilies.comparison_square inverses i t.hom u.hom
    (congrArg (fun k => k.hom) ht)

example : isTotal (PartialSliceTheoryFamilies.sentenceComparison inverses i S.obj) :=
  PartialSliceTheoryFamilies.sentenceComparison_total inverses i S.obj

example : isTotal (PartialSliceTheoryFamilies.comparison inverses i i.hom) :=
  PartialSliceTheoryFamilies.comparison_total inverses i i.hom i.property

example : ((PartialSliceEquivalence.functor inverses U).map
    (PartialSliceTheoryFamilies.sentenceComparison inverses i S.obj)).hom =
      nearProd_map i.hom (𝟙 S.obj) := by
  rw [PartialSliceTheoryFamilies.sentenceComparison_value]
  rfl

example : ((PartialSliceEquivalence.functor inverses U).map
    (PartialSliceTheoryFamilies.comparison inverses i i.hom)).hom =
      nearProd_map i.hom i.hom := by
  rw [PartialSliceTheoryFamilies.comparison_value, PartialSliceTheoryComparison.comparison_value]

example : PartialSliceTuring.constantObject T S.obj ≅
    (reindex i inverses).obj (PartialSliceTuring.constantObject U S.obj) :=
  PartialSliceTheoryFamilies.sentenceIso inverses i S.obj

example (t : T ⟶ S) (u : U ⟶ S) [Mono t] [Mono u] (ht : i ≫ u = t) :
    PartialSliceTheoryFamilies.sourceTheorySubobject inverses t ≤
      PartialSliceTheoryFamilies.pulledTheorySubobject inverses i u :=
  PartialSliceTheoryFamilies.theory_bound inverses i t u ht

#print axioms PartialSlicePostcompose.functor
#print axioms PartialSlicePostcompose.full
#print axioms PartialSlicePostcompose.compose
#print axioms PartialSliceReindex.functor
#print axioms PartialSliceReindex.preserves_restriction
#print axioms PartialSliceLeftAdjunction.homEquiv
#print axioms PartialSliceLeftAdjunction.naturality_left
#print axioms PartialSliceLeftAdjunction.naturality_right
#print axioms PartialSliceLeftAdjunction.adjunction
#print axioms PartialSliceRightAdjunction.domain_absorb
#print axioms PartialSliceRightAdjunction.homEquiv
#print axioms PartialSliceRightAdjunction.naturality_left
#print axioms PartialSliceRightAdjunction.naturality_right
#print axioms PartialSliceRightAdjunction.adjunction
#print axioms PartialSliceProperness.isIso_of_terminal_image
#print axioms PartialSliceProperness.not_essSurj
#print axioms PartialMaps.inducedFunctor_comp
#print axioms PartialMaps.inducedFunctor_congr
#print axioms PartialMaps.ofSpan_factorization
#print axioms PartialSliceChangeBase.postcompose
#print axioms PartialSliceChangeBase.postcompose_full
#print axioms PartialSliceChangeBase.postcompose_faithful
#print axioms PartialSliceChangeBase.postcompose_restriction
#print axioms PartialSliceChangeBase.reindex_restriction
#print axioms PartialSliceChangeBase.reindex_eq_spanPullback
#print axioms PartialSliceChangeBase.reindex_ofTotal
#print axioms PartialSliceChangeBase.reindex_inverseMono
#print axioms PartialSliceChangeBase.leftAdjunction
#print axioms PartialSliceChangeBase.rightAdjunction
#print axioms PartialSliceChangeBase.left_naturality_left
#print axioms PartialSliceChangeBase.left_naturality_right
#print axioms PartialSliceChangeBase.right_naturality_left
#print axioms PartialSliceChangeBase.right_naturality_right
#print axioms PartialSliceChangeBase.right_unit_span
#print axioms PartialSliceChangeBase.right_unit_not_total
#print axioms PartialSliceChangeBase.not_essSurj
#print axioms PartialSliceChangeBase.postcompose_comp
#print axioms PartialSliceChangeBase.postcompose_id
#print axioms PartialSliceTheoryComparison.comparison_square
#print axioms PartialSliceTheoryComparison.sentenceIso
#print axioms PartialSliceTheoryComparison.theorem_square
#print axioms PartialSliceTheoryFamilies.comparison_square
#print axioms PartialSliceTheoryFamilies.sentenceComparison_total
#print axioms PartialSliceTheoryFamilies.comparison_total
#print axioms PartialSliceTheoryFamilies.sentenceIso
#print axioms PartialSliceTheoryFamilies.theorem_square
#print axioms PartialSliceTheoryFamilies.theoremComparison_total
#print axioms PartialSliceTheoryFamilies.theory_bound
#print axioms PartialSlicePostcomposeProducts.actualProductIso
#print axioms PartialSlicePostcomposeProducts.actualProductIso_fst
#print axioms PartialSlicePostcomposeProducts.actualProductIso_snd
