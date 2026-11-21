/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerCategoryInclusion
public import CategoricalEssentialIncompleteness.V46MillerCategoryTuring
public import CategoricalEssentialIncompleteness.V46MillerOracleRelative

/-! # The fixed-oracle target and the faithful inclusion

The same closure construction is applied to the singleton oracle family.
Its entire partial numerical functions are proved equivalent to usual
relative recursiveness; no ordinary value-extension requirement occurs.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Encodable
open CategoryTheory CategoryTheory.RestrictionCategory CategoryTheory.Limits
open CategoryTheory.CoprodStruct CategoryTheory.HasCoproducts
open CategoricalEssentialIncompleteness.LocalConnectedness
namespace CategoricalEssentialIncompleteness.V46.Miller.Uniform
open OracleComputation (Ty)
attribute [instance 2000] nativeRestriction

def restrictFamily {P Q : Family} (h : Q.oracles ⊆ P.oracles) : Object P ⥤ Object Q where
  obj X := ⟨X.type⟩
  map f := ⟨f.val,by
    obtain ⟨e,he⟩ := f.represented
    exact ⟨e,fun p hp x y => he p (h hp) x y⟩⟩
  map_id _ := Arrow.ext rfl
  map_comp _ _ := Arrow.ext rfl

instance {P Q : Family} (h : Q.oracles ⊆ P.oracles) : (restrictFamily h).Faithful where
  map_injective := by
    intro X Y f g he
    apply Arrow.ext
    exact congrArg (fun k : (restrictFamily h).obj X ⟶ (restrictFamily h).obj Y => k.val) he

theorem restrictFamily_map_val {P Q : Family} (h : Q.oracles ⊆ P.oracles)
    {X Y : Object P} (f : X ⟶ Y) : ((restrictFamily h).map f).val = f.val := rfl

theorem restrictFamily_i0 {P Q : Family} (h : Q.oracles ⊆ P.oracles) (X Y : Object P) :
    (restrictFamily h).map (i0 X Y) = i0 ((restrictFamily h).obj X) ((restrictFamily h).obj Y) :=
  Arrow.ext rfl

theorem restrictFamily_i1 {P Q : Family} (h : Q.oracles ⊆ P.oracles) (X Y : Object P) :
    (restrictFamily h).map (i1 X Y) = i1 ((restrictFamily h).obj X) ((restrictFamily h).obj Y) :=
  Arrow.ext rfl

theorem restrictFamily_comparison {P Q : Family} (h : Q.oracles ⊆ P.oracles) (X Y : Object P) :
    coproductComparison (restrictFamily h) X Y =
      𝟙 (coprod ((restrictFamily h).obj X) ((restrictFamily h).obj Y)) := by
  rw [coproductComparison,restrictFamily_i0,restrictFamily_i1,copair_i0_i1]

def restrictFamilyRangeFunctor {P Q : Family} (h : Q.oracles ⊆ P.oracles) :
    RangeFunctor (Object P) (Object Q) where
  toFunctor := restrictFamily h
  map_restrict _ := Arrow.ext rfl
  map_range _ := Arrow.ext rfl
  map_zero _ _ := Arrow.ext rfl
  comparison_isIso X Y := by
    rw [restrictFamily_comparison]
    exact (Iso.refl (coprod ((restrictFamily h).obj X) ((restrictFamily h).obj Y))).isIso_hom

theorem restrictFamily_product {P Q : Family} (h : Q.oracles ⊆ P.oracles)
    {W X Y Z : Object P} (f : W ⟶ X) (g : Y ⟶ Z) :
    (restrictFamily h).map (productMap f g) =
      productMap ((restrictFamily h).map f) ((restrictFamily h).map g) := Arrow.ext rfl

def restrictFamilyProductIso {P Q : Family} (h : Q.oracles ⊆ P.oracles) (X Y : Object P) :
    (restrictFamily h).obj (product X Y) ≅ product ((restrictFamily h).obj X) ((restrictFamily h).obj Y) :=
  Iso.refl _

theorem restrictFamily_compatible {P Q : Family} (h : Q.oracles ⊆ P.oracles)
    {X Y : Object P} (f g : X ⟶ Y) (hc : Compatible f g) :
    Compatible ((restrictFamily h).map f) ((restrictFamily h).map g) :=
  (compatible_iff _ _).mpr ((compatible_iff f g).mp hc)

theorem restrictFamily_pairwiseCompatible {P Q : Family} (h : Q.oracles ⊆ P.oracles)
    {X Y : Object P} (L : List (X ⟶ Y)) (hc : PairwiseCompatible L) :
    PairwiseCompatible (L.map (fun f => (restrictFamily h).map f)) := by
  intro f' hf' g' hg'
  obtain ⟨f,hf,rfl⟩ := List.mem_map.mp hf'
  obtain ⟨g,hg,rfl⟩ := List.mem_map.mp hg'
  exact restrictFamily_compatible h f g (hc f hf g hg)

theorem restrictFamily_finiteJoin {P Q : Family} (h : Q.oracles ⊆ P.oracles)
    {X Y : Object P} (L : List (X ⟶ Y)) (hc : PairwiseCompatible L) :
    (restrictFamily h).map (finiteJoin L hc) =
      finiteJoin (L.map (fun f => (restrictFamily h).map f))
        (restrictFamily_pairwiseCompatible h L hc) := by
  apply hom_ext_mem
  intro x y
  change y ∈ (finiteJoin L hc).val x ↔ _
  rw [finiteJoin_graph,finiteJoin_graph]
  simp only [List.mem_map]
  constructor
  · rintro ⟨f,hf,hy⟩
    exact ⟨(restrictFamily h).map f,⟨f,hf,rfl⟩,hy⟩
  · rintro ⟨f',⟨f,hf,rfl⟩,hy⟩
    exact ⟨f,hf,hy⟩

abbrev RelativeObject (p : Bits) := Object (Family.singleton p)

theorem singleton_represented_iff_recursiveIn (p : Bits) (X Y : Ty)
    (f : X.carrier → Part Y.carrier) :
    Represented (Family.singleton p) X Y f ↔
      Nat.RecursiveIn (OracleComputation.oracleSet (OracleRelative.oracleSupport p))
        (encodeFunction X Y f) := by
  rw [represented_iff_numerical]
  constructor
  · rintro ⟨e,he⟩
    exact (OracleRelative.numberedEval_recursiveIn e p).of_eq
      (fun n => Part.ext (fun y => (he p rfl n y).symm))
  · intro hf
    obtain ⟨e,he⟩ := OracleRelative.exists_index_of_recursiveIn p (encodeFunction X Y f) hf
    refine ⟨e,?_⟩
    intro p' hp' n y
    have hpp : p' = p := Set.mem_singleton_iff.mp hp'
    subst p'
    exact (Iff.of_eq (congrArg (fun v : Part ℕ => y ∈ v) (he n))).symm

theorem relative_morphism_iff (p : Bits) (X Y : RelativeObject p)
    (f : carrier (Family.singleton p) X → Part (carrier (Family.singleton p) Y)) :
    (∃ g : X ⟶ Y,g.val = f) ↔
      Nat.RecursiveIn (OracleComputation.oracleSet (OracleRelative.oracleSupport p))
        (encodeFunction X.type Y.type f) := by
  constructor
  · rintro ⟨g,rfl⟩
    exact (singleton_represented_iff_recursiveIn p X.type Y.type g.val).mp g.represented
  · intro hf
    exact ⟨⟨f,(singleton_represented_iff_recursiveIn p X.type Y.type f).mpr hf⟩,rfl⟩

private theorem universal_numbered (p : Bits) (e n : ℕ) :
    OracleProgram.numberedEval (encode OracleProgram.universalCode) p (Nat.pair e n) =
      OracleProgram.numberedEval e p n := by
  rw [OracleProgram.numberedEval_encode]
  have he := OracleProgram.universalCode_eval (Denumerable.ofNat OracleProgram.Code e) p n
  simpa only [OracleProgram.numberedEval,Denumerable.encode_ofNat] using he

def oracleTau (p : Bits) :
    product (N (Family.singleton p)) (N (Family.singleton p)) ⟶ N (Family.singleton p) :=
  ⟨fun a => OracleProgram.numberedEval a.1 p a.2,⟨encode OracleProgram.universalCode,by
    intro q hq a y
    have hqp : q=p := Set.mem_singleton_iff.mp hq
    subst q
    exact Iff.of_eq (congrArg (fun v : Part ℕ => y ∈ v) (universal_numbered p a.1 a.2).symm)⟩⟩

theorem oracleTau_graph (p : Bits) (e n y : ℕ) :
    y ∈ (oracleTau p).val (e,n) ↔ y ∈ OracleProgram.numberedEval e p n := Iff.rfl

theorem oracleTau_parameterization (p : Bits) (Y : RelativeObject p)
    (f : product Y (N (Family.singleton p)) ⟶ N (Family.singleton p)) :
    ∃ r : Y ⟶ N (Family.singleton p),isTotal r ∧
      productMap r (𝟙 (N (Family.singleton p))) ≫ oracleTau p = f := by
  obtain ⟨e,he⟩ := f.represented
  let r : Y ⟶ N (Family.singleton p) := totalFromFunction
    (parameterIndex e Y) (parameterIndex_computable e Y)
  refine ⟨r,totalFromFunction_total _ _,?_⟩
  apply hom_ext_mem
  rintro ⟨y,n⟩ m
  simp only [comp_val,productMap_val,id_val,r,totalFromFunction,ofPartrec,
    Part.bind_some,Part.map_some,parameterIndex]
  change m ∈ OracleProgram.numberedEval (OracleProgram.specializationIndex e (Y.type.toNat y)) p n ↔ _
  rw [OracleProgram.specializationIndex_eval]
  exact (he p rfl (y,n) m).symm

theorem oracleTau_isTuring (p : Bits) : RecursionCategory.IsTuringMorphism (oracleTau p) := by
  intro Y f
  obtain ⟨r,hr,he⟩ := oracleTau_parameterization p Y f
  refine ⟨r,?_,he⟩
  change PCategoryStruct.rst r = 𝟙 Y
  rw [induced_restriction]
  exact hr

instance relativeRecursionCategory (p : Bits) : RecursionCategory.PRecursionCategory (RelativeObject p) where
  W := N (Family.singleton p)
  X := N (Family.singleton p)
  Y := N (Family.singleton p)
  tau := oracleTau p
  is_turing := oracleTau_isTuring p

def J (z : Point) (p : Bits) (hp : p ∈ representations z) :
    RangeFunctor (PointObject z) (RelativeObject p) :=
  restrictFamilyRangeFunctor (P := Family.ofPoint z) (Q := Family.singleton p)
    (fun q hq => by
      have hqp : q=p := Set.mem_singleton_iff.mp hq
      subst q
      exact hp)

instance (z : Point) (p : Bits) (hp : p ∈ representations z) : (J z p hp).toFunctor.Faithful :=
  inferInstanceAs ((restrictFamily (P := Family.ofPoint z) (Q := Family.singleton p)
    (fun q hq => by
      have hqp : q=p := Set.mem_singleton_iff.mp hq
      subst q
      exact hp)).Faithful)

theorem J_value (z : Point) (p : Bits) (hp : p ∈ representations z)
    {X Y : PointObject z} (f : X ⟶ Y) : ((J z p hp).toFunctor.map f).val = f.val := rfl

theorem J_product (z : Point) (p : Bits) (hp : p ∈ representations z)
    {W X Y Z : PointObject z} (f : W ⟶ X) (g : Y ⟶ Z) :
    (J z p hp).toFunctor.map (productMap f g) =
      productMap ((J z p hp).toFunctor.map f) ((J z p hp).toFunctor.map g) := Arrow.ext rfl

theorem J_pairwiseCompatible (z : Point) (p : Bits) (hp : p ∈ representations z)
    {X Y : PointObject z} (L : List (X ⟶ Y)) (hc : PairwiseCompatible L) :
    PairwiseCompatible (L.map (fun f => (J z p hp).toFunctor.map f)) := by
  intro f' hf' g' hg'
  obtain ⟨f,hf,rfl⟩ := List.mem_map.mp hf'
  obtain ⟨g,hg,rfl⟩ := List.mem_map.mp hg'
  exact (compatible_iff _ _).mpr ((compatible_iff f g).mp (hc f hf g hg))

theorem J_finiteJoin (z : Point) (p : Bits) (hp : p ∈ representations z)
    {X Y : PointObject z} (L : List (X ⟶ Y)) (hc : PairwiseCompatible L) :
    (J z p hp).toFunctor.map (finiteJoin L hc) =
      finiteJoin (L.map (fun f => (J z p hp).toFunctor.map f)) (J_pairwiseCompatible z p hp L hc) := by
  apply hom_ext_mem
  intro x y
  change y ∈ (finiteJoin L hc).val x ↔ _
  rw [finiteJoin_graph,finiteJoin_graph]
  simp only [List.mem_map]
  constructor
  · rintro ⟨f,hf,hy⟩
    exact ⟨(J z p hp).toFunctor.map f,⟨f,hf,rfl⟩,hy⟩
  · rintro ⟨f',⟨f,hf,rfl⟩,hy⟩
    exact ⟨f,hf,hy⟩

theorem J_nonzero (z : Point) (p : Bits) (hp : p ∈ representations z) :
    (J z p hp).toFunctor.map (𝟙 (N (Family.ofPoint z))) ≠ 0 := by
  intro he
  have h0 := congrArg (fun f => f.val (0 : ℕ)) he
  change Part.some (0 : ℕ) = Part.none at h0
  have hm := Part.mem_some (0 : ℕ)
  rw [h0] at hm
  exact hm.1

end CategoricalEssentialIncompleteness.V46.Miller.Uniform
