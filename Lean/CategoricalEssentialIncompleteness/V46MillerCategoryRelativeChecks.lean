import CategoricalEssentialIncompleteness.V46MillerCategoryRelative
noncomputable section
open CategoryTheory CategoryTheory.RestrictionCategory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.LocalConnectedness
namespace CategoricalEssentialIncompleteness.V46.Miller.Uniform
open OracleComputation (Ty)
attribute [instance 2000] nativeRestriction

example (P : Family) : P.oracles.Nonempty := P.nonempty
example (z : Point) : (Family.ofPoint z).oracles = representations z := rfl
example (p : Bits) : (Family.singleton p).oracles = {p} := rfl
example {P Q : Family} (h : Q.oracles ⊆ P.oracles) :
    RangeFunctor (Object P) (Object Q) := restrictFamilyRangeFunctor h
example {P Q : Family} (h : Q.oracles ⊆ P.oracles) : (restrictFamily h).Faithful := inferInstance
example {P Q : Family} (h : Q.oracles ⊆ P.oracles) {X Y : Object P} (f : X ⟶ Y) :
    ((restrictFamily h).map f).val = f.val := restrictFamily_map_val h f
example {P Q : Family} (h : Q.oracles ⊆ P.oracles) {X Y : Object P} (f : X ⟶ Y) :
    (restrictFamily h).map (rst f) = rst ((restrictFamily h).map f) := Arrow.ext rfl
example {P Q : Family} (h : Q.oracles ⊆ P.oracles) {X Y : Object P} (f : X ⟶ Y) :
    (restrictFamily h).map (Ranges.range f).hom =
      (Ranges.range ((restrictFamily h).map f)).hom := Arrow.ext rfl
example {P Q : Family} (h : Q.oracles ⊆ P.oracles) {W X Y Z : Object P}
    (f : W ⟶ X) (g : Y ⟶ Z) :
    (restrictFamily h).map (productMap f g) =
      productMap ((restrictFamily h).map f) ((restrictFamily h).map g) := restrictFamily_product h f g
example {P Q : Family} (h : Q.oracles ⊆ P.oracles) {X Y : Object P}
    (L : List (X ⟶ Y)) (hc : PairwiseCompatible L) :
    (restrictFamily h).map (finiteJoin L hc) =
      finiteJoin (L.map (fun f => (restrictFamily h).map f))
        (restrictFamily_pairwiseCompatible h L hc) := restrictFamily_finiteJoin h L hc

example (p : Bits) (X Y : Ty) (f : X.carrier → Part Y.carrier) :
    Represented (Family.singleton p) X Y f ↔
      Nat.RecursiveIn (OracleComputation.oracleSet (OracleRelative.oracleSupport p))
        (fun n => (f (X.fromNat n)).map Y.toNat) := singleton_represented_iff_recursiveIn p X Y f
example (p : Bits) (X Y : RelativeObject p)
    (f : carrier (Family.singleton p) X → Part (carrier (Family.singleton p) Y)) :
    (∃ g : X ⟶ Y,g.val = f) ↔
      Nat.RecursiveIn (OracleComputation.oracleSet (OracleRelative.oracleSupport p))
        (encodeFunction X.type Y.type f) := relative_morphism_iff p X Y f
example (p : Bits) : RecursionCategory.PRecursionCategory (RelativeObject p) := inferInstance
example (p : Bits) (e n y : ℕ) :
    y ∈ (oracleTau p).val (e,n) ↔ y ∈ OracleProgram.numberedEval e p n := oracleTau_graph p e n y
example (p : Bits) : RecursionCategory.IsTuringMorphism (oracleTau p) := oracleTau_isTuring p

example (z : Point) (p : Bits) (hp : p ∈ representations z) :
    RangeFunctor (PointObject z) (RelativeObject p) := J z p hp
example (z : Point) (p : Bits) (hp : p ∈ representations z) : (J z p hp).toFunctor.Faithful := inferInstance
example (z : Point) (p : Bits) (hp : p ∈ representations z) {X Y : PointObject z} (f : X ⟶ Y) :
    ((J z p hp).toFunctor.map f).val = f.val := J_value z p hp f
example (z : Point) (p : Bits) (hp : p ∈ representations z) {X Y : PointObject z} (f : X ⟶ Y) :
    (J z p hp).toFunctor.map (rst f) = rst ((J z p hp).toFunctor.map f) := Arrow.ext rfl
example (z : Point) (p : Bits) (hp : p ∈ representations z) {X Y : PointObject z} (f : X ⟶ Y) :
    (J z p hp).toFunctor.map (Ranges.range f).hom =
      (Ranges.range ((J z p hp).toFunctor.map f)).hom := Arrow.ext rfl
example (z : Point) (p : Bits) (hp : p ∈ representations z) {W X Y Z : PointObject z}
    (f : W ⟶ X) (g : Y ⟶ Z) :
    (J z p hp).toFunctor.map (productMap f g) =
      productMap ((J z p hp).toFunctor.map f) ((J z p hp).toFunctor.map g) := J_product z p hp f g
example (z : Point) (p : Bits) (hp : p ∈ representations z) {X Y : PointObject z}
    (L : List (X ⟶ Y)) (hc : PairwiseCompatible L) :
    (J z p hp).toFunctor.map (finiteJoin L hc) =
      finiteJoin (L.map (fun f => (J z p hp).toFunctor.map f)) (J_pairwiseCompatible z p hp L hc) :=
  J_finiteJoin z p hp L hc
example (z : Point) (p : Bits) (hp : p ∈ representations z) :
    (J z p hp).toFunctor.map (𝟙 (N (Family.ofPoint z))) ≠ 0 := J_nonzero z p hp
end CategoricalEssentialIncompleteness.V46.Miller.Uniform
