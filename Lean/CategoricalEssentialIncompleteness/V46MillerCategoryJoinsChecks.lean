import CategoricalEssentialIncompleteness.V46MillerCategoryJoins
open CategoryTheory CategoryTheory.RestrictionCategory
open CategoricalEssentialIncompleteness.LocalConnectedness
namespace CategoricalEssentialIncompleteness.V46.Miller.Uniform
variable {z : Family}
attribute [instance 2000] nativeRestriction

example : DisjointArrowJoins (Object z) := inferInstance
example {X Y : Object z} (f g : X ⟶ Y)
    (hd : Idem.ofRestrict f ⊓ Idem.ofRestrict g = ⊥) : rst f ≫ g = rst g ≫ f :=
  compatible_of_disjoint f g hd
example {X Y : Object z} (f g : X ⟶ Y) :
    Compatible f g ↔ ∀ x a b,a ∈ f.val x → b ∈ g.val x → a = b := compatible_iff f g
example {X Y : Object z} (f g : X ⟶ Y) :
    Below f g ↔ ∀ x y,y ∈ f.val x → y ∈ g.val x := below_iff f g
example {X Y : Object z} (f g : X ⟶ Y) (hc : rst f ≫ g = rst g ≫ f)
    (x : carrier z X) (y : carrier z Y) :
    y ∈ (join f g hc).val x ↔ y ∈ f.val x ∨ y ∈ g.val x := join_graph f g hc x y
example {X Y : Object z} (f g : X ⟶ Y) (hc : Compatible f g) :
    rst f ≫ join f g hc = f := join_left f g hc
example {X Y : Object z} (f g : X ⟶ Y) (hc : Compatible f g) :
    rst g ≫ join f g hc = g := join_right f g hc
example {X Y : Object z} (f g h : X ⟶ Y) (hc : Compatible f g)
    (hf : rst f ≫ h = f) (hg : rst g ≫ h = g) : rst (join f g hc) ≫ h = join f g hc :=
  join_least f g h hc hf hg
example {W X Y : Object z} (h : W ⟶ X) (f g : X ⟶ Y) (hc : Compatible f g) :
    h ≫ join f g hc = join (h ≫ f) (h ≫ g) (compatible_comp_left h f g hc) := comp_join h f g hc
example {X Y Z : Object z} (f g : X ⟶ Y) (h : Y ⟶ Z) (hc : Compatible f g) :
    join f g hc ≫ h = join (f ≫ h) (g ≫ h) (compatible_comp_right f g h hc) := join_comp f g h hc
example {X Y : Object z} (f : X ⟶ Y) : rst (0 : X ⟶ Y) ≫ f = 0 := zero_below f
example {X Y : Object z} (L : List (X ⟶ Y)) (hc : ∀ f ∈ L,∀ g ∈ L,rst f ≫ g = rst g ≫ f)
    (x : carrier z X) (y : carrier z Y) :
    y ∈ (finiteJoin L hc).val x ↔ ∃ f ∈ L,y ∈ f.val x := finiteJoin_graph L hc x y
example {X Y : Object z} (L : List (X ⟶ Y)) (hc : PairwiseCompatible L)
    (f : X ⟶ Y) (hf : f ∈ L) : rst f ≫ finiteJoin L hc = f := le_finiteJoin L hc f hf
example {X Y : Object z} (L : List (X ⟶ Y)) (hc : PairwiseCompatible L)
    (h : X ⟶ Y) (hh : ∀ f ∈ L,rst f ≫ h = f) : rst (finiteJoin L hc) ≫ h = finiteJoin L hc :=
  finiteJoin_least L hc h hh
example {X Y : Object z} (hc : PairwiseCompatible ([] : List (X ⟶ Y))) :
    finiteJoin [] hc = (0 : X ⟶ Y) := finiteJoin_nil hc
example {W X Y : Object z} (h : W ⟶ X) (L : List (X ⟶ Y)) (hc : PairwiseCompatible L) :
    h ≫ finiteJoin L hc =
      finiteJoin (L.map (fun f => h ≫ f)) (pairwiseCompatible_comp_left h L hc) := comp_finiteJoin h L hc
example {X Y Z : Object z} (L : List (X ⟶ Y)) (h : Y ⟶ Z) (hc : PairwiseCompatible L) :
    finiteJoin L hc ≫ h =
      finiteJoin (L.map (fun f => f ≫ h)) (pairwiseCompatible_comp_right L h hc) := finiteJoin_comp L h hc
end CategoricalEssentialIncompleteness.V46.Miller.Uniform
