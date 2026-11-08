import CategoricalEssentialIncompleteness.V46MillerCategoryInclusion
open CategoryTheory CategoryTheory.RestrictionCategory CategoryTheory.CoprodStruct
open CategoricalEssentialIncompleteness.LocalConnectedness
namespace CategoricalEssentialIncompleteness.V46.Miller.Uniform
variable (z : Family)
attribute [instance 2000] nativeRestriction

example : RangeFunctor (Object z) PartialFunctions.Pfn := rangeFunctor z
example : (rangeFunctor z).toFunctor = inclusion z := rfl
example : (inclusion z).Faithful := inferInstance
example {X Y : Object z} (f : X ⟶ Y) :
    (inclusion z).map (rst f) = rst ((inclusion z).map f) := rfl
example {X Y : Object z} (f : X ⟶ Y) :
    (inclusion z).map (Ranges.range f).hom = (Ranges.range ((inclusion z).map f)).hom := rfl
example {X Y : Object z} (f : X ⟶ Y) (h : (inclusion z).map f = 0) : f = 0 :=
  inclusion_reflects_zero z f h
example (X Y : Object z) : coproductComparison (inclusion z) X Y =
    𝟙 (coprod ((inclusion z).obj X) ((inclusion z).obj Y)) := comparison_eq_id z X Y
example {W X Y Z : Object z} (f : W ⟶ X) (g : Y ⟶ Z) :
    (inclusion z).map (productMap f g) = PFun.prodMap f.val g.val := inclusion_product z f g
example {X Y : Object z} (L : List (X ⟶ Y)) (hc : PairwiseCompatible L)
    (x : carrier z X) (y : carrier z Y) :
    y ∈ (show Part (carrier z Y) from (inclusion z).map (finiteJoin L hc) x) ↔
      ∃ f ∈ L,y ∈ (show Part (carrier z Y) from (inclusion z).map f x) :=
  inclusion_finiteJoin_graph z L hc x y
example : (inclusion z).map (𝟙 (N z)) ≠ 0 := inclusion_nonzero z
end CategoricalEssentialIncompleteness.V46.Miller.Uniform
