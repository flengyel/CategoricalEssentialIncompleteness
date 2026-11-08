import CategoricalEssentialIncompleteness.V46MillerCategoryProducts
open CategoryTheory CategoryTheory.RestrictionCategory
open CategoricalEssentialIncompleteness.LocalConnectedness
namespace CategoricalEssentialIncompleteness.V46.Miller.Uniform
variable {z : Family}
attribute [instance 2000] nativeRestriction

example : PCategoryStruct (Object z) := inferInstance
example : PCategory (Object z) := inferInstance
example : RecursionCategory.Prodominical (Object z) := inferInstance
example (X Y : Object z) : carrier z (product X Y) = (carrier z X × carrier z Y) := rfl
example {W X Y : Object z} (f : W ⟶ X) (g : W ⟶ Y)
    (w : carrier z W) (x : carrier z X) (y : carrier z Y) :
    (x,y) ∈ (pairing f g).val w ↔ x ∈ f.val w ∧ y ∈ g.val w := mem_pairing f g w x y
example (X Y : Object z) : productMap (𝟙 X) (𝟙 Y) = 𝟙 (product X Y) := productMap_id X Y
example {U V W X Y Z : Object z} (f : U ⟶ V) (g : V ⟶ W) (h : X ⟶ Y) (k : Y ⟶ Z) :
    productMap f h ≫ productMap g k = productMap (f ≫ g) (h ≫ k) := productMap_comp f g h k
example {X Y : Object z} (f : X ⟶ Y) :
    PCategoryStruct.rst f = rst (self := nativeRestriction) f := induced_restriction f
end CategoricalEssentialIncompleteness.V46.Miller.Uniform
