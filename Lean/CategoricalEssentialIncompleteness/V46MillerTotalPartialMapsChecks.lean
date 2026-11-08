import CategoricalEssentialIncompleteness.V46MillerTotalPartialMaps
noncomputable section
open CategoryTheory CategoryTheory.RestrictionCategory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.LocalConnectedness
namespace CategoricalEssentialIncompleteness.V46.Miller.Total
variable {P : Uniform.Family}
example (z : Point) : PartialMaps.Par (WideSubcategory (isTotal (C := SplitObject (Uniform.PointObject z)))) ≌
    SplitObject (Uniform.PointObject z) := partialMapEquivalence z
example (z : Point) {X Y : PartialMaps.Par (CanonicalTotal z)} (f : X ⟶ Y) :
    (partialMapEquivalence z).functor.map (rst f) = rst ((partialMapEquivalence z).functor.map f) :=
  partialMap_preserves_restrictions z f
example (z : Point) {X Y : SplitObject (Uniform.PointObject z)} (f : X ⟶ Y) :
    (partialMapEquivalence z).inverse.map (rst f) = rst ((partialMapEquivalence z).inverse.map f) :=
  partialMap_inverse_preserves_restrictions z f
example (z : Point) {X Y : CanonicalTotal z} (m : X ⟶ Y) [Mono m] :
    ∃ r : Y.obj ⟶ X.obj,m.hom ≫ r = 𝟙 X.obj ∧ r ≫ m.hom = rst r := mono_has_partial_inverse z m
end CategoricalEssentialIncompleteness.V46.Miller.Total
