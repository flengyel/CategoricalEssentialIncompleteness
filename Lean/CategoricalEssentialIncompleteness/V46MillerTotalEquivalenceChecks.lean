/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerTotalEquivalence


/-! # The semidecidable presentation of the total splitting -/

@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.RestrictionCategory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.LocalConnectedness
namespace CategoricalEssentialIncompleteness.V46.Miller.Total
variable {P : Uniform.Family}
example : (inclusion (P := P)).Full := inferInstance
example : (inclusion (P := P)).Faithful := inferInstance
example : (inclusion (P := P)).EssSurj := inferInstance
example : Carrier P ≌ SplitObject (Uniform.Object P) := carrierEquivalence
example : PreservesRestriction (inclusion (P := P)) := inclusion_rst
example : TotalCategory P ≌ WideSubcategory (isTotal (C := SplitObject (Uniform.Object P))) := totalEquivalence
example (z : Point) : PointTotal z ≌ WideSubcategory (isTotal (C := SplitObject (Uniform.PointObject z))) := pointPresentation z
example (z : Point) {X Y : PointTotal z} (f : X ⟶ Y) :
    ((pointPresentation z).functor.map f).hom.hom.val = val f.hom := pointPresentation_value z f
end CategoricalEssentialIncompleteness.V46.Miller.Total
