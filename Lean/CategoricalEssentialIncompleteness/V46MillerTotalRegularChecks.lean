/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerTotalRegular


/-! # Regularity from uniform fiber-constant descent -/

@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.RestrictionCategory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.LocalConnectedness
namespace CategoricalEssentialIncompleteness.V46.Miller.Total
variable {P : Uniform.Family}
example : Regular (TotalCategory P) := inferInstance
example {X Y Z : TotalCategory P} (e : X ⟶ Y) (he : Surjective e.hom) (h : X ⟶ Z)
    (hc : FiberConstant e h) : e ≫ descent e he h hc = h := descent_fac e he h hc
example {X Y Z : TotalCategory P} (e : X ⟶ Y) (he : Surjective e.hom) (h : X ⟶ Z)
    (hc : FiberConstant e h) (k : Y ⟶ Z) (hk : e ≫ k = h) : k = descent e he h hc := descent_unique e he h hc k hk
example {X Y K : TotalCategory P} (e : X ⟶ Y) (he : Surjective e.hom) {a b : K ⟶ X} (hk : IsKernelPair e a b) :
    IsColimit (Cofork.ofπ e hk.w) := surjectionCoforkIsColimit e he hk
example {X Y : TotalCategory P} (e : X ⟶ Y) (he : Surjective e.hom) : IsRegularEpi e := isRegularEpi_of_surjective e he
example {X Y : TotalCategory P} (f : X ⟶ Y) : IsRegularEpi f ↔ Ranges.range f.hom = ⊤ := regularEpi_iff_range_top f
example {X Y : TotalCategory P} (f : X ⟶ Y) : IsImage (imageFactorization f).toMonoFactorisation := imageIsImage f
end CategoricalEssentialIncompleteness.V46.Miller.Total
