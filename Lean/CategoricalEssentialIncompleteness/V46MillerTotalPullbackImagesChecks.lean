/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerTotalPullbackImages


/-! # Statement checks in `V46MillerTotalPullbackImagesChecks` -/

@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.RestrictionCategory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.LocalConnectedness
namespace CategoricalEssentialIncompleteness.V46.Miller.Total
variable {P : Uniform.Family}
example {W X Y Z : TotalCategory P} {p : W ⟶ X} {q : W ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    (h : IsPullback p q f g) : Ranges.range q.hom = Idem.pull g.hom (Ranges.range f.hom) := pullback_image h
example {W X Y Z : TotalCategory P} {p : W ⟶ X} {q : W ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    (h : IsPullback p q f g) (x y z : ℕ) (hf : z ∈ val f.hom x) (hg : z ∈ val g.hom y) :
    ∃ w,x ∈ val p.hom w ∧ y ∈ val q.hom w := pullback_lifts_elements h x y z hf hg
end CategoricalEssentialIncompleteness.V46.Miller.Total
