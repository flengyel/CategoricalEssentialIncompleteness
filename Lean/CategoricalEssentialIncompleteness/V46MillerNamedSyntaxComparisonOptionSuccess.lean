/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerNamedSyntaxComparisonOptions

/-! # The option-success pullback for a finite-geometry functor -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v₁ v₂ u₁ u₂
open CategoryTheory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness.V46.Miller.NamedSyntaxComparison.Options
variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
variable [Regular C] [FinitaryExtensive C] [Regular D] [FinitaryExtensive D]
variable (F : C ⥤ D) [PreservesFiniteLimits F] [PreservesFiniteCoproducts F]

variable {W Y : C} {W' Y' : D}
variable (i : F.obj W ≅ W') (j : F.obj Y ≅ Y')
variable (f : W ⟶ OptionSyntax.obj Y) (f' : W' ⟶ OptionSyntax.obj Y')
variable (hf : F.map f ≫ (optionIso F j).hom = i.hom ≫ f')

include hf in
/-- The mapped success square is a pullback after the input, value and option comparison
isomorphisms. -/
theorem success_isPullback :
    IsPullback (F.map (pullback.fst f coprod.inr) ≫ i.hom)
      (F.map (pullback.snd f coprod.inr) ≫ j.hom) f' coprod.inr := by
  apply (F.map_isPullback (IsPullback.of_hasPullback f (coprod.inr : Y ⟶ OptionSyntax.obj Y))).of_iso
    (Iso.refl (F.obj (pullback f coprod.inr))) i j (optionIso F j)
  · simp
  · simp
  · exact hf
  · exact optionIso_inr F j

/-- This is the canonical isomorphism of the two success pullbacks, with both of its
projections specified below. -/
def successIso : F.obj (pullback f coprod.inr) ≅ pullback f' coprod.inr :=
  (success_isPullback F i j f f' hf).isoPullback

@[reassoc] theorem successIso_fst :
    (successIso F i j f f' hf).hom ≫ pullback.fst f' coprod.inr =
      F.map (pullback.fst f coprod.inr) ≫ i.hom :=
  (success_isPullback F i j f f' hf).isoPullback_hom_fst

@[reassoc] theorem successIso_snd :
    (successIso F i j f f' hf).hom ≫ pullback.snd f' coprod.inr =
      F.map (pullback.snd f coprod.inr) ≫ j.hom :=
  (success_isPullback F i j f f' hf).isoPullback_hom_snd

end CategoricalEssentialIncompleteness.V46.Miller.NamedSyntaxComparison.Options
