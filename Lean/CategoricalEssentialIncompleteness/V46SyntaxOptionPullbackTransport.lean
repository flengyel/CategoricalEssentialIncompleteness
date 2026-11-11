/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SyntaxOptionTransport

/-! # The actual success pullback through the option comparison -/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v₁ v₂ u₁ u₂
open CategoryTheory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness.V46.SyntaxOptionTransport
variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
variable [Regular C] [FinitaryExtensive C] [Regular D] [FinitaryExtensive D]
variable (E : C ≌ D)
local notation "F" => E.functor

variable {W Y : C} {W' Y' : D}
variable (i : E.functor.obj W ≅ W') (j : E.functor.obj Y ≅ Y')
variable (f : W ⟶ OptionSyntax.obj Y) (f' : W' ⟶ OptionSyntax.obj Y')
variable (hf : E.functor.map f ≫ (optionIso E j).hom = i.hom ≫ f')

include hf in
/-- The mapped success square is a pullback after the actual input,
value and option comparison isomorphisms. -/
theorem success_isPullback :
    IsPullback (E.functor.map (pullback.fst f coprod.inr) ≫ i.hom)
      (E.functor.map (pullback.snd f coprod.inr) ≫ j.hom) f' coprod.inr := by
  apply (E.functor.map_isPullback (IsPullback.of_hasPullback f (coprod.inr : Y ⟶ OptionSyntax.obj Y))).of_iso
    (Iso.refl (E.functor.obj (pullback f coprod.inr))) i j (optionIso E j)
  · simp
  · simp
  · exact hf
  · exact optionIso_inr E j

/-- This is the canonical isomorphism of the two actual success
pullbacks, with both of its projections specified below. -/
def successIso : E.functor.obj (pullback f coprod.inr) ≅ pullback f' coprod.inr :=
  (success_isPullback E i j f f' hf).isoPullback

@[reassoc] theorem successIso_fst :
    (successIso E i j f f' hf).hom ≫ pullback.fst f' coprod.inr =
      E.functor.map (pullback.fst f coprod.inr) ≫ i.hom :=
  (success_isPullback E i j f f' hf).isoPullback_hom_fst

@[reassoc] theorem successIso_snd :
    (successIso E i j f f' hf).hom ≫ pullback.snd f' coprod.inr =
      E.functor.map (pullback.snd f coprod.inr) ≫ j.hom :=
  (success_isPullback E i j f f' hf).isoPullback_hom_snd

end CategoricalEssentialIncompleteness.V46.SyntaxOptionTransport
