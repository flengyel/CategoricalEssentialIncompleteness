/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import PCats.DomPullbacks

/-!
# Signature guards for pullbacks in `Dom C`

Exact `@`-ascriptions guard the eleven public telescopes. Applied examples guard
the general pullback declarations at arbitrary objects `A`, `B`, `D`, apex `W`,
and arrows `f`, `g`, `h`, `k`; they guard the Lemma A.4 specialization at
arbitrary objects `X`, `Y`, `Z` and arrows `f`, `q`. All contexts assume
`[HasRanges C]` and no stronger structure. `check_axioms.lean` audits axiom
dependencies.

`autoImplicit` is off: `lake env lean` does not apply the package's
`leanOptions`, and an unbound identifier would otherwise be auto-bound and the
guard would hold vacuously.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe v u

namespace CategoryTheory

#check @Dom.pullbackObject
#check @Dom.pullbackFst
#check @Dom.pullbackSnd
#check @Dom.pullback_comm
#check @Dom.pullbackLift
#check @Dom.pullbackLift_fst
#check @Dom.pullbackLift_snd
#check @Dom.pullbackLift_unique
#check @Dom.pullback_existsUnique
#check @Dom.rangeLiftPullback_isPullbackSquare
#check @Dom.exists_total_lift_iff_rangeLiftPullback_section

/-! ### The pullback object and its legs -/

example : ∀ {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
    [HasRanges C] {A B D : Dom C}, (A ⟶ D) → (B ⟶ D) → Dom C :=
  @Dom.pullbackObject

example {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
    [HasRanges C] {A B D : Dom C} (f : A ⟶ D) (g : B ⟶ D) :
    Dom.pullbackObject f g
      = Dom.equalizerObject (Dom.binaryProductFst A B ≫ f)
          (Dom.binaryProductSnd A B ≫ g) :=
  rfl

example : ∀ {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
    [HasRanges C] {A B D : Dom C} (f : A ⟶ D) (g : B ⟶ D),
    Dom.pullbackObject f g ⟶ A :=
  @Dom.pullbackFst

example {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
    [HasRanges C] {A B D : Dom C} (f : A ⟶ D) (g : B ⟶ D) :
    Dom.pullbackFst f g
      = Dom.equalizerInclusion (Dom.binaryProductFst A B ≫ f)
            (Dom.binaryProductSnd A B ≫ g) ≫ Dom.binaryProductFst A B :=
  rfl

example : ∀ {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
    [HasRanges C] {A B D : Dom C} (f : A ⟶ D) (g : B ⟶ D),
    Dom.pullbackObject f g ⟶ B :=
  @Dom.pullbackSnd

example {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
    [HasRanges C] {A B D : Dom C} (f : A ⟶ D) (g : B ⟶ D) :
    Dom.pullbackSnd f g
      = Dom.equalizerInclusion (Dom.binaryProductFst A B ≫ f)
            (Dom.binaryProductSnd A B ≫ g) ≫ Dom.binaryProductSnd A B :=
  rfl

/-! ### Commutativity -/

example : ∀ {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
    [HasRanges C] {A B D : Dom C} (f : A ⟶ D) (g : B ⟶ D),
    Dom.pullbackFst f g ≫ f = Dom.pullbackSnd f g ≫ g :=
  @Dom.pullback_comm

example {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
    [HasRanges C] {A B D : Dom C} (f : A ⟶ D) (g : B ⟶ D) :
    Dom.pullbackFst f g ≫ f = Dom.pullbackSnd f g ≫ g :=
  Dom.pullback_comm f g

/-! ### The lift and its two equations -/

example : ∀ {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
    [HasRanges C] {A B D W : Dom C} (f : A ⟶ D) (g : B ⟶ D) (h : W ⟶ A)
    (k : W ⟶ B), h ≫ f = k ≫ g → (W ⟶ Dom.pullbackObject f g) :=
  @Dom.pullbackLift

example : ∀ {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
    [HasRanges C] {A B D W : Dom C} (f : A ⟶ D) (g : B ⟶ D) (h : W ⟶ A)
    (k : W ⟶ B) (hfg : h ≫ f = k ≫ g),
    Dom.pullbackLift f g h k hfg ≫ Dom.pullbackFst f g = h :=
  @Dom.pullbackLift_fst

example {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
    [HasRanges C] {A B D W : Dom C} (f : A ⟶ D) (g : B ⟶ D) (h : W ⟶ A)
    (k : W ⟶ B) (hfg : h ≫ f = k ≫ g) :
    Dom.pullbackLift f g h k hfg ≫ Dom.pullbackFst f g = h :=
  Dom.pullbackLift_fst f g h k hfg

example : ∀ {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
    [HasRanges C] {A B D W : Dom C} (f : A ⟶ D) (g : B ⟶ D) (h : W ⟶ A)
    (k : W ⟶ B) (hfg : h ≫ f = k ≫ g),
    Dom.pullbackLift f g h k hfg ≫ Dom.pullbackSnd f g = k :=
  @Dom.pullbackLift_snd

example {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
    [HasRanges C] {A B D W : Dom C} (f : A ⟶ D) (g : B ⟶ D) (h : W ⟶ A)
    (k : W ⟶ B) (hfg : h ≫ f = k ≫ g) :
    Dom.pullbackLift f g h k hfg ≫ Dom.pullbackSnd f g = k :=
  Dom.pullbackLift_snd f g h k hfg

/-! ### Uniqueness -/

example : ∀ {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
    [HasRanges C] {A B D W : Dom C} (f : A ⟶ D) (g : B ⟶ D) (h : W ⟶ A)
    (k : W ⟶ B) (hfg : h ≫ f = k ≫ g) (l : W ⟶ Dom.pullbackObject f g),
    l ≫ Dom.pullbackFst f g = h → l ≫ Dom.pullbackSnd f g = k →
    l = Dom.pullbackLift f g h k hfg :=
  @Dom.pullbackLift_unique

example {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
    [HasRanges C] {A B D W : Dom C} (f : A ⟶ D) (g : B ⟶ D) (h : W ⟶ A)
    (k : W ⟶ B) (hfg : h ≫ f = k ≫ g) (l : W ⟶ Dom.pullbackObject f g)
    (hl : l ≫ Dom.pullbackFst f g = h) (hk : l ≫ Dom.pullbackSnd f g = k) :
    l = Dom.pullbackLift f g h k hfg :=
  Dom.pullbackLift_unique f g h k hfg l hl hk

/-! ### The universal property -/

example : ∀ {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
    [HasRanges C] {A B D W : Dom C} (f : A ⟶ D) (g : B ⟶ D) (h : W ⟶ A)
    (k : W ⟶ B), h ≫ f = k ≫ g →
    ∃! l : W ⟶ Dom.pullbackObject f g,
      l ≫ Dom.pullbackFst f g = h ∧ l ≫ Dom.pullbackSnd f g = k :=
  @Dom.pullback_existsUnique

example {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
    [HasRanges C] {A B D W : Dom C} (f : A ⟶ D) (g : B ⟶ D) (h : W ⟶ A)
    (k : W ⟶ B) (hfg : h ≫ f = k ≫ g) :
    ∃! l : W ⟶ Dom.pullbackObject f g,
      l ≫ Dom.pullbackFst f g = h ∧ l ≫ Dom.pullbackSnd f g = k :=
  Dom.pullback_existsUnique f g h k hfg

/-- The universal property destructured: an arbitrary commuting cone over an
arbitrary cospan factors through a unique morphism. -/
example {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
    [HasRanges C] {A B D W : Dom C} (f : A ⟶ D) (g : B ⟶ D) (h : W ⟶ A)
    (k : W ⟶ B) (hfg : h ≫ f = k ≫ g) :
    ∃ l : W ⟶ Dom.pullbackObject f g,
      l ≫ Dom.pullbackFst f g = h ∧ l ≫ Dom.pullbackSnd f g = k ∧
        Dom.pullbackFst f g ≫ f = Dom.pullbackSnd f g ≫ g ∧
        ∀ m : W ⟶ Dom.pullbackObject f g,
          m ≫ Dom.pullbackFst f g = h → m ≫ Dom.pullbackSnd f g = k → m = l := by
  obtain ⟨l, ⟨hl, hk⟩, hu⟩ := Dom.pullback_existsUnique f g h k hfg
  exact ⟨l, hl, hk, Dom.pullback_comm f g, fun m hm hm' => hu m ⟨hm, hm'⟩⟩

/-! ### `HasRanges` suffices; `IsRP` is not required

The context here supplies `HasRanges` and no `IsRP` instance, so an `IsRP`
premise in any of the eleven declarations would make these fail to
elaborate. -/

example {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
    [HasRanges C] {A B D W : Dom C} (f : A ⟶ D) (g : B ⟶ D) (h : W ⟶ A)
    (k : W ⟶ B) (hfg : h ≫ f = k ≫ g) :
    (Dom.pullbackObject f g = Dom.pullbackObject f g)
      ∧ (Dom.pullbackLift f g h k hfg ≫ Dom.pullbackFst f g = h) :=
  ⟨rfl, Dom.pullbackLift_fst f g h k hfg⟩

/-! ### The pullback of Lemma A.4 -/

example : ∀ {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
    [HasRanges C] {X Y Z : C} (f : X ⟶ Y) {q : Z ⟶ Y}
    (hq : PCategoryStruct.rst q = 𝟙 Z) (hρ : q ≫ HasRanges.ran f = q),
    Dom.IsPullbackSquare hq hρ
      (Dom.pullbackFst (Dom.sharp f) (Dom.sharpTotal (f := f) q hq hρ))
      (Dom.pullbackSnd (Dom.sharp f) (Dom.sharpTotal (f := f) q hq hρ)) :=
  @Dom.rangeLiftPullback_isPullbackSquare

example : ∀ {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
    [HasRanges C] {X Y Z : C} (f : X ⟶ Y) {q : Z ⟶ Y}
    (hq : PCategoryStruct.rst q = 𝟙 Z) (hρ : q ≫ HasRanges.ran f = q),
    (∃ p : Z ⟶ X, PCategoryStruct.rst p = 𝟙 Z ∧ p ≫ f = q) ↔
      ∃ s : Dom.total Z ⟶
          Dom.pullbackObject (Dom.sharp f) (Dom.sharpTotal (f := f) q hq hρ),
        s ≫ Dom.pullbackSnd (Dom.sharp f) (Dom.sharpTotal (f := f) q hq hρ)
          = 𝟙 (Dom.total Z) :=
  @Dom.exists_total_lift_iff_rangeLiftPullback_section

example {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
    [HasRanges C] {X Y Z : C} (f : X ⟶ Y) {q : Z ⟶ Y}
    (hq : PCategoryStruct.rst q = 𝟙 Z) (hρ : q ≫ HasRanges.ran f = q)
    {W : Dom C} (a : W ⟶ Dom.src f) (b : W ⟶ Dom.total Z)
    (hab : a ≫ Dom.sharp f = b ≫ Dom.sharpTotal (f := f) q hq hρ) :
    (Dom.pullbackFst (Dom.sharp f) (Dom.sharpTotal (f := f) q hq hρ)
        ≫ Dom.sharp f
      = Dom.pullbackSnd (Dom.sharp f) (Dom.sharpTotal (f := f) q hq hρ)
        ≫ Dom.sharpTotal (f := f) q hq hρ)
    ∧ ∃! s : W ⟶
        Dom.pullbackObject (Dom.sharp f) (Dom.sharpTotal (f := f) q hq hρ),
        s ≫ Dom.pullbackFst (Dom.sharp f)
              (Dom.sharpTotal (f := f) q hq hρ) = a ∧
        s ≫ Dom.pullbackSnd (Dom.sharp f)
              (Dom.sharpTotal (f := f) q hq hρ) = b :=
  ⟨(Dom.rangeLiftPullback_isPullbackSquare f hq hρ).comm,
    (Dom.rangeLiftPullback_isPullbackSquare f hq hρ).universal a b hab⟩

example {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
    [HasRanges C] {X Y Z : C} (f : X ⟶ Y) {q : Z ⟶ Y}
    (hq : PCategoryStruct.rst q = 𝟙 Z) (hρ : q ≫ HasRanges.ran f = q) :
    (∃ p : Z ⟶ X, PCategoryStruct.rst p = 𝟙 Z ∧ p ≫ f = q) ↔
      ∃ s : Dom.total Z ⟶
          Dom.pullbackObject (Dom.sharp f) (Dom.sharpTotal (f := f) q hq hρ),
        s ≫ Dom.pullbackSnd (Dom.sharp f) (Dom.sharpTotal (f := f) q hq hρ)
          = 𝟙 (Dom.total Z) :=
  Dom.exists_total_lift_iff_rangeLiftPullback_section f hq hρ

example {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
    [HasRanges C] {X Y Z : C} (f : X ⟶ Y) {q : Z ⟶ Y}
    (hq : PCategoryStruct.rst q = 𝟙 Z) (hρ : q ≫ HasRanges.ran f = q) :
    (∃ p : Z ⟶ X, PCategoryStruct.rst p = 𝟙 Z ∧ p ≫ f = q) →
      ∃ s : Dom.total Z ⟶
          Dom.pullbackObject (Dom.sharp f) (Dom.sharpTotal (f := f) q hq hρ),
        s ≫ Dom.pullbackSnd (Dom.sharp f) (Dom.sharpTotal (f := f) q hq hρ)
          = 𝟙 (Dom.total Z) :=
  (Dom.exists_total_lift_iff_rangeLiftPullback_section f hq hρ).mp

example {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
    [HasRanges C] {X Y Z : C} (f : X ⟶ Y) {q : Z ⟶ Y}
    (hq : PCategoryStruct.rst q = 𝟙 Z) (hρ : q ≫ HasRanges.ran f = q) :
    (∃ s : Dom.total Z ⟶
        Dom.pullbackObject (Dom.sharp f) (Dom.sharpTotal (f := f) q hq hρ),
      s ≫ Dom.pullbackSnd (Dom.sharp f) (Dom.sharpTotal (f := f) q hq hρ)
        = 𝟙 (Dom.total Z)) →
      ∃ p : Z ⟶ X, PCategoryStruct.rst p = 𝟙 Z ∧ p ≫ f = q :=
  (Dom.exists_total_lift_iff_rangeLiftPullback_section f hq hρ).mpr

end CategoryTheory
