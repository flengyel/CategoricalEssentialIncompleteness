/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import PCats.DomEqualizers

/-!
# Pullbacks in `Dom C`

For a cospan `f : A ⟶ D`, `g : B ⟶ D` in `Dom C`, `pullbackObject f g` is the
equalizer of the two composites

    binaryProductFst A B ≫ f    and    binaryProductSnd A B ≫ g

out of `binaryProduct A B`, and the legs `pullbackFst` and `pullbackSnd` are
the equalizer inclusion followed by the two product projections.

The mediating morphism `pullbackLift` is the equalizer lift of
`binaryProductLift h k`, and `binaryProductLift_unique` with
`equalizerLift_unique` prove `pullbackLift_unique`, hence
`pullback_existsUnique`. The universal property is stated directly; no Mathlib
limit instance is declared.

`Dom.exists_pullback_of_mem_subdomainMorphisms` of
`PCats.DomSubdomainMorphisms` is a separate result: it requires no ranges and
applies when one leg of the cospan lies in `Dom.subdomainMorphisms`.

The construction assumes `Category`, `PCategoryStruct`, `PCategory`, and
`HasRanges`. `IsRP`, choice, zero morphisms, prodominical structure, isotypes,
and recursion data are not used.
-/

universe v u

namespace CategoryTheory

open PCategoryStruct

variable {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
  [HasRanges C]

namespace Dom

/-! ### The pullback object and its legs -/

/-- The pullback of a cospan, as the equalizer of the two composites out of the
binary product. -/
def pullbackObject {A B D : Dom C} (f : A ⟶ D) (g : B ⟶ D) : Dom C :=
  equalizerObject
    (binaryProductFst A B ≫ f)
    (binaryProductSnd A B ≫ g)

/-- The first leg: the equalizer inclusion followed by the first projection. -/
def pullbackFst {A B D : Dom C} (f : A ⟶ D) (g : B ⟶ D) :
    pullbackObject f g ⟶ A :=
  equalizerInclusion
      (binaryProductFst A B ≫ f)
      (binaryProductSnd A B ≫ g) ≫
    binaryProductFst A B

/-- The second leg: the equalizer inclusion followed by the second
projection. -/
def pullbackSnd {A B D : Dom C} (f : A ⟶ D) (g : B ⟶ D) :
    pullbackObject f g ⟶ B :=
  equalizerInclusion
      (binaryProductFst A B ≫ f)
      (binaryProductSnd A B ≫ g) ≫
    binaryProductSnd A B

/-- The pullback square commutes. -/
theorem pullback_comm {A B D : Dom C} (f : A ⟶ D) (g : B ⟶ D) :
    pullbackFst f g ≫ f = pullbackSnd f g ≫ g :=
  have e1 : pullbackFst f g ≫ f
      = equalizerInclusion (binaryProductFst A B ≫ f)
          (binaryProductSnd A B ≫ g) ≫ (binaryProductFst A B ≫ f) :=
    Category.assoc _ _ _
  have e2 : pullbackSnd f g ≫ g
      = equalizerInclusion (binaryProductFst A B ≫ f)
          (binaryProductSnd A B ≫ g) ≫ (binaryProductSnd A B ≫ g) :=
    Category.assoc _ _ _
  e1.trans ((equalizer_comm _ _).trans e2.symm)

/-! ### The lift -/

omit [HasRanges C] in
/-- A commuting cone pairs to a morphism equalizing the two composites. -/
private lemma binaryProductLift_comm {A B D W : Dom C} {f : A ⟶ D} {g : B ⟶ D}
    {h : W ⟶ A} {k : W ⟶ B} (hfg : h ≫ f = k ≫ g) :
    binaryProductLift h k ≫ (binaryProductFst A B ≫ f)
      = binaryProductLift h k ≫ (binaryProductSnd A B ≫ g) := by
  rw [← Category.assoc, ← Category.assoc, binaryProductLift_fst,
    binaryProductLift_snd, hfg]

/-- The mediating morphism into the pullback. -/
def pullbackLift {A B D W : Dom C} (f : A ⟶ D) (g : B ⟶ D)
    (h : W ⟶ A) (k : W ⟶ B) (hfg : h ≫ f = k ≫ g) :
    W ⟶ pullbackObject f g :=
  equalizerLift
    (binaryProductFst A B ≫ f)
    (binaryProductSnd A B ≫ g)
    (binaryProductLift h k)
    (binaryProductLift_comm hfg)

theorem pullbackLift_fst {A B D W : Dom C} (f : A ⟶ D) (g : B ⟶ D)
    (h : W ⟶ A) (k : W ⟶ B) (hfg : h ≫ f = k ≫ g) :
    pullbackLift f g h k hfg ≫ pullbackFst f g = h :=
  have e1 : pullbackLift f g h k hfg ≫ pullbackFst f g
      = (pullbackLift f g h k hfg
          ≫ equalizerInclusion (binaryProductFst A B ≫ f)
              (binaryProductSnd A B ≫ g)) ≫ binaryProductFst A B :=
    (Category.assoc _ _ _).symm
  have e2 : (pullbackLift f g h k hfg
        ≫ equalizerInclusion (binaryProductFst A B ≫ f)
            (binaryProductSnd A B ≫ g)) ≫ binaryProductFst A B
      = binaryProductLift h k ≫ binaryProductFst A B :=
    congrArg (fun t => t ≫ binaryProductFst A B)
      (equalizerLift_inclusion _ _ _ (binaryProductLift_comm hfg))
  e1.trans (e2.trans (binaryProductLift_fst h k))

theorem pullbackLift_snd {A B D W : Dom C} (f : A ⟶ D) (g : B ⟶ D)
    (h : W ⟶ A) (k : W ⟶ B) (hfg : h ≫ f = k ≫ g) :
    pullbackLift f g h k hfg ≫ pullbackSnd f g = k :=
  have e1 : pullbackLift f g h k hfg ≫ pullbackSnd f g
      = (pullbackLift f g h k hfg
          ≫ equalizerInclusion (binaryProductFst A B ≫ f)
              (binaryProductSnd A B ≫ g)) ≫ binaryProductSnd A B :=
    (Category.assoc _ _ _).symm
  have e2 : (pullbackLift f g h k hfg
        ≫ equalizerInclusion (binaryProductFst A B ≫ f)
            (binaryProductSnd A B ≫ g)) ≫ binaryProductSnd A B
      = binaryProductLift h k ≫ binaryProductSnd A B :=
    congrArg (fun t => t ≫ binaryProductSnd A B)
      (equalizerLift_inclusion _ _ _ (binaryProductLift_comm hfg))
  e1.trans (e2.trans (binaryProductLift_snd h k))

/-! ### Uniqueness and the universal property -/

theorem pullbackLift_unique {A B D W : Dom C} (f : A ⟶ D) (g : B ⟶ D)
    (h : W ⟶ A) (k : W ⟶ B) (hfg : h ≫ f = k ≫ g)
    (l : W ⟶ pullbackObject f g)
    (hl : l ≫ pullbackFst f g = h)
    (hk : l ≫ pullbackSnd f g = k) :
    l = pullbackLift f g h k hfg :=
  have h1 : (l ≫ equalizerInclusion (binaryProductFst A B ≫ f)
        (binaryProductSnd A B ≫ g)) ≫ binaryProductFst A B = h :=
    (Category.assoc _ _ _).trans hl
  have h2 : (l ≫ equalizerInclusion (binaryProductFst A B ≫ f)
        (binaryProductSnd A B ≫ g)) ≫ binaryProductSnd A B = k :=
    (Category.assoc _ _ _).trans hk
  equalizerLift_unique _ _ _ (binaryProductLift_comm hfg) l
    (binaryProductLift_unique _ h1 h2)

/-- The pullback universal property, stated directly. -/
theorem pullback_existsUnique {A B D W : Dom C} (f : A ⟶ D) (g : B ⟶ D)
    (h : W ⟶ A) (k : W ⟶ B) (hfg : h ≫ f = k ≫ g) :
    ∃! l : W ⟶ pullbackObject f g,
      l ≫ pullbackFst f g = h ∧ l ≫ pullbackSnd f g = k :=
  ⟨pullbackLift f g h k hfg,
    ⟨pullbackLift_fst f g h k hfg, pullbackLift_snd f g h k hfg⟩,
    fun _ hlk => pullbackLift_unique f g h k hfg _ hlk.1 hlk.2⟩

/-! ### The pullback of Lemma A.4

`Dom.exists_total_lift_iff_exists_section` of `PCats.Domains` is stated
relative to a supplied `Dom.IsPullbackSquare`. The pullback of `Dom.sharp f`
and `Dom.sharpTotal q` is such a square, so the equivalence specializes to it.
-/

/-- The explicit pullback of `f♯` and `q♯` satisfies `Dom.IsPullbackSquare`. -/
theorem rangeLiftPullback_isPullbackSquare {X Y Z : C} (f : X ⟶ Y)
    {q : Z ⟶ Y} (hq : rst q = 𝟙 Z) (hρ : q ≫ HasRanges.ran f = q) :
    IsPullbackSquare hq hρ
      (pullbackFst (sharp f) (sharpTotal (f := f) q hq hρ))
      (pullbackSnd (sharp f) (sharpTotal (f := f) q hq hρ)) where
  comm := pullback_comm _ _
  universal a b hab := pullback_existsUnique _ _ a b hab

/-- Lemma A.4 specialized to the pullback of `f♯` and `q♯`. -/
theorem exists_total_lift_iff_rangeLiftPullback_section {X Y Z : C}
    (f : X ⟶ Y) {q : Z ⟶ Y} (hq : rst q = 𝟙 Z)
    (hρ : q ≫ HasRanges.ran f = q) :
    (∃ p : Z ⟶ X, rst p = 𝟙 Z ∧ p ≫ f = q) ↔
      ∃ s : total Z ⟶
          pullbackObject (sharp f) (sharpTotal (f := f) q hq hρ),
        s ≫ pullbackSnd (sharp f) (sharpTotal (f := f) q hq hρ)
          = 𝟙 (total Z) :=
  exists_total_lift_iff_exists_section f hq hρ
    (rangeLiftPullback_isPullbackSquare f hq hρ)

end Dom

end CategoryTheory
