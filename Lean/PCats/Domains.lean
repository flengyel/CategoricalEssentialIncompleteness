/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import PCats.Ranges

/-!
# The category of domains

Appendix A, subsection "The category of domains". Rosolini's `Dom(C)`, written
`𝖣𝗈𝗆(C)` in the appendix and `Dom C` here.

Objects are restriction idempotents `d : X ⟶ X`. A morphism `u : d ⟶ e`, where
`d : X ⟶ X` and `e : Y ⟶ Y`, is a morphism `u : X ⟶ Y` of `C` with `rst u = d`
and `e u = u`: defined on all of the source domain, landing in the target
domain.

The category structure needs no hypotheses beyond `PCategory`. The identity of
`d` is `d` itself, by idempotence; composition is inherited, closure under
`rst` being R3 in the form `rst (gf) = rst (rst g f)`. The relative form of
Lemma A.4 is proved here; `PCats.DomPullbacks` specializes it to the explicit
pullback.
-/

@[expose] public section

universe v u

namespace CategoryTheory

open PCategoryStruct

variable {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]

/-- An object of `Dom C`: a restriction idempotent on some object of `C`. -/
structure Dom (C : Type u) [Category.{v} C] [PCategoryStruct C]
    [PCategory C] where
  /-- The underlying object of `C`. -/
  base : C
  /-- The idempotent. -/
  idem : base ⟶ base
  /-- It is a restriction idempotent. -/
  rst_idem : rst idem = idem

namespace Dom

lemma idem_comp_idem (d : Dom C) : d.idem ≫ d.idem = d.idem := by
  have h : rst d.idem ≫ rst d.idem = rst d.idem :=
    RestrictionCategory.rst_idem d.idem
  rwa [d.rst_idem] at h

/-- A morphism `u : d ⟶ e` is a morphism of `C` defined on all of `d` and
landing in `e`. -/
structure Hom (d e : Dom C) where
  /-- The underlying morphism of `C`. -/
  hom : d.base ⟶ e.base
  /-- `u` is defined on all of the source domain. -/
  rst_hom : rst hom = d.idem
  /-- `u` lands in the target domain. -/
  comp_idem : hom ≫ e.idem = hom

lemma Hom.ext' {d e : Dom C} : ∀ {u v : Hom d e}, u.hom = v.hom → u = v
  | ⟨_, _, _⟩, ⟨_, _, _⟩, rfl => rfl

instance : Category.{v} (Dom C) where
  Hom d e := Hom d e
  id d := ⟨d.idem, d.rst_idem, d.idem_comp_idem⟩
  comp {d _ g} u v :=
    ⟨u.hom ≫ v.hom,
     by rw [PCategory.rst_comp_rst_right', v.rst_hom, u.comp_idem, u.rst_hom],
     by rw [Category.assoc, v.comp_idem]⟩
  id_comp {d _} u := Hom.ext' (show d.idem ≫ u.hom = u.hom by
    have h : rst u.hom ≫ u.hom = u.hom := RestrictionCategory.rst_comp_self u.hom
    rwa [u.rst_hom] at h)
  comp_id u := Hom.ext' u.comp_idem
  assoc _ _ _ := Hom.ext' (Category.assoc _ _ _)

@[simp] lemma id_hom (d : Dom C) : (𝟙 d : Hom d d).hom = d.idem := rfl

@[simp] lemma comp_hom {d e g : Dom C} (u : d ⟶ e) (v : e ⟶ g) :
    (u ≫ v).hom = u.hom ≫ v.hom := rfl

/-- The total object `X`, represented by the identity domain `1_X`. -/
def total (X : C) : Dom C := ⟨X, 𝟙 X, PCategory.rst_id X⟩

@[simp] lemma total_base (X : C) : (total X).base = X := rfl

@[simp] lemma total_idem (X : C) : (total X : Dom C).idem = 𝟙 X := rfl

/-- A total morphism of `C` landing in `d` is a morphism `1_Z ⟶ d`. -/
def homOfTotal {Z : C} {d : Dom C} (p : Z ⟶ d.base) (hp : rst p = 𝟙 Z)
    (hd : p ≫ d.idem = p) : total Z ⟶ d :=
  ⟨p, hp, hd⟩

@[simp] lemma homOfTotal_hom {Z : C} {d : Dom C} (p : Z ⟶ d.base)
    (hp : rst p = 𝟙 Z) (hd : p ≫ d.idem = p) :
    (homOfTotal p hp hd).hom = p := rfl

/-- Every morphism out of a total object is total in `C`. -/
lemma rst_hom_of_total {Z : C} {d : Dom C} (u : total Z ⟶ d) :
    rst u.hom = 𝟙 Z := u.rst_hom

/-! ### The sharp constructions -/

section Ranges

variable [HasRanges C]

/-- The domain object `rst f`. -/
def src {X Y : C} (f : X ⟶ Y) : Dom C := ⟨X, rst f, PCategory.rst_rst f⟩

/-- The domain object `ran f`. -/
def tgt {X Y : C} (f : X ⟶ Y) : Dom C := ⟨Y, HasRanges.ran f, HasRanges.rst_ran f⟩

/-- Appendix A: the arrow `f` represents `f♯ : rst f ⟶ ran f`. -/
def sharp {X Y : C} (f : X ⟶ Y) : src f ⟶ tgt f :=
  ⟨f, rfl, HasRanges.comp_ran f⟩

@[simp] lemma sharp_hom {X Y : C} (f : X ⟶ Y) : (sharp f).hom = f := rfl

/-- Appendix A: a total `q` received by `ran f` represents `q♯ : 1_Z ⟶ ran f`. -/
def sharpTotal {X Y Z : C} {f : X ⟶ Y} (q : Z ⟶ Y) (hq : rst q = 𝟙 Z)
    (hρ : q ≫ HasRanges.ran f = q) : total Z ⟶ tgt f :=
  ⟨q, hq, hρ⟩

@[simp] lemma sharpTotal_hom {X Y Z : C} {f : X ⟶ Y} (q : Z ⟶ Y)
    (hq : rst q = 𝟙 Z) (hρ : q ≫ HasRanges.ran f = q) :
    (sharpTotal (f := f) q hq hρ).hom = q := rfl

omit [HasRanges C] in
/-- The computation behind the converse half of Lemma A.4: a total `p` with
`f p = q` is received by `rst f`, hence represents `p♯ : 1_Z ⟶ rst f`. -/
lemma comp_rst_self {X Y Z : C} (f : X ⟶ Y) (p : Z ⟶ X) {q : Z ⟶ Y}
    (hq : rst q = 𝟙 Z) (hfp : p ≫ f = q) : p ≫ rst f = p := by
  have h := PCategory.rst_comp' p f
  rw [hfp, hq, Category.id_comp] at h
  exact h.symm

/-- A total `p : Z ⟶ X` with `f p = q` and `q` total represents `1_Z ⟶ rst f`. -/
def sharpOfTotalLift {X Y Z : C} (f : X ⟶ Y) (p : Z ⟶ X) {q : Z ⟶ Y}
    (hp : rst p = 𝟙 Z) (hq : rst q = 𝟙 Z) (hfp : p ≫ f = q) :
    total Z ⟶ src f :=
  ⟨p, hp, comp_rst_self f p hq hfp⟩

omit [HasRanges C] in
@[simp] lemma sharpOfTotalLift_hom {X Y Z : C} (f : X ⟶ Y) (p : Z ⟶ X)
    {q : Z ⟶ Y} (hp : rst p = 𝟙 Z) (hq : rst q = 𝟙 Z) (hfp : p ≫ f = q) :
    (sharpOfTotalLift f p hp hq hfp).hom = p := rfl

/-- `p♯ f♯ = q♯` when `f p = q`. -/
lemma sharpOfTotalLift_comp_sharp {X Y Z : C} (f : X ⟶ Y) (p : Z ⟶ X)
    {q : Z ⟶ Y} (hp : rst p = 𝟙 Z) (hq : rst q = 𝟙 Z) (hfp : p ≫ f = q)
    (hρ : q ≫ HasRanges.ran f = q) :
    sharpOfTotalLift f p hp hq hfp ≫ sharp f = sharpTotal (f := f) q hq hρ :=
  Hom.ext' hfp

/-! ### Lemma A.4

The theorem is stated relative to a supplied pullback square and uses only its
universal property. The universal property is written out directly rather than
through Mathlib's limits interface.

`PCats.DomPullbacks` constructs such a square and specializes the equivalence
in `Dom.exists_total_lift_iff_rangeLiftPullback_section`.

Note that "section" in Lemma A.4 means a right inverse of `π_Z`, which is not
the `P`-categorical `IsSection` of `PCats.Ranges`. -/

/-- The square with legs `π₁, π₂` over the cospan `f♯, q♯` is a pullback. -/
structure IsPullbackSquare {X Y Z : C} {f : X ⟶ Y} {q : Z ⟶ Y}
    (hq : rst q = 𝟙 Z) (hρ : q ≫ HasRanges.ran f = q)
    {E : Dom C} (π₁ : E ⟶ src f) (π₂ : E ⟶ total Z) : Prop where
  /-- The square commutes. -/
  comm : π₁ ≫ sharp f = π₂ ≫ sharpTotal (f := f) q hq hρ
  /-- Every competing cone factors uniquely. -/
  universal : ∀ {W : Dom C} (a : W ⟶ src f) (b : W ⟶ total Z),
    a ≫ sharp f = b ≫ sharpTotal (f := f) q hq hρ →
    ∃! s : W ⟶ E, s ≫ π₁ = a ∧ s ≫ π₂ = b

/-- Lemma A.4: a total lift of `q` along `f` in `C` exists exactly when the
projection `π_Z` of the pullback has a section in `Dom C`. -/
theorem exists_total_lift_iff_exists_section {X Y Z : C} (f : X ⟶ Y)
    {q : Z ⟶ Y} (hq : rst q = 𝟙 Z) (hρ : q ≫ HasRanges.ran f = q)
    {E : Dom C} {π₁ : E ⟶ src f} {π₂ : E ⟶ total Z}
    (hE : IsPullbackSquare hq hρ π₁ π₂) :
    (∃ p : Z ⟶ X, rst p = 𝟙 Z ∧ p ≫ f = q)
      ↔ (∃ s : total Z ⟶ E, s ≫ π₂ = 𝟙 (total Z)) := by
  constructor
  · rintro ⟨p, hp, hfp⟩
    obtain ⟨s, ⟨_, hs2⟩, _⟩ :=
      hE.universal (sharpOfTotalLift f p hp hq hfp) (𝟙 (total Z))
        (by rw [sharpOfTotalLift_comp_sharp f p hp hq hfp hρ, Category.id_comp])
    exact ⟨s, hs2⟩
  · rintro ⟨s, hs⟩
    refine ⟨(s ≫ π₁).hom, (s ≫ π₁).rst_hom, ?_⟩
    have h : (s ≫ π₁) ≫ sharp f = sharpTotal (f := f) q hq hρ := by
      rw [Category.assoc, hE.comm, ← Category.assoc, hs, Category.id_comp]
    exact congrArg Hom.hom h

end Ranges

end Dom

end CategoryTheory
