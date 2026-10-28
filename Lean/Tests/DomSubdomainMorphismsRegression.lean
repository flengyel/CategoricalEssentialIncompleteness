/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import PCats.DomSubdomainMorphisms

/-!
# Signature guards for the family of subdomain morphisms

Each `example` fails to elaborate if a protected signature or equation changes.
Exact `@`-ascriptions pin the telescopes of `Dom.Subdomain.top`,
`Dom.subdomainMorphisms`, `Dom.subdomainMorphisms_iff`,
`Dom.Subdomain.inclusion_mem_subdomainMorphisms`,
`Dom.id_mem_subdomainMorphisms`, `Dom.mono_of_mem_subdomainMorphisms`,
`Dom.subdomainMorphisms_precomp_iso`, `Dom.subdomainMorphisms_precomp_iso_iff`,
`Dom.Subdomain.inverseImageIso` with its two underlying-map formulas and
`Dom.Subdomain.inverseImageIso_hom_inclusion`, `Dom.subdomainMorphisms_comp`,
`Dom.instIsMultiplicativeSubdomainMorphisms`, and
`Dom.exists_pullback_of_mem_subdomainMorphisms`; applied examples guard the
defining equations of `top`, the membership formula together with the
orientation `i.hom ≫ s.inclusion = m`, the monicity and source-isomorphism
consequences, both inverse laws of the comparison isomorphism, the
representative of a composite, the identity and composition operations of the
`IsMultiplicative` instance, and the pullback witnesses together with the
square, both factorization equations, uniqueness, and monicity of the
base-changed leg.

Each guard writes out the whole telescope, so it fails to elaborate if a range,
zero-morphism, choice, dominical, prodominical, isotype, recursion, or limits
premise enters a protected declaration. Classical axiom dependencies are not
visible to these guards and are checked separately by `check_axioms.lean`.

`autoImplicit` is off: `lake env lean` does not apply the package's
`leanOptions`, and an unbound identifier would otherwise be auto-bound and the
guard would hold vacuously.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe v u

namespace CategoryTheory

#check @Dom.Subdomain.top
#check @Dom.subdomainMorphisms
#check @Dom.subdomainMorphisms_iff
#check @Dom.Subdomain.inclusion_mem_subdomainMorphisms
#check @Dom.id_mem_subdomainMorphisms
#check @Dom.mono_of_mem_subdomainMorphisms
#check @Dom.subdomainMorphisms_precomp_iso
#check @Dom.subdomainMorphisms_precomp_iso_iff
#check @Dom.Subdomain.inverseImageIso
#check @Dom.Subdomain.inverseImageIso_hom_hom
#check @Dom.Subdomain.inverseImageIso_inv_hom
#check @Dom.Subdomain.inverseImageIso_hom_inclusion
#check @Dom.subdomainMorphisms_comp
#check @Dom.instIsMultiplicativeSubdomainMorphisms

/-! ### The identity subdomain -/

example : ∀ {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
    (A : Dom C), Dom.Subdomain A :=
  @Dom.Subdomain.top

example {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
    (A : Dom C) : (Dom.Subdomain.top A).idem = A.idem :=
  Dom.Subdomain.top_idem A

example {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
    (A : Dom C) : (Dom.Subdomain.top A).idem = A.idem :=
  rfl

example {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
    (A : Dom C) : (Dom.Subdomain.top A).toDom = A :=
  Dom.Subdomain.top_toDom A

example {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
    (A : Dom C) : (Dom.Subdomain.top A).toDom = A :=
  rfl

example {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
    (A : Dom C) : (Dom.Subdomain.top A).inclusion = 𝟙 A :=
  Dom.Subdomain.top_inclusion A

example {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
    (A : Dom C) : (Dom.Subdomain.top A).inclusion = 𝟙 A :=
  rfl

/-! ### The membership formula -/

example : ∀ {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C],
    MorphismProperty (Dom C) :=
  @Dom.subdomainMorphisms

example : ∀ {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
    {X A : Dom C} (m : X ⟶ A),
    Dom.subdomainMorphisms m ↔
      ∃ (s : Dom.Subdomain A) (i : X ≅ s.toDom),
        i.hom ≫ s.inclusion = m :=
  @Dom.subdomainMorphisms_iff

example {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
    {X A : Dom C} (m : X ⟶ A) :
    Dom.subdomainMorphisms m ↔
      ∃ (s : Dom.Subdomain A) (i : X ≅ s.toDom),
        i.hom ≫ s.inclusion = m :=
  Iff.rfl

example {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
    {X A : Dom C} (m : X ⟶ A) (hm : Dom.subdomainMorphisms m) :
    ∃ (s : Dom.Subdomain A) (i : X ≅ s.toDom),
      i.hom ≫ s.inclusion = m :=
  (Dom.subdomainMorphisms_iff m).mp hm

example {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
    {X A : Dom C} (m : X ⟶ A) (s : Dom.Subdomain A) (i : X ≅ s.toDom)
    (h : i.hom ≫ s.inclusion = m) : Dom.subdomainMorphisms m :=
  (Dom.subdomainMorphisms_iff m).mpr ⟨s, i, h⟩

/-! ### Canonical inclusions and identities belong -/

example : ∀ {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
    {A : Dom C} (s : Dom.Subdomain A),
    Dom.subdomainMorphisms s.inclusion :=
  @Dom.Subdomain.inclusion_mem_subdomainMorphisms

example {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
    {A : Dom C} (s : Dom.Subdomain A) :
    Dom.subdomainMorphisms s.inclusion :=
  Dom.Subdomain.inclusion_mem_subdomainMorphisms s

example : ∀ {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
    (A : Dom C), Dom.subdomainMorphisms (𝟙 A) :=
  @Dom.id_mem_subdomainMorphisms

example {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
    (A : Dom C) : Dom.subdomainMorphisms (𝟙 A) :=
  Dom.id_mem_subdomainMorphisms A

/-! ### Every member is monic -/

example : ∀ {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
    {X A : Dom C} {m : X ⟶ A}, Dom.subdomainMorphisms m → Mono m :=
  @Dom.mono_of_mem_subdomainMorphisms

example {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
    {X A : Dom C} {m : X ⟶ A} (hm : Dom.subdomainMorphisms m) : Mono m :=
  Dom.mono_of_mem_subdomainMorphisms hm

example {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
    {X A : Dom C} {m : X ⟶ A} (hm : Dom.subdomainMorphisms m) {W : Dom C}
    (f g : W ⟶ X) (h : f ≫ m = g ≫ m) : f = g :=
  (Dom.mono_of_mem_subdomainMorphisms hm).right_cancellation f g h

/-! ### Invariance under a source isomorphism -/

example : ∀ {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
    {X Y A : Dom C} (i : X ≅ Y) {m : Y ⟶ A}, Dom.subdomainMorphisms m →
    Dom.subdomainMorphisms (i.hom ≫ m) :=
  @Dom.subdomainMorphisms_precomp_iso

example {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
    {X Y A : Dom C} (i : X ≅ Y) {m : Y ⟶ A}
    (hm : Dom.subdomainMorphisms m) :
    Dom.subdomainMorphisms (i.hom ≫ m) :=
  Dom.subdomainMorphisms_precomp_iso i hm

example : ∀ {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
    {X Y A : Dom C} (i : X ≅ Y) (m : Y ⟶ A),
    Dom.subdomainMorphisms (i.hom ≫ m) ↔ Dom.subdomainMorphisms m :=
  @Dom.subdomainMorphisms_precomp_iso_iff

example {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
    {X Y A : Dom C} (i : X ≅ Y) (m : Y ⟶ A)
    (hm : Dom.subdomainMorphisms (i.hom ≫ m)) : Dom.subdomainMorphisms m :=
  (Dom.subdomainMorphisms_precomp_iso_iff i m).mp hm

example {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
    {X Y A : Dom C} (i : X ≅ Y) (m : Y ⟶ A)
    (hm : Dom.subdomainMorphisms m) :
    Dom.subdomainMorphisms (i.hom ≫ m) :=
  (Dom.subdomainMorphisms_precomp_iso_iff i m).mpr hm

/-! ### The comparison isomorphism -/

example : ∀ {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
    {A B : Dom C} (s : Dom.Subdomain A) (i : A ≅ B),
    s.toDom ≅ (s.inverseImage i.inv).toDom :=
  @Dom.Subdomain.inverseImageIso

example {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
    {A B : Dom C} (s : Dom.Subdomain A) (i : A ≅ B) :
    s.toDom ≅ (s.inverseImage i.inv).toDom :=
  s.inverseImageIso i

example : ∀ {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
    {A B : Dom C} (s : Dom.Subdomain A) (i : A ≅ B),
    (s.inverseImageIso i).hom.hom = s.idem ≫ i.hom.hom :=
  @Dom.Subdomain.inverseImageIso_hom_hom

example {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
    {A B : Dom C} (s : Dom.Subdomain A) (i : A ≅ B) :
    (s.inverseImageIso i).hom.hom = s.idem ≫ i.hom.hom :=
  Dom.Subdomain.inverseImageIso_hom_hom s i

example {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
    {A B : Dom C} (s : Dom.Subdomain A) (i : A ≅ B) :
    (s.inverseImageIso i).hom.hom = s.idem ≫ i.hom.hom :=
  rfl

example : ∀ {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
    {A B : Dom C} (s : Dom.Subdomain A) (i : A ≅ B),
    (s.inverseImageIso i).inv.hom = i.inv.hom ≫ s.idem :=
  @Dom.Subdomain.inverseImageIso_inv_hom

example {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
    {A B : Dom C} (s : Dom.Subdomain A) (i : A ≅ B) :
    (s.inverseImageIso i).inv.hom = i.inv.hom ≫ s.idem :=
  Dom.Subdomain.inverseImageIso_inv_hom s i

example {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
    {A B : Dom C} (s : Dom.Subdomain A) (i : A ≅ B) :
    (s.inverseImageIso i).inv.hom = i.inv.hom ≫ s.idem :=
  rfl

example : ∀ {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
    {A B : Dom C} (s : Dom.Subdomain A) (i : A ≅ B),
    (s.inverseImageIso i).hom ≫ (s.inverseImage i.inv).inclusion
      = s.inclusion ≫ i.hom :=
  @Dom.Subdomain.inverseImageIso_hom_inclusion

example {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
    {A B : Dom C} (s : Dom.Subdomain A) (i : A ≅ B) :
    (s.inverseImageIso i).hom ≫ (s.inverseImage i.inv).inclusion
      = s.inclusion ≫ i.hom :=
  Dom.Subdomain.inverseImageIso_hom_inclusion s i

example {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
    {A B : Dom C} (s : Dom.Subdomain A) (i : A ≅ B) :
    (s.inverseImageIso i).hom ≫ (s.inverseImageIso i).inv = 𝟙 s.toDom :=
  (s.inverseImageIso i).hom_inv_id

example {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
    {A B : Dom C} (s : Dom.Subdomain A) (i : A ≅ B) :
    (s.inverseImageIso i).inv ≫ (s.inverseImageIso i).hom
      = 𝟙 (s.inverseImage i.inv).toDom :=
  (s.inverseImageIso i).inv_hom_id

/-! ### Closure under composition -/

example : ∀ {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
    {X Y A : Dom C} {m : X ⟶ Y} {n : Y ⟶ A},
    Dom.subdomainMorphisms m → Dom.subdomainMorphisms n →
    Dom.subdomainMorphisms (m ≫ n) :=
  @Dom.subdomainMorphisms_comp

example {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
    {X Y A : Dom C} {m : X ⟶ Y} {n : Y ⟶ A}
    (hm : Dom.subdomainMorphisms m) (hn : Dom.subdomainMorphisms n) :
    Dom.subdomainMorphisms (m ≫ n) :=
  Dom.subdomainMorphisms_comp hm hn

example {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
    {X Y A : Dom C} {m : X ⟶ Y} {n : Y ⟶ A}
    (hm : Dom.subdomainMorphisms m) (hn : Dom.subdomainMorphisms n) :
    ∃ (s : Dom.Subdomain A) (i : X ≅ s.toDom),
      i.hom ≫ s.inclusion = m ≫ n :=
  (Dom.subdomainMorphisms_iff (m ≫ n)).mp
    (Dom.subdomainMorphisms_comp hm hn)

/-! ### Identity and composition closure as a `MorphismProperty` -/

example : ∀ {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C],
    (Dom.subdomainMorphisms (C := C)).IsMultiplicative :=
  @Dom.instIsMultiplicativeSubdomainMorphisms

example {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C] :
    (Dom.subdomainMorphisms (C := C)).IsMultiplicative :=
  inferInstance

example {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
    (A : Dom C) : Dom.subdomainMorphisms (𝟙 A) :=
  MorphismProperty.id_mem Dom.subdomainMorphisms A

example {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
    {X Y A : Dom C} (m : X ⟶ Y) (n : Y ⟶ A)
    (hm : Dom.subdomainMorphisms m) (hn : Dom.subdomainMorphisms n) :
    Dom.subdomainMorphisms (m ≫ n) :=
  MorphismProperty.comp_mem Dom.subdomainMorphisms m n hm hn

/-! ### Pullback representatives -/

#check @Dom.exists_pullback_of_mem_subdomainMorphisms

example : ∀ {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
    {X A B : Dom C} {m : X ⟶ B},
    Dom.subdomainMorphisms m → ∀ (θ : A ⟶ B),
    ∃ (P : Dom C) (p : P ⟶ X) (q : P ⟶ A),
      Dom.subdomainMorphisms q ∧
      p ≫ m = q ≫ θ ∧
      ∀ {W : Dom C} (γ : W ⟶ X) (β : W ⟶ A),
        γ ≫ m = β ≫ θ →
          ∃! l : W ⟶ P,
            l ≫ p = γ ∧ l ≫ q = β :=
  @Dom.exists_pullback_of_mem_subdomainMorphisms

example {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
    {X A B : Dom C} {m : X ⟶ B} (hm : Dom.subdomainMorphisms m) (θ : A ⟶ B) :
    ∃ (P : Dom C) (p : P ⟶ X) (q : P ⟶ A),
      Dom.subdomainMorphisms q ∧
      p ≫ m = q ≫ θ ∧
      ∀ {W : Dom C} (γ : W ⟶ X) (β : W ⟶ A),
        γ ≫ m = β ≫ θ →
          ∃! l : W ⟶ P,
            l ≫ p = γ ∧ l ≫ q = β :=
  Dom.exists_pullback_of_mem_subdomainMorphisms hm θ

example {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
    {X A B : Dom C} {m : X ⟶ B} (hm : Dom.subdomainMorphisms m) (θ : A ⟶ B)
    {W : Dom C} (γ : W ⟶ X) (β : W ⟶ A) (hcomm : γ ≫ m = β ≫ θ) :
    ∃ (P : Dom C) (p : P ⟶ X) (q : P ⟶ A) (l : W ⟶ P),
      Mono q ∧ p ≫ m = q ≫ θ ∧ l ≫ p = γ ∧ l ≫ q = β ∧
        ∀ k : W ⟶ P, k ≫ p = γ → k ≫ q = β → k = l := by
  obtain ⟨P, p, q, hq, hsq, huniv⟩ :=
    Dom.exists_pullback_of_mem_subdomainMorphisms hm θ
  obtain ⟨l, ⟨hlp, hlq⟩, hlu⟩ := huniv γ β hcomm
  exact ⟨P, p, q, l, Dom.mono_of_mem_subdomainMorphisms hq, hsq, hlp, hlq,
    fun k hkp hkq => hlu k ⟨hkp, hkq⟩⟩

end CategoryTheory
