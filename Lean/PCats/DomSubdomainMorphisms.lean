/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import PCats.DomSubdomains

/-!
# Morphisms isomorphic to canonical subdomain inclusions

`Dom.subdomainMorphisms` is the family of morphisms of `Dom C` that are
isomorphic over a fixed codomain to a canonical subdomain inclusion: a morphism
`m : X ⟶ A` belongs when there are `s : Dom.Subdomain A` and an isomorphism
`i : X ≅ s.toDom` with

    i.hom ≫ s.inclusion = m.

Every member is monic, since the canonical inclusion `s.inclusion` is monic and
the isomorphism of sources cancels against its inverse. The canonical
inclusions belong, by the identity isomorphism, and the identity of `A`
belongs, by the subdomain `Dom.Subdomain.top A` carried by `A.idem` itself.
Membership is invariant under changing the source by an isomorphism over the
same codomain: `m` belongs exactly when `i.hom ≫ m` does, for `i` an
isomorphism of sources.

The family is closed under composition. Given representatives `s` of
`m : X ⟶ Y` through `i : X ≅ s.toDom` and `t` of `n : Y ⟶ A` through
`j : Y ≅ t.toDom`, the subdomain `s.inverseImage j.inv` of `t.toDom` transports
`s` along `j`, and `Subdomain.inverseImageIso` identifies `s.toDom` with it.
The canonical composite subdomain `t.compose (s.inverseImage j.inv)` of `A`
then represents `m ≫ n`, through the isomorphism obtained by precomposing that
comparison isomorphism with `i`. `Dom.instIsMultiplicativeSubdomainMorphisms`
records the identity and composition closure facts, and only those.

Every member has a pullback along an arbitrary morphism, and the base-changed
leg is again a member. For `m : X ⟶ B` in the family, represented by
`s : Subdomain B` through `i : X ≅ s.toDom`, and for `θ : A ⟶ B`,
`Dom.exists_pullback_of_mem_subdomainMorphisms` exhibits the pullback object
`(s.inverseImage θ).toDom` with legs `s.inverseImageMap θ ≫ i.inv` into `X` and
`(s.inverseImage θ).inclusion` into `A`. The second leg is a canonical
inclusion, hence a member; the square and its `∃!` universal property are
stated directly. The existential theorem does not define a choice of pullback
objects or legs. No `Limits.HasPullbacks` instance and no base-change instance
is declared. It is distinct from `Subdomain.inverseImage_existsUnique`, which
proves the canonical-inclusion case that its construction uses.

The construction assumes `Category`, `PCategoryStruct`, and `PCategory`.

Together with the direct binary products in `Dom C`, these results establish
the defining conditions for Rosolini's dominion: `Dom.subdomainMorphisms` is a
source-isomorphism-saturated family of monomorphisms, contains the identities,
is closed under composition, and admits a pullback representative in the family
along every morphism. No bundled Lean definition or structure for dominions is
provided. Rosolini's induced embedding of `C` remains unformalized.
-/

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]

namespace Dom

namespace Subdomain

/-! ### The identity subdomain -/

/-- The subdomain of `A` carried by `A.idem`, whose inclusion is `𝟙 A`. -/
def top (A : Dom C) : Subdomain A where
  idem := A.idem
  rst_idem := A.rst_idem
  comp_idem := A.idem_comp_idem

@[simp] lemma top_idem (A : Dom C) :
    (top A).idem = A.idem := rfl

@[simp] lemma top_toDom (A : Dom C) :
    (top A).toDom = A := rfl

@[simp] lemma top_inclusion (A : Dom C) :
    (top A).inclusion = 𝟙 A := rfl

end Subdomain

end Dom

/-! ### The family of subdomain morphisms -/

/-- The morphisms isomorphic over a fixed codomain to a canonical subdomain
inclusion. -/
def Dom.subdomainMorphisms : MorphismProperty (Dom C) :=
  fun {X A} m =>
    ∃ (s : Dom.Subdomain A) (i : X ≅ s.toDom),
      i.hom ≫ s.inclusion = m

lemma Dom.subdomainMorphisms_iff {X A : Dom C} (m : X ⟶ A) :
    Dom.subdomainMorphisms m ↔
      ∃ (s : Dom.Subdomain A) (i : X ≅ s.toDom),
        i.hom ≫ s.inclusion = m :=
  Iff.rfl

/-- A canonical inclusion belongs, witnessed by the identity isomorphism on
`s.toDom`. -/
theorem Dom.Subdomain.inclusion_mem_subdomainMorphisms
    {A : Dom C} (s : Dom.Subdomain A) :
    Dom.subdomainMorphisms s.inclusion :=
  ⟨s, ⟨𝟙 s.toDom, 𝟙 s.toDom, Category.id_comp _, Category.id_comp _⟩,
    Category.id_comp s.inclusion⟩

/-- The identity of `A` belongs, witnessed by `Dom.Subdomain.top A` and the
identity isomorphism on `A`. -/
theorem Dom.id_mem_subdomainMorphisms (A : Dom C) :
    Dom.subdomainMorphisms (𝟙 A) :=
  ⟨Dom.Subdomain.top A, ⟨𝟙 A, 𝟙 A, Category.id_comp _, Category.id_comp _⟩,
    Category.id_comp (𝟙 A)⟩

/-- Every member is a monomorphism: the canonical inclusion of the representing
subdomain is monic, and the isomorphism of sources cancels against its
inverse. -/
theorem Dom.mono_of_mem_subdomainMorphisms
    {X A : Dom C} {m : X ⟶ A}
    (hm : Dom.subdomainMorphisms m) :
    Mono m := by
  obtain ⟨s, i, hi⟩ := hm
  refine ⟨fun f g h => ?_⟩
  have h' : (f ≫ i.hom) ≫ s.inclusion = (g ≫ i.hom) ≫ s.inclusion := by
    rw [Category.assoc, Category.assoc, hi]
    exact h
  have hfg : f ≫ i.hom = g ≫ i.hom :=
    s.inclusion_mono.right_cancellation _ _ h'
  calc f = (f ≫ i.hom) ≫ i.inv := by
        rw [Category.assoc, i.hom_inv_id, Category.comp_id]
    _ = (g ≫ i.hom) ≫ i.inv := by rw [hfg]
    _ = g := by rw [Category.assoc, i.hom_inv_id, Category.comp_id]

/-- Membership is preserved by precomposition with an isomorphism of sources:
the witness `j` is replaced by the composite of `i` and `j`. -/
theorem Dom.subdomainMorphisms_precomp_iso
    {X Y A : Dom C} (i : X ≅ Y) {m : Y ⟶ A}
    (hm : Dom.subdomainMorphisms m) :
    Dom.subdomainMorphisms (i.hom ≫ m) := by
  obtain ⟨s, j, hj⟩ := hm
  refine ⟨s, ⟨i.hom ≫ j.hom, j.inv ≫ i.inv, ?_, ?_⟩, ?_⟩
  · rw [Category.assoc, ← Category.assoc j.hom, j.hom_inv_id, Category.id_comp,
      i.hom_inv_id]
  · rw [Category.assoc, ← Category.assoc i.inv, i.inv_hom_id, Category.id_comp,
      j.inv_hom_id]
  · rw [Category.assoc, hj]

/-- Membership is invariant under changing the source by an isomorphism over
the same codomain. The reverse implication precomposes with the inverse
isomorphism and cancels by `i.inv_hom_id`. -/
theorem Dom.subdomainMorphisms_precomp_iso_iff
    {X Y A : Dom C} (i : X ≅ Y) (m : Y ⟶ A) :
    Dom.subdomainMorphisms (i.hom ≫ m) ↔
      Dom.subdomainMorphisms m := by
  refine ⟨fun hm => ?_, fun hm => Dom.subdomainMorphisms_precomp_iso i hm⟩
  have h : Dom.subdomainMorphisms (i.inv ≫ i.hom ≫ m) :=
    Dom.subdomainMorphisms_precomp_iso
      (⟨i.inv, i.hom, i.inv_hom_id, i.hom_inv_id⟩ : Y ≅ X) hm
  rwa [← Category.assoc, i.inv_hom_id, Category.id_comp] at h

/-! ### Closure under composition -/

/-- The family is closed under composition. The representative of `m ≫ n` is
the canonical composite subdomain `t.compose (s.inverseImage j.inv)`, reached
from the representative `s` of `m` by transporting it along `j` into
`t.toDom`. -/
theorem Dom.subdomainMorphisms_comp
    {X Y A : Dom C} {m : X ⟶ Y} {n : Y ⟶ A}
    (hm : Dom.subdomainMorphisms m)
    (hn : Dom.subdomainMorphisms n) :
    Dom.subdomainMorphisms (m ≫ n) := by
  obtain ⟨s, i, hi⟩ := hm
  obtain ⟨t, j, hj⟩ := hn
  have h := Dom.subdomainMorphisms_precomp_iso i
    (Dom.subdomainMorphisms_precomp_iso (s.inverseImageIso j)
      (Dom.Subdomain.inclusion_mem_subdomainMorphisms
        (t.compose (s.inverseImage j.inv))))
  have key : i.hom ≫ (s.inverseImageIso j).hom
        ≫ (t.compose (s.inverseImage j.inv)).inclusion = m ≫ n := by
    rw [Dom.Subdomain.compose_inclusion,
      ← Category.assoc (s.inverseImageIso j).hom,
      Dom.Subdomain.inverseImageIso_hom_inclusion, Category.assoc, hj,
      ← Category.assoc, hi]
  rwa [key] at h

/-- Identities belong and composites of members are members. This records those
two closure facts and nothing further. -/
instance Dom.instIsMultiplicativeSubdomainMorphisms :
    (Dom.subdomainMorphisms (C := C)).IsMultiplicative where
  id_mem := Dom.id_mem_subdomainMorphisms
  comp_mem _ _ hf hg := Dom.subdomainMorphisms_comp hf hg

/-! ### Pullback representatives -/

/-- Every member has a pullback along an arbitrary morphism whose base-changed
leg `q` is again a member. The square and its universal property are stated
directly; the pullback object is exhibited, not selected. -/
theorem Dom.exists_pullback_of_mem_subdomainMorphisms
    {X A B : Dom C} {m : X ⟶ B}
    (hm : Dom.subdomainMorphisms m) (θ : A ⟶ B) :
    ∃ (P : Dom C) (p : P ⟶ X) (q : P ⟶ A),
      Dom.subdomainMorphisms q ∧
      p ≫ m = q ≫ θ ∧
      ∀ {W : Dom C} (γ : W ⟶ X) (β : W ⟶ A),
        γ ≫ m = β ≫ θ →
          ∃! l : W ⟶ P,
            l ≫ p = γ ∧ l ≫ q = β := by
  obtain ⟨s, i, hi⟩ := hm
  refine ⟨(s.inverseImage θ).toDom, s.inverseImageMap θ ≫ i.inv,
    (s.inverseImage θ).inclusion,
    Dom.Subdomain.inclusion_mem_subdomainMorphisms _, ?_, ?_⟩
  · rw [← hi, Category.assoc, ← Category.assoc i.inv, i.inv_hom_id,
      Category.id_comp, s.inverseImage_comm θ]
  · intro W γ β hcomm
    have hcanon : (γ ≫ i.hom) ≫ s.inclusion = β ≫ θ := by
      rw [Category.assoc, hi, hcomm]
    refine ⟨s.inverseImageLift θ (γ ≫ i.hom) β hcanon, ⟨?_, ?_⟩, ?_⟩
    · rw [← Category.assoc, s.inverseImageLift_map, Category.assoc,
        i.hom_inv_id, Category.comp_id]
    · exact s.inverseImageLift_inclusion θ (γ ≫ i.hom) β hcanon
    · intro l hl
      exact s.inverseImageLift_unique θ (γ ≫ i.hom) β hcanon l hl.2

end CategoryTheory
