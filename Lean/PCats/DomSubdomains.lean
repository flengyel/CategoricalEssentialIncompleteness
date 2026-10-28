/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import PCats.Domains

/-!
# Subdomains, composition, inverse images, and the comparison isomorphism

The composition-of-subdomains and inverse-image clauses of Rosolini,
Theorem 2.3.3.

A subdomain of `A : Dom C` is a restriction idempotent on `A.base` received by
`A.idem`. It carries the domain object `⟨A.base, s.idem⟩` and includes into `A`
by `s.idem`, a monomorphism because a morphism into `s.toDom` is absorbed by
`s.idem`.

The canonical subdomain inclusions are closed under composition. For
`t : Subdomain s.toDom` the composite `s.compose t` has idempotent `t.idem`,
which is received by `A.idem` because it is received by `s.idem` and `s.idem`
by `A.idem`. The represented domain object is definitionally `t.toDom`, and

    (s.compose t).inclusion = t.inclusion ≫ s.inclusion.

The inverse image of `s : Subdomain B` along `θ : A ⟶ B` has idempotent
`rst (θ.hom ≫ s.idem)`. It is received by `A.idem` because `rst θ.hom = A.idem`,
restriction idempotents commute, and `rst (θ.hom ≫ s.idem)` is absorbed by
`rst θ.hom`. The upper arrow of the square is `θ.hom ≫ s.idem`, and
commutativity is R4 for `θ.hom` and `s.idem`.

`Subdomain.inverseImage_existsUnique` states the pullback universal property
directly: the lift of a compatible pair `γ`, `β` is `β.hom`, which lands in the
inverse image by R4 together with the compatibility equation. No
`Limits.HasPullbacks` instance is declared.

`Subdomain.inverseImageIso` identifies `s.toDom` with the inverse image of `s`
along the inverse of an isomorphism `i : A ≅ B` of the ambient domains. Its
forward map is the lift of the compatible pair `𝟙 s.toDom`,
`s.inclusion ≫ i.hom`, its backward map is the upper arrow
`Subdomain.inverseImageMap`, and

    (s.inverseImageIso i).hom ≫ (s.inverseImage i.inv).inclusion
      = s.inclusion ≫ i.hom.

On underlying morphisms of `C` the two maps are `s.idem ≫ i.hom.hom` and
`i.inv.hom ≫ s.idem`. The first inverse law is the lift equation for the upper
arrow; the second is obtained by right-cancelling the monic inclusion of the
inverse image.

The results above are results about the canonical inclusions. The family of
morphisms isomorphic over a fixed codomain to a canonical inclusion is
`Dom.subdomainMorphisms` of `PCats.DomSubdomainMorphisms`, which uses
`inverseImageIso` to transfer composition closure to all of its members, and
`inverseImage_existsUnique` to transfer pullback representatives: the
canonical-inclusion case proved here is what
`Dom.exists_pullback_of_mem_subdomainMorphisms` invokes for an arbitrary
member.

The construction assumes `Category`, `PCategoryStruct`, and `PCategory`.
Ranges, zero morphisms, and choice are not used.

Together with the direct binary products in `Dom C`, these results establish
Rosolini's dominion conditions for `Dom.subdomainMorphisms`. No bundled Lean
definition or structure for dominions is provided.

Theorem 2.3.2 is formalized in `PCats.DomTotalEmbedding`: `Dom.totalEmbedding`
is full and faithful, and `Dom.totalEmbedding_binaryProduct_existsUnique`
proves preservation of binary products against an arbitrary apex of `Dom C`.
Theorem 2.3.3, the induced embedding of `C` into the partial-map category over
`Dom C` determined by these monomorphisms, remains unformalized.

The equalizer clause of Corollary 2.4.10 is formalized in
`PCats.DomEqualizers`, whose equalizer is the inverse image, along a pairing,
of the subdomain carried by the range of the diagonal; the finite-limit
consequence of that corollary is not bundled as a Lean result.
-/

universe v u

namespace CategoryTheory

open PCategoryStruct

variable {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]

namespace Dom

/-- A subdomain of `A`: a restriction idempotent on `A.base` received by
`A.idem`. -/
structure Subdomain (A : Dom C) where
  /-- The underlying idempotent. -/
  idem : A.base ⟶ A.base
  /-- It is a restriction idempotent. -/
  rst_idem : rst idem = idem
  /-- It is received by `A`. -/
  comp_idem : idem ≫ A.idem = idem

namespace Subdomain

variable {A B : Dom C}

/-! ### The subdomain as a domain object -/

/-- The domain object carried by a subdomain. -/
def toDom (s : Subdomain A) : Dom C := ⟨A.base, s.idem, s.rst_idem⟩

@[simp] lemma toDom_base (s : Subdomain A) : s.toDom.base = A.base := rfl

@[simp] lemma toDom_idem (s : Subdomain A) : s.toDom.idem = s.idem := rfl

lemma idem_comp_idem (s : Subdomain A) : s.idem ≫ s.idem = s.idem :=
  s.toDom.idem_comp_idem

/-- The inclusion of a subdomain into its ambient domain. -/
def inclusion (s : Subdomain A) : s.toDom ⟶ A where
  hom := s.idem
  rst_hom := s.rst_idem
  comp_idem := s.comp_idem

@[simp] lemma inclusion_hom (s : Subdomain A) : (inclusion s).hom = s.idem := rfl

/-- The inclusion is a monomorphism: a morphism into `s.toDom` is absorbed by
`s.idem`, so postcomposition with the inclusion recovers it. -/
theorem inclusion_mono (s : Subdomain A) : Mono s.inclusion :=
  ⟨fun f g h => Hom.ext' (by
    have hf : f.hom ≫ s.idem = f.hom := f.comp_idem
    have hg : g.hom ≫ s.idem = g.hom := g.comp_idem
    have h' : f.hom ≫ s.idem = g.hom ≫ s.idem := congrArg Hom.hom h
    rwa [hf, hg] at h')⟩

/-! ### Composition -/

/-- An idempotent received by `s.idem` is received by `A.idem`. -/
private lemma comp_ambient_idem (s : Subdomain A) {i : A.base ⟶ A.base}
    (hi : i ≫ s.idem = i) : i ≫ A.idem = i :=
  calc i ≫ A.idem = (i ≫ s.idem) ≫ A.idem := by rw [hi]
    _ = i ≫ s.idem ≫ A.idem := Category.assoc _ _ _
    _ = i ≫ s.idem := by rw [s.comp_idem]
    _ = i := hi

/-- The composite of nested subdomains, represented by the inner idempotent.
Taking `t.idem` rather than `t.idem ≫ s.idem` makes the represented domain
object definitionally `t.toDom`. -/
def compose (s : Subdomain A) (t : Subdomain s.toDom) : Subdomain A where
  idem := t.idem
  rst_idem := t.rst_idem
  comp_idem := comp_ambient_idem s t.comp_idem

@[simp] lemma compose_idem (s : Subdomain A) (t : Subdomain s.toDom) :
    (s.compose t).idem = t.idem := rfl

@[simp] lemma compose_toDom (s : Subdomain A) (t : Subdomain s.toDom) :
    (s.compose t).toDom = t.toDom := rfl

/-- The canonical inclusion of `s.compose t` is the composite of the
canonical inclusions of `t` and `s`. -/
theorem compose_inclusion (s : Subdomain A) (t : Subdomain s.toDom) :
    (s.compose t).inclusion = t.inclusion ≫ s.inclusion :=
  Hom.ext' t.comp_idem.symm

/-! ### Inverse images -/

/-- The inverse image of a subdomain of `B` along `θ : A ⟶ B`. -/
def inverseImage (s : Subdomain B) (θ : A ⟶ B) : Subdomain A where
  idem := rst (θ.hom ≫ s.idem)
  rst_idem := PCategory.rst_rst _
  comp_idem := by
    have habsorb : rst θ.hom ≫ rst (θ.hom ≫ s.idem) = rst (θ.hom ≫ s.idem) :=
      RestrictionCategory.rst_comp_absorb θ.hom s.idem
    calc rst (θ.hom ≫ s.idem) ≫ A.idem
        = rst (θ.hom ≫ s.idem) ≫ rst θ.hom := by rw [θ.rst_hom]
      _ = rst θ.hom ≫ rst (θ.hom ≫ s.idem) :=
          PCategory.rst_comm' (θ.hom ≫ s.idem) θ.hom
      _ = rst (θ.hom ≫ s.idem) := habsorb

@[simp] lemma inverseImage_idem (s : Subdomain B) (θ : A ⟶ B) :
    (s.inverseImage θ).idem = rst (θ.hom ≫ s.idem) := rfl

/-- The upper arrow of the inverse-image square. -/
def inverseImageMap (s : Subdomain B) (θ : A ⟶ B) :
    (s.inverseImage θ).toDom ⟶ s.toDom where
  hom := θ.hom ≫ s.idem
  rst_hom := rfl
  comp_idem := by
    change (θ.hom ≫ s.idem) ≫ s.idem = θ.hom ≫ s.idem
    rw [Category.assoc, s.idem_comp_idem]

@[simp] lemma inverseImageMap_hom (s : Subdomain B) (θ : A ⟶ B) :
    (s.inverseImageMap θ).hom = θ.hom ≫ s.idem := rfl

/-- The inverse-image square commutes. -/
theorem inverseImage_comm (s : Subdomain B) (θ : A ⟶ B) :
    s.inverseImageMap θ ≫ s.inclusion
      = (s.inverseImage θ).inclusion ≫ θ := by
  refine Hom.ext' ?_
  change (θ.hom ≫ s.idem) ≫ s.idem = rst (θ.hom ≫ s.idem) ≫ θ.hom
  rw [Category.assoc, s.idem_comp_idem, PCategory.rst_comp' θ.hom s.idem,
    s.rst_idem]

/-! ### The pullback universal property -/

/-- The compatibility equation on underlying morphisms. -/
private lemma hom_comm (s : Subdomain B) (θ : A ⟶ B) {W : Dom C}
    {γ : W ⟶ s.toDom} {β : W ⟶ A} (hcomm : γ ≫ s.inclusion = β ≫ θ) :
    β.hom ≫ θ.hom = (γ.hom : W.base ⟶ B.base) := by
  have hγ : (γ.hom : W.base ⟶ B.base) ≫ s.idem = γ.hom := γ.comp_idem
  have h : (γ.hom : W.base ⟶ B.base) ≫ s.idem = β.hom ≫ θ.hom :=
    congrArg Hom.hom hcomm
  rw [hγ] at h
  exact h.symm

/-- A compatible morphism into `A` is received by the inverse-image
idempotent. -/
private lemma comp_inverseImage_idem (s : Subdomain B) (θ : A ⟶ B)
    {W : Dom C} {g : W.base ⟶ B.base} {b : W.base ⟶ A.base}
    (hg : g ≫ s.idem = g) (hrg : rst g = W.idem) (hrb : rst b = W.idem)
    (hbθ : b ≫ θ.hom = g) : b ≫ rst (θ.hom ≫ s.idem) = b :=
  calc b ≫ rst (θ.hom ≫ s.idem)
      = rst (b ≫ θ.hom ≫ s.idem) ≫ b :=
        (PCategory.rst_comp' b (θ.hom ≫ s.idem)).symm
    _ = rst g ≫ b := by rw [← Category.assoc, hbθ, hg]
    _ = W.idem ≫ b := by rw [hrg]
    _ = rst b ≫ b := by rw [hrb]
    _ = b := RestrictionCategory.rst_comp_self b

/-- A compatible morphism composed with the upper arrow recovers `γ`. -/
private lemma comp_inverseImageMap_hom (s : Subdomain B) (θ : A ⟶ B)
    {W : Dom C} {g : W.base ⟶ B.base} {b : W.base ⟶ A.base}
    (hg : g ≫ s.idem = g) (hbθ : b ≫ θ.hom = g) :
    b ≫ (θ.hom ≫ s.idem) = g := by
  rw [← Category.assoc, hbθ, hg]

/-- The mediating morphism for a compatible pair, with underlying morphism
`β.hom`. -/
def inverseImageLift (s : Subdomain B) (θ : A ⟶ B) {W : Dom C}
    (γ : W ⟶ s.toDom) (β : W ⟶ A) (hcomm : γ ≫ s.inclusion = β ≫ θ) :
    W ⟶ (s.inverseImage θ).toDom where
  hom := β.hom
  rst_hom := β.rst_hom
  comp_idem := by
    change β.hom ≫ rst (θ.hom ≫ s.idem) = β.hom
    exact comp_inverseImage_idem s θ γ.comp_idem γ.rst_hom β.rst_hom
      (hom_comm s θ hcomm)

@[simp] lemma inverseImageLift_hom (s : Subdomain B) (θ : A ⟶ B) {W : Dom C}
    (γ : W ⟶ s.toDom) (β : W ⟶ A) (hcomm : γ ≫ s.inclusion = β ≫ θ) :
    (s.inverseImageLift θ γ β hcomm).hom = β.hom := rfl

theorem inverseImageLift_map (s : Subdomain B) (θ : A ⟶ B) {W : Dom C}
    (γ : W ⟶ s.toDom) (β : W ⟶ A) (hcomm : γ ≫ s.inclusion = β ≫ θ) :
    s.inverseImageLift θ γ β hcomm ≫ s.inverseImageMap θ = γ :=
  Hom.ext'
    (comp_inverseImageMap_hom s θ γ.comp_idem (hom_comm s θ hcomm))

theorem inverseImageLift_inclusion (s : Subdomain B) (θ : A ⟶ B) {W : Dom C}
    (γ : W ⟶ s.toDom) (β : W ⟶ A) (hcomm : γ ≫ s.inclusion = β ≫ θ) :
    s.inverseImageLift θ γ β hcomm ≫ (s.inverseImage θ).inclusion = β :=
  Hom.ext' (s.inverseImageLift θ γ β hcomm).comp_idem

theorem inverseImageLift_unique (s : Subdomain B) (θ : A ⟶ B) {W : Dom C}
    (γ : W ⟶ s.toDom) (β : W ⟶ A) (hcomm : γ ≫ s.inclusion = β ≫ θ)
    (l : W ⟶ (s.inverseImage θ).toDom)
    (hl : l ≫ (s.inverseImage θ).inclusion = β) :
    l = s.inverseImageLift θ γ β hcomm := by
  refine Hom.ext' ?_
  have habs : l.hom ≫ rst (θ.hom ≫ s.idem) = l.hom := l.comp_idem
  have h : l.hom ≫ rst (θ.hom ≫ s.idem) = β.hom := congrArg Hom.hom hl
  rwa [habs] at h

/-- The pullback universal property, stated directly. -/
theorem inverseImage_existsUnique (s : Subdomain B) (θ : A ⟶ B) {W : Dom C}
    (γ : W ⟶ s.toDom) (β : W ⟶ A) (hcomm : γ ≫ s.inclusion = β ≫ θ) :
    ∃! l : W ⟶ (s.inverseImage θ).toDom,
      l ≫ s.inverseImageMap θ = γ ∧
        l ≫ (s.inverseImage θ).inclusion = β :=
  ⟨s.inverseImageLift θ γ β hcomm,
    ⟨s.inverseImageLift_map θ γ β hcomm,
      s.inverseImageLift_inclusion θ γ β hcomm⟩,
    fun _ hl => s.inverseImageLift_unique θ γ β hcomm _ hl.2⟩

/-! ### The comparison isomorphism -/

/-- The compatibility equation for the comparison isomorphism. -/
private lemma inverseImageIso_comm (s : Subdomain A) (i : A ≅ B) :
    (𝟙 s.toDom) ≫ s.inclusion = (s.inclusion ≫ i.hom) ≫ i.inv := by
  rw [Category.id_comp, Category.assoc, i.hom_inv_id, Category.comp_id]

/-- A represented domain is isomorphic to its inverse image along the inverse
of an isomorphism of the ambient domains. The forward map is the lift of the
compatible pair `𝟙 s.toDom`, `s.inclusion ≫ i.hom`; the backward map is the
upper arrow of the inverse-image square. -/
def inverseImageIso (s : Subdomain A) (i : A ≅ B) :
    s.toDom ≅ (s.inverseImage i.inv).toDom where
  hom := s.inverseImageLift i.inv (𝟙 s.toDom) (s.inclusion ≫ i.hom)
    (inverseImageIso_comm s i)
  inv := s.inverseImageMap i.inv
  hom_inv_id := s.inverseImageLift_map i.inv (𝟙 s.toDom) (s.inclusion ≫ i.hom)
    (inverseImageIso_comm s i)
  inv_hom_id := by
    refine (s.inverseImage i.inv).inclusion_mono.right_cancellation _ _ ?_
    rw [Category.assoc, s.inverseImageLift_inclusion, ← Category.assoc,
      s.inverseImage_comm, Category.assoc, i.inv_hom_id, Category.comp_id,
      Category.id_comp]

@[simp] theorem inverseImageIso_hom_hom (s : Subdomain A) (i : A ≅ B) :
    (s.inverseImageIso i).hom.hom = s.idem ≫ i.hom.hom := rfl

@[simp] theorem inverseImageIso_inv_hom (s : Subdomain A) (i : A ≅ B) :
    (s.inverseImageIso i).inv.hom = i.inv.hom ≫ s.idem := rfl

/-- The forward map followed by the inverse-image inclusion is the original
inclusion transported along `i`. -/
theorem inverseImageIso_hom_inclusion (s : Subdomain A) (i : A ≅ B) :
    (s.inverseImageIso i).hom ≫ (s.inverseImage i.inv).inclusion
      = s.inclusion ≫ i.hom :=
  s.inverseImageLift_inclusion i.inv (𝟙 s.toDom) (s.inclusion ≫ i.hom)
    (inverseImageIso_comm s i)

end Subdomain

end Dom

end CategoryTheory
