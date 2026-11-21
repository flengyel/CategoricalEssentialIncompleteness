/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.NumericalDomains
public import CategoricalEssentialIncompleteness.NumericalEmbedding

/-!
# Inverse image of numerical restriction domains

Inverse image preserves the bottom domain, binary meets, and binary joins along every
partial numerical morphism. Along total morphisms it also preserves the top domain,
giving contravariant bounded lattice homomorphisms.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
open CategoryTheory
namespace CategoricalEssentialIncompleteness
namespace Numerical

@[simp] theorem domainInverse_bot {X Y : Numerical} (f : X ⟶ Y) :
    domainInverse f ⊥ = ⊥ := by
  apply Domain.support_injective
  ext n
  simp only [domainInverse_support, Domain.support_bot, Set.mem_ofPred_eq,
    Set.mem_empty_iff_false, and_false, exists_false]

@[simp] theorem domainInverse_inf {X Y : Numerical} (f : X ⟶ Y) (a b : Domain Y) :
    domainInverse f (a ⊓ b) = domainInverse f a ⊓ domainInverse f b := by
  apply Domain.support_injective
  ext n
  simp only [domainInverse_support, Domain.support_inf, Set.mem_inter_iff, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨m, hm, ha, hb⟩
    exact ⟨⟨m, hm, ha⟩, ⟨m, hm, hb⟩⟩
  · rintro ⟨⟨m, hm, ha⟩, ⟨k, hk, hb⟩⟩
    have hkm : k = m := Part.mem_unique hk hm
    subst k
    exact ⟨m, hm, ha, hb⟩

@[simp] theorem domainInverse_sup {X Y : Numerical} (f : X ⟶ Y) (a b : Domain Y) :
    domainInverse f (a ⊔ b) = domainInverse f a ⊔ domainInverse f b := by
  apply Domain.support_injective
  ext n
  simp only [domainInverse_support, Domain.support_sup, Set.mem_union, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨m, hm, ha | hb⟩
    · exact Or.inl ⟨m, hm, ha⟩
    · exact Or.inr ⟨m, hm, hb⟩
  · rintro (⟨m, hm, ha⟩ | ⟨m, hm, hb⟩)
    · exact ⟨m, hm, Or.inl ha⟩
    · exact ⟨m, hm, Or.inr hb⟩

@[simp] theorem domainInverse_top {X Y : Total} (f : X ⟶ Y) :
    domainInverse f.hom ⊤ = ⊤ := by
  apply Domain.support_injective
  ext n
  simp only [domainInverse_support, Domain.support_top, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨m, hm, _⟩
    exact f.hom.source hm
  · intro hn
    have hf := Part.get_mem ((total_iff f.hom).mp f.property n hn)
    exact ⟨_, hf, f.hom.target hf⟩

@[simp] theorem domainInverse_id (X : Numerical) (e : Domain X) :
    domainInverse (𝟙 X) e = e := by
  apply Domain.support_injective
  ext n
  simp only [domainInverse_support, id_val, Set.mem_ofPred_eq, mem_supportIdentity]
  constructor
  · rintro ⟨m, ⟨_, rfl⟩, hm⟩
    exact hm
  · intro hn
    exact ⟨n, ⟨e.hom.source (Part.get_mem hn), rfl⟩, hn⟩

@[simp] theorem domainInverse_comp {X Y Z : Numerical} (f : X ⟶ Y) (g : Y ⟶ Z)
    (e : Domain Z) : domainInverse (f ≫ g) e = domainInverse f (domainInverse g e) := by
  apply Domain.support_injective
  ext n
  simp only [domainInverse_support, comp_val, Set.mem_ofPred_eq, Part.mem_bind_iff]
  constructor
  · rintro ⟨m, ⟨k, hk, hm⟩, he⟩
    exact ⟨k, hk, m, hm, he⟩
  · rintro ⟨k, hk, m, hm, he⟩
    exact ⟨m, ⟨k, hk, hm⟩, he⟩

/-- Inverse image along a total numerical morphism preserves the bounded lattice
operations. -/
def domainInverseHom {X Y : Total} (f : X ⟶ Y) :
    BoundedLatticeHom (Domain Y.obj) (Domain X.obj) where
  toFun := domainInverse f.hom
  map_sup' := domainInverse_sup f.hom
  map_inf' := domainInverse_inf f.hom
  map_top' := domainInverse_top f
  map_bot' := domainInverse_bot f.hom

@[simp] theorem domainInverseHom_apply {X Y : Total} (f : X ⟶ Y) (e : Domain Y.obj) :
    domainInverseHom f e = domainInverse f.hom e := rfl

@[simp] theorem domainInverseHom_id (X : Total) :
    domainInverseHom (𝟙 X) = BoundedLatticeHom.id (Domain X.obj) := by
  apply DFunLike.ext
  intro e
  exact domainInverse_id X.obj e

@[simp] theorem domainInverseHom_comp {X Y Z : Total} (f : X ⟶ Y) (g : Y ⟶ Z) :
    domainInverseHom (f ≫ g) = (domainInverseHom f).comp (domainInverseHom g) := by
  apply DFunLike.ext
  intro e
  exact domainInverse_comp f.hom g.hom e

end Numerical
end CategoricalEssentialIncompleteness
