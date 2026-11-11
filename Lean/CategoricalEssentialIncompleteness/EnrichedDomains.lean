/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.EnrichedTotals
public import CategoricalEssentialIncompleteness.InternalRepresentation

/-!
# Restriction inverse image on the domain equalizers

The action is constructed as the restriction of composition, lifted to the
fixed-point equalizer. Its identity, composition, meet, and bound laws are
proved from the restriction equations. The extra lattice and join-stability
structure is specified on these equalizers, as in the manuscript.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe v u w
open CategoryTheory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness
namespace EnrichedRestriction
variable {V : Type u} [Category.{v} V] [HasFiniteLimits V] {O : Type w}
variable {H : InternalHom V O} (R : EnrichedRestriction H)

/-- Restriction inverse image, without a totality assumption on the arrow. -/
def domainInverse {T : V} {X Y : O} (f : T ⟶ H.hom X Y)
    (e : T ⟶ R.domainObject Y) : T ⟶ R.domainObject X :=
  R.domainLift (R.restrict (H.comp f (e ≫ R.domainι Y))) (R.restrict_restrict _)

@[simp] theorem domainInverse_ι {T : V} {X Y : O} (f : T ⟶ H.hom X Y)
    (e : T ⟶ R.domainObject Y) :
    R.domainInverse f e ≫ R.domainι X = R.restrict (H.comp f (e ≫ R.domainι Y)) := by
  simp [domainInverse]

@[simp] theorem precomp_domainInverse {T T' : V} (k : T' ⟶ T) {X Y : O}
    (f : T ⟶ H.hom X Y) (e : T ⟶ R.domainObject Y) :
    k ≫ R.domainInverse f e = R.domainInverse (k ≫ f) (k ≫ e) := by
  apply (cancel_mono (R.domainι X)).mp
  simp only [Category.assoc, R.domainInverse_ι, R.precomp_restrict, H.precomp_comp]

@[simp] theorem domainInverse_id {T : V} {X : O} (e : T ⟶ R.domainObject X) :
    R.domainInverse (H.identity X) e = e := by
  apply (cancel_mono (R.domainι X)).mp
  rw [R.domainInverse_ι, R.id_comp, R.domain_condition]

theorem domainInverse_comp {T : V} {X Y Z : O}
    (f : T ⟶ H.hom X Y) (g : T ⟶ H.hom Y Z) (e : T ⟶ R.domainObject Z) :
    R.domainInverse (H.comp f g) e = R.domainInverse f (R.domainInverse g e) := by
  apply (cancel_mono (R.domainι X)).mp
  simp only [R.domainInverse_ι, R.assoc]
  exact RestrictionCategory.rst_comp_rst_right (C := R.Parameterized T)
    (X := ⟨X⟩) (Y := ⟨Y⟩) (Z := ⟨Z⟩) f (H.comp g (e ≫ R.domainι Z))

/-- The manuscript's inverse-image morphism, defined for all partial arrows. -/
def partialDomainAction (X Y : O) : H.hom X Y ⨯ R.domainObject Y ⟶ R.domainObject X :=
  R.domainInverse prod.fst prod.snd

theorem partialDomainAction_apply {T : V} {X Y : O}
    (f : T ⟶ H.hom X Y) (e : T ⟶ R.domainObject Y) :
    R.domainInverse f e = prod.lift f e ≫ R.partialDomainAction X Y := by
  simp [partialDomainAction, R.precomp_domainInverse]

/-- The restriction of the partial-arrow action to the totality pullback. -/
def domainAction (X Y : O) : R.totalObject X Y ⨯ R.domainObject Y ⟶ R.domainObject X :=
  prod.map (R.totalι X Y) (𝟙 _) ≫ R.partialDomainAction X Y

theorem domainAction_apply {T : V} {X Y : O}
    (f : T ⟶ R.totalObject X Y) (e : T ⟶ R.domainObject Y) :
    R.domainInverse (f ≫ R.totalι X Y) e = prod.lift f e ≫ R.domainAction X Y := by
  simp [domainAction, ← Category.assoc, ← R.partialDomainAction_apply]

/-- Internal zero morphisms, with absorption and the restriction-zero equation. -/
class Zeros where
  zero : ∀ X Y, ⊤_ V ⟶ H.hom X Y
  zero_comp : ∀ {T X Y Z} (f : T ⟶ H.hom Y Z),
    H.comp (terminal.from T ≫ zero X Y) f = terminal.from T ≫ zero X Z
  comp_zero : ∀ {T X Y Z} (f : T ⟶ H.hom X Y),
    H.comp f (terminal.from T ≫ zero Y Z) = terminal.from T ≫ zero X Z
  restriction_zero : ∀ X Y, zero X Y ≫ R.restriction X Y = zero X X

variable [R.Zeros]

def zeroAt (T : V) (X Y : O) : T ⟶ H.hom X Y := terminal.from T ≫ Zeros.zero R X Y

@[simp] theorem restrict_zero {T : V} (X Y : O) :
    R.restrict (R.zeroAt T X Y) = R.zeroAt T X X := by
  simp only [restrict, zeroAt, Category.assoc, Zeros.restriction_zero]

/-- The manuscript's internal bounded distributive lattice and stable joins on
`E_X`. Meet, top, and bottom are tied to composition, identity, and zero.
There is no global complementation hypothesis. -/
class DomainLattices where
  lattice : ∀ X T, DistribLattice (T ⟶ R.domainObject X)
  bounds : ∀ X T, BoundedOrder (T ⟶ R.domainObject X)
  precomp : ∀ {T T' X}, (T' ⟶ T) →
    BoundedLatticeHom (T ⟶ R.domainObject X) (T' ⟶ R.domainObject X)
  precomp_apply : ∀ {T T' X} (k : T' ⟶ T) (e : T ⟶ R.domainObject X), precomp k e = k ≫ e
  inf_ι : ∀ {T X} (a b : T ⟶ R.domainObject X),
    (a ⊓ b) ≫ R.domainι X = H.comp (a ≫ R.domainι X) (b ≫ R.domainι X)
  top_ι : ∀ T X, (⊤ : T ⟶ R.domainObject X) ≫ R.domainι X = H.identity X
  bot_ι : ∀ T X, (⊥ : T ⟶ R.domainObject X) ≫ R.domainι X = R.zeroAt T X X
  pull_sup : ∀ {T X Y} (f : T ⟶ H.hom X Y) (a b : T ⟶ R.domainObject Y),
    R.domainInverse f (a ⊔ b) = R.domainInverse f a ⊔ R.domainInverse f b

attribute [instance_reducible, instance] DomainLattices.lattice DomainLattices.bounds
variable [R.DomainLattices]

/-- The internal lattice carried by the domain equalizer. -/
def domainLattice (X : O) : InternalLattice V where
  obj := R.domainObject X
  lattice T := DomainLattices.lattice X T
  bounds T := DomainLattices.bounds X T
  precomp := DomainLattices.precomp
  precomp_apply := DomainLattices.precomp_apply

/-- The specified lattice order is exactly the restriction-domain order. -/
theorem domain_le_iff {T : V} {X : O} (a b : T ⟶ R.domainObject X) :
    a ≤ b ↔ H.comp (a ≫ R.domainι X) (b ≫ R.domainι X) = a ≫ R.domainι X := by
  constructor
  · intro h
    rw [← DomainLattices.inf_ι, inf_eq_left.mpr h]
  · intro h
    apply inf_eq_left.mp
    apply (cancel_mono (R.domainι X)).mp
    rw [DomainLattices.inf_ι]
    exact h

/-- The identity/zero distinction gives the required inequality of global domain bounds. -/
theorem domain_bounds_ne (X : O) (h : H.unit X ≠ Zeros.zero R X X) :
    (⊥ : ⊤_ V ⟶ R.domainObject X) ≠ ⊤ := by
  intro heq
  have he := congrArg (fun k ↦ k ≫ R.domainι X) heq
  rw [DomainLattices.bot_ι, DomainLattices.top_ι] at he
  apply h
  simpa only [zeroAt, InternalHom.identity,
    terminalIsTerminal.hom_ext (terminal.from (⊤_ V)) (𝟙 (⊤_ V)), Category.id_comp] using he.symm

/-- Meet preservation is derived from R3 and R4, not included among the extra data. -/
theorem domainInverse_inf {T : V} {X Y : O} (f : T ⟶ H.hom X Y)
    (a b : T ⟶ R.domainObject Y) :
    R.domainInverse f (a ⊓ b) = R.domainInverse f a ⊓ R.domainInverse f b := by
  apply (cancel_mono (R.domainι X)).mp
  simp only [R.domainInverse_ι, DomainLattices.inf_ι]
  have h : H.comp (R.restrict (H.comp f (a ≫ R.domainι Y))) f =
      H.comp f (a ≫ R.domainι Y) := by
    have h := R.rst_comp f (a ≫ R.domainι Y)
    change H.comp (R.restrict (H.comp f (a ≫ R.domainι Y))) f =
      H.comp f (R.restrict (a ≫ R.domainι Y)) at h
    simpa only [R.domain_condition] using h
  calc
    _ = R.restrict (H.comp
        (H.comp (R.restrict (H.comp f (a ≫ R.domainι Y))) f) (b ≫ R.domainι Y)) := by
      rw [h, R.assoc]
    _ = _ := by
      rw [R.assoc]
      exact R.rst_comp_rst (H.comp f (a ≫ R.domainι Y)) (H.comp f (b ≫ R.domainι Y))

theorem domainInverse_top {T : V} {X Y : O} (f : T ⟶ R.totalObject X Y) :
    R.domainInverse (f ≫ R.totalι X Y) (⊤ : T ⟶ R.domainObject Y) = ⊤ := by
  apply (cancel_mono (R.domainι X)).mp
  rw [R.domainInverse_ι, DomainLattices.top_ι, R.comp_id,
    R.total_condition, DomainLattices.top_ι]

theorem domainInverse_bot {T : V} {X Y : O} (f : T ⟶ H.hom X Y) :
    R.domainInverse f (⊥ : T ⟶ R.domainObject Y) = ⊥ := by
  apply (cancel_mono (R.domainι X)).mp
  rw [R.domainInverse_ι, DomainLattices.bot_ι, DomainLattices.bot_ι]
  change R.restrict (H.comp f (terminal.from T ≫ Zeros.zero R Y Y)) = R.zeroAt T X X
  rw [Zeros.comp_zero]
  exact R.restrict_zero X Y

/-- Total inverse image as a bounded lattice homomorphism on generalized domains. -/
def domainPull {T : V} {X Y : O} (f : T ⟶ R.totalObject X Y) :
    BoundedLatticeHom (T ⟶ R.domainObject Y) (T ⟶ R.domainObject X) where
  toFun := R.domainInverse (f ≫ R.totalι X Y)
  map_sup' := DomainLattices.pull_sup _
  map_inf' := R.domainInverse_inf _
  map_top' := R.domainInverse_top f
  map_bot' := R.domainInverse_bot _

/-- The required internal domain-predicate structure is derived from restriction. -/
def domainPredicates (P : R.Products) : InternalPredicates (R.totalHom P) where
  lattice := R.domainLattice
  action := R.domainAction
  pull := R.domainPull
  pull_apply := R.domainAction_apply
  pull_id {T X} a := by
    change R.domainInverse ((R.totalHom P).identity X ≫ R.totalι X X) a = a
    rw [R.total_identity_ι, R.domainInverse_id]
  pull_comp f g a := by
    change R.domainInverse ((R.totalHom P).comp f g ≫ R.totalι _ _) a =
      R.domainInverse (f ≫ R.totalι _ _) (R.domainInverse (g ≫ R.totalι _ _) a)
    rw [R.total_comp_ι, R.domainInverse_comp]

/-- Internal inseparability with the domain equalizers and totality pullbacks
constructed from the enriched restriction operations. -/
theorem enriched_internal_inseparability (products : R.Products)
    {P : InternalPredicates (R.totalHom products)}
    (D : InternalDiagonalData (R.domainPredicates products) P)
    (σ : D.RepresentationSection) :
    ∃ f : D.Sep ⟶ D.ZeroLocus,
      f ≫ equalizer.ι (⊥ : ⊤_ V ⟶ R.domainObject D.U) ⊤ =
        terminal.from D.Sep :=
  D.internal_inseparability σ

/-- The nontriviality condition is imposed on the original enriched identity and zero. -/
theorem enriched_no_global_separator (products : R.Products)
    {P : InternalPredicates (R.totalHom products)}
    (D : InternalDiagonalData (R.domainPredicates products) P)
    (σ : D.RepresentationSection) (hU : H.unit D.U ≠ Zeros.zero R D.U D.U) :
    IsEmpty (⊤_ V ⟶ D.Sep) :=
  D.no_global_separator σ (R.domain_bounds_ne D.U hU)

end EnrichedRestriction
end CategoricalEssentialIncompleteness
