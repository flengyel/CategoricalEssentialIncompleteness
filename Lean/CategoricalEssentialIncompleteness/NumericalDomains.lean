/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.NumericalCategory
public import CategoricalEssentialIncompleteness.Diagonal

/-!
# Numerical restriction domains and enumerable supports

Restriction idempotents are identified with c.e. subsets of their source.
Their lattice operations are intersection and union, and partial inverse image
is the domain of composition. On ℕ, complementary pairs are exactly recursive
sets together with their complements.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
open CategoryTheory
namespace CategoricalEssentialIncompleteness

theorem re_inter {A B : Set ℕ} (hA : REPred (· ∈ A)) (hB : REPred (· ∈ B)) :
    REPred (· ∈ A ∩ B) := by
  exact (hA.bind (hB.comp Computable.fst).to₂).of_eq fun n ↦
    Part.ext fun u ↦ by simp [Part.mem_bind_iff, Part.mem_assert_iff]

theorem re_union {A B : Set ℕ} (hA : REPred (· ∈ A)) (hB : REPred (· ∈ B)) :
    REPred (· ∈ A ∪ B) := by
  obtain ⟨k, hk, h⟩ := Partrec.merge hA hB (fun _ _ _ _ _ ↦ Subsingleton.elim _ _)
  apply hk.of_eq
  intro n
  apply Part.ext
  intro u
  rw [h]
  cases u
  simp

namespace Numerical

/-- C.e. subsets of the carrier of a numerical object. -/
def EnumerableSubset (X : Numerical) :=
  {A : Set ℕ // REPred (· ∈ A) ∧ A ⊆ X.carrier}

instance (X : Numerical) : DistribLattice (EnumerableSubset X) :=
  Subtype.distribLattice
    (fun {_ _} hA hB ↦ ⟨re_union hA.1 hB.1, Set.union_subset hA.2 hB.2⟩)
    (fun {_ _} hA hB ↦ ⟨re_inter hA.1 hB.1, Set.Subset.trans Set.inter_subset_left hA.2⟩)

instance (X : Numerical) : BoundedOrder (EnumerableSubset X) where
  top := ⟨X.carrier, X.recursive.to_re, Set.Subset.rfl⟩
  bot := ⟨∅, Partrec.none.of_eq (fun _ ↦ Part.ext fun _ ↦ by simp), Set.empty_subset _⟩
  le_top A := A.property.2
  bot_le A := Set.empty_subset _

/-- restriction idempotents in the numerical category. -/
@[ext] structure Domain (X : Numerical) where
  hom : X ⟶ X
  isDomain : RestrictionCategory.rst hom = hom

def Domain.support {X : Numerical} (e : Domain X) : Set ℕ := {n | (e.hom.val n).Dom}

theorem Domain.support_enumerable {X : Numerical} (e : Domain X) :
    REPred (· ∈ e.support) := e.hom.computable.dom_re

theorem Domain.mem_iff {X : Numerical} (e : Domain X) (n m : ℕ) :
    m ∈ e.hom.val n ↔ n ∈ e.support ∧ m = n := by
  conv_lhs => rw [← e.isDomain]
  exact mem_restrict _ _ _

def domainOfSupport {X : Numerical} (A : EnumerableSubset X) : Domain X where
  hom :=
    { val := supportIdentity A.val
      computable := supportIdentity_partrec _ A.property.1
      source := fun h ↦ A.property.2 ((mem_supportIdentity _ _ _).mp h).1
      target := by
        intro n m h
        obtain ⟨hn, rfl⟩ := (mem_supportIdentity _ _ _).mp h
        exact A.property.2 hn }
  isDomain := by
    apply Hom.ext; funext n; apply Part.ext; intro m
    change m ∈ (restrict _).val n ↔ m ∈ supportIdentity A.val n
    simp [mem_restrict]

@[simp] theorem domainOfSupport_support {X : Numerical} (A : EnumerableSubset X) :
    (domainOfSupport A).support = A.val := by
  ext n; exact supportIdentity_dom _ _

/-- The identification asserted at the start of the numerical interpretation. -/
def domainSupportEquiv (X : Numerical) : Domain X ≃ EnumerableSubset X where
  toFun e := ⟨e.support, e.support_enumerable, fun _ hn ↦ e.hom.source (Part.get_mem hn)⟩
  invFun := domainOfSupport
  left_inv e := by
    apply Domain.ext; apply Hom.ext; funext n; apply Part.ext; intro m
    exact (mem_supportIdentity _ _ _).trans (e.mem_iff n m).symm
  right_inv A := by
    apply Subtype.ext; ext n
    exact supportIdentity_dom _ _

instance (X : Numerical) : DistribLattice (Domain X) := (domainSupportEquiv X).distribLattice

instance (X : Numerical) : BoundedOrder (Domain X) where
  top := (domainSupportEquiv X).symm ⊤
  bot := (domainSupportEquiv X).symm ⊥
  le_top e := by
    change domainSupportEquiv X e ≤ domainSupportEquiv X ((domainSupportEquiv X).symm ⊤)
    rw [Equiv.apply_symm_apply]; exact le_top
  bot_le e := by
    change domainSupportEquiv X ((domainSupportEquiv X).symm ⊥) ≤ domainSupportEquiv X e
    rw [Equiv.apply_symm_apply]; exact bot_le

def domainSupportOrderIso (X : Numerical) : Domain X ≃o EnumerableSubset X where
  toEquiv := domainSupportEquiv X
  map_rel_iff' := Iff.rfl

@[simp] theorem Domain.support_inf {X : Numerical} (a b : Domain X) :
    (a ⊓ b).support = a.support ∩ b.support :=
  congrArg Subtype.val ((domainSupportOrderIso X).map_inf a b)

@[simp] theorem Domain.support_sup {X : Numerical} (a b : Domain X) :
    (a ⊔ b).support = a.support ∪ b.support :=
  congrArg Subtype.val ((domainSupportOrderIso X).map_sup a b)

@[simp] theorem Domain.support_top (X : Numerical) : (⊤ : Domain X).support = X.carrier :=
  congrArg Subtype.val ((domainSupportOrderIso X).map_top)

@[simp] theorem Domain.support_bot (X : Numerical) : (⊥ : Domain X).support = ∅ :=
  congrArg Subtype.val ((domainSupportOrderIso X).map_bot)

theorem Domain.support_injective (X : Numerical) :
    Function.Injective (Domain.support (X := X)) := fun _ _ h ↦
  (domainSupportEquiv X).injective (Subtype.ext h)

theorem Domain.le_iff {X : Numerical} (a b : Domain X) :
    a ≤ b ↔ a.hom ≫ b.hom = a.hom := by
  change a.support ⊆ b.support ↔ _
  constructor
  · intro h
    apply Hom.ext; funext n; apply Part.ext; intro m
    simp only [comp_val, Part.mem_bind_iff, a.mem_iff, b.mem_iff]
    constructor
    · rintro ⟨k, ⟨ha, rfl⟩, _, hm⟩; exact ⟨ha, hm⟩
    · rintro ⟨ha, rfl⟩; exact ⟨_, ⟨ha, rfl⟩, h ha, rfl⟩
  · intro h n hn
    have hm : n ∈ (a.hom ≫ b.hom).val n := by
      rw [h]; exact (a.mem_iff _ _).mpr ⟨hn, rfl⟩
    obtain ⟨k, hk, hb⟩ := Part.mem_bind_iff.mp hm
    obtain ⟨_, rfl⟩ := (a.mem_iff _ _).mp hk
    exact (b.mem_iff _ _).mp hb |>.1

theorem Domain.inf_hom {X : Numerical} (a b : Domain X) :
    (a ⊓ b).hom = a.hom ≫ b.hom := by
  apply Hom.ext; funext n; apply Part.ext; intro m
  simp only [comp_val, Part.mem_bind_iff, Domain.mem_iff, Domain.support_inf,
    Set.mem_inter_iff]
  constructor
  · rintro ⟨⟨ha, hb⟩, rfl⟩; exact ⟨_, ⟨ha, rfl⟩, hb, rfl⟩
  · rintro ⟨k, ⟨ha, rfl⟩, hb, hm⟩; exact ⟨⟨ha, hb⟩, hm⟩

@[simp] theorem Domain.top_hom (X : Numerical) : (⊤ : Domain X).hom = 𝟙 X := rfl

@[simp] theorem Domain.bot_hom (X : Numerical) : (⊥ : Domain X).hom = 0 := by
  apply Hom.ext; funext n; apply Part.ext; intro m
  rw [Domain.mem_iff, Domain.support_bot, zero_val]
  simp

def domainInverse {X Y : Numerical} (f : X ⟶ Y) (e : Domain Y) : Domain X where
  hom := restrict (f ≫ e.hom)
  isDomain := by
    apply Hom.ext; funext n; apply Part.ext; intro m
    change m ∈ (restrict (restrict _)).val n ↔ m ∈ (restrict _).val n
    simp [restrict]

theorem domainInverse_support {X Y : Numerical} (f : X ⟶ Y) (e : Domain Y) :
    (domainInverse f e).support = {n | ∃ m ∈ f.val n, m ∈ e.support} := by
  ext n
  change (supportIdentity _ n).Dom ↔ _
  rw [supportIdentity_dom]
  simp only [Set.mem_ofPred_eq, comp_val, Part.dom_iff_mem, Part.mem_bind_iff, e.mem_iff]
  constructor
  · rintro ⟨m, k, hk, he, _⟩; exact ⟨k, hk, he⟩
  · rintro ⟨m, hm, he⟩; exact ⟨m, m, hm, he, rfl⟩

/-- Complementarity supplies a decision procedure by Post's theorem. -/
theorem complementary_support_recursive (a : ComplementaryPair (Domain nat)) :
    ComputablePred (· ∈ a.pos.support) := by
  have hi : a.pos.support ∩ a.neg.support = ∅ := by
    rw [← Domain.support_inf, a.compl.inf_eq_bot, Domain.support_bot]
  have hu : a.pos.support ∪ a.neg.support = Set.univ := by
    rw [← Domain.support_sup, a.compl.sup_eq_top, Domain.support_top]; rfl
  apply ComputablePred.computable_iff_re_compl_re'.mpr
  refine ⟨a.pos.support_enumerable, a.neg.support_enumerable.of_eq ?_⟩
  intro n
  constructor
  · intro hn hp
    have : n ∈ a.pos.support ∩ a.neg.support := ⟨hp, hn⟩
    rw [hi] at this; exact this
  · intro hn
    have : n ∈ a.pos.support ∪ a.neg.support := by rw [hu]; trivial
    exact this.resolve_left hn

set_option backward.isDefEq.respectTransparency false in
/-- Every recursive set gives complementary restriction domains. -/
def recursivePair (A : Set ℕ) (hA : ComputablePred (· ∈ A)) :
    ComplementaryPair (Domain nat) where
  pos := domainOfSupport ⟨A, hA.to_re, Set.subset_univ _⟩
  neg := domainOfSupport ⟨Aᶜ, hA.not.to_re, Set.subset_univ _⟩
  compl := IsCompl.of_eq
    (by
      apply Domain.support_injective
      rw [Domain.support_inf, Domain.support_bot, domainOfSupport_support, domainOfSupport_support]
      exact Set.inter_compl_self _)
    (by
      apply Domain.support_injective
      rw [Domain.support_sup, Domain.support_top, domainOfSupport_support, domainOfSupport_support]
      exact Set.union_compl_self _)

@[simp] theorem recursivePair_support (A : Set ℕ) (hA : ComputablePred (· ∈ A)) :
    (recursivePair A hA).pos.support = A := by
  ext n; exact supportIdentity_dom _ _

theorem recursive_iff_complemented_support (A : Set ℕ) :
    ComputablePred (· ∈ A) ↔ ∃ a : ComplementaryPair (Domain nat), a.pos.support = A := by
  constructor
  · intro hA; exact ⟨recursivePair A hA, recursivePair_support A hA⟩
  · rintro ⟨a, rfl⟩; exact complementary_support_recursive a

end Numerical
end CategoricalEssentialIncompleteness
