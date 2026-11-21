/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.NumericalPredicates
public import CategoricalEssentialIncompleteness.ComplementedSubobjects
public import CategoricalEssentialIncompleteness.NumericalBooleanFibers

/-!
# Complemented numerical subobjects

The complemented subobjects of the equality PER on `ℕ` are exactly the recursive
support inclusions. Equivalently, they are the upper fibers of Boolean morphisms, or
the images of complemented numerical restriction domains.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness
namespace NumericalPER

/-- A complemented subobject of `D_ℕ` is exactly an upper Boolean fiber. -/
theorem isComplemented_iff_boolean_fiber (A : Subobject (discrete Set.univ)) :
    IsComplemented A ↔
      ∃ f : discrete Set.univ ⟶ boolean, boundFiber f (booleanPoint true) = A := by
  rw [isComplemented_iff_exists_characteristic]
  constructor
  · rintro ⟨f, hf⟩
    refine ⟨f ≫ booleanIso.hom, ?_⟩
    rw [← booleanIso_point, boundFiber_mono_postcomp, hf]
  · rintro ⟨f, hf⟩
    refine ⟨f ≫ booleanIso.inv, ?_⟩
    have hp : booleanPoint true ≫ booleanIso.inv = Two.point true := by
      rw [← booleanIso_point, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    rw [← hp, boundFiber_mono_postcomp, hf]

/-- The complemented subobjects of `D_ℕ` are precisely the recursive support inclusions. -/
theorem isComplemented_iff_recursive_support (A : Subobject (discrete Set.univ)) :
    IsComplemented A ↔ ∃ D : Set ℕ, ComputablePred (· ∈ D) ∧
      supportSubobject D (Set.subset_univ D) = A :=
  (isComplemented_iff_boolean_fiber A).trans
    (exists_boolean_fiber_iff_recursive_support A)

end NumericalPER
namespace Numerical

/-- The positive domain of a recursive pair represents the given support inclusion. -/
theorem domainSubobject_recursivePair (A : Set ℕ) (hA : ComputablePred (· ∈ A)) :
    domainSubobject nat (recursivePair A hA).pos =
      NumericalPER.supportSubobject A (Set.subset_univ A) := by
  change NumericalPER.supportSubobject (recursivePair A hA).pos.support _ = _
  apply (NumericalPER.supportSubobject_eq_iff _ _).mpr
  exact recursivePair_support A hA

/-- A numerical restriction domain on `ℕ` is complemented exactly when its support is recursive. -/
theorem isComplemented_domain_iff_recursive_support (e : Domain nat) :
    IsComplemented e ↔ ComputablePred (· ∈ e.support) := by
  constructor
  · rintro ⟨d, hd⟩
    exact complementary_support_recursive ⟨e, d, hd⟩
  · intro h
    have he : (recursivePair e.support h).pos = e :=
      Domain.support_injective nat (recursivePair_support e.support h)
    have hc := (recursivePair e.support h).compl
    rw [he] at hc
    exact ⟨(recursivePair e.support h).neg, hc⟩

/-- A recursive support inclusion is a complemented PER subobject. -/
theorem recursive_support_isComplemented (A : Set ℕ) (hA : ComputablePred (· ∈ A)) :
    IsComplemented (NumericalPER.supportSubobject A (Set.subset_univ A)) := by
  rw [← domainSubobject_recursivePair A hA]
  exact ⟨domainSubobject nat (recursivePair A hA).neg,
    (domainSubobject_isCompl_iff _ _).mpr (recursivePair A hA).compl⟩

/-- Complemented numerical subobjects are exactly images of complemented restriction domains. -/
theorem isComplemented_iff_represented_domain
    (A : Subobject (NumericalPER.discrete Set.univ)) :
    IsComplemented A ↔ ∃ a : ComplementaryPair (Domain nat),
      domainSubobject nat a.pos = A := by
  constructor
  · intro h
    obtain ⟨D, hD, hA⟩ := (NumericalPER.isComplemented_iff_recursive_support A).mp h
    exact ⟨recursivePair D hD, (domainSubobject_recursivePair D hD).trans hA⟩
  · rintro ⟨a, rfl⟩
    exact ⟨domainSubobject nat a.neg, (domainSubobject_isCompl_iff _ _).mpr a.compl⟩

/-- The domain embedding reflects the existence of a complement on `ℕ`. -/
theorem isComplemented_domainSubobject_iff (e : Domain nat) :
    IsComplemented (domainSubobject nat e) ↔ IsComplemented e := by
  constructor
  · intro h
    obtain ⟨a, ha⟩ := (isComplemented_iff_represented_domain _).mp h
    have he : a.pos = e := (domainSubobject nat).injective ha
    exact ⟨a.neg, he ▸ a.compl⟩
  · rintro ⟨d, hd⟩
    exact ⟨domainSubobject nat d, (domainSubobject_isCompl_iff _ _).mpr hd⟩

end Numerical
namespace NumericalPER

/-- A support inclusion in `D_ℕ` is complemented exactly when its support is recursive. -/
theorem supportSubobject_isComplemented_iff (A : Set ℕ) :
    IsComplemented (supportSubobject A (Set.subset_univ A)) ↔ ComputablePred (· ∈ A) := by
  constructor
  · intro h
    obtain ⟨D, hD, he⟩ := (isComplemented_iff_recursive_support _).mp h
    have hDA := (supportSubobject_eq_iff _ _).mp he
    rwa [← hDA]
  · exact Numerical.recursive_support_isComplemented A

end NumericalPER
end CategoricalEssentialIncompleteness
