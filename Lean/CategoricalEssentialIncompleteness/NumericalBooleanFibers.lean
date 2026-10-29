/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.NumericalBooleanArrows

/-!
# Fibers of numerical Boolean arrows

The fibers of a total recursive Boolean function are its recursive inverse
images of the two values. Every recursive subset of the natural numbers
is the upper fiber of such an arrow.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness
namespace NumericalPER

/-- The categorical fiber of a recursive Boolean function is its support inclusion. -/
theorem booleanArrow_boundFiber (f : ℕ → Bool) (hf : Computable f) (b : Bool) :
    boundFiber (booleanArrow f hf) (booleanPoint b) =
      supportSubobject {n | f n = b} (Set.subset_univ _) := by
  rw [PresentationLemmas.boundFiber_eq_pullback, booleanPoint_subobject]
  change (Subobject.pullback (ofRepresentative (booleanRepresentative f hf))).obj
      (supportSubobject {b.toNat} _) = _
  rw [supportSubobject_pullback]
  apply (supportSubobject_eq_iff _ _).mpr
  ext n
  simp only [inverseSupport, booleanRepresentative, Set.mem_ofPred_eq, Set.mem_univ,
    true_and, Part.mem_some_iff, Set.mem_singleton_iff, exists_eq_left]
  cases f n <;> cases b <;> decide

/-- Each truth-value fiber of a recursive Boolean function is recursive. -/
theorem boolean_fiber_recursive (f : ℕ → Bool) (hf : Computable f) (b : Bool) :
    ComputablePred (fun n ↦ f n = b) :=
  ((Primrec.eq.decide.to_comp).comp hf (Computable.const b)).computablePred

/-- Every fiber of an arrow to the Boolean PER is a recursive support inclusion. -/
theorem boolean_fiber_is_recursive_support
    (f : discrete Set.univ ⟶ boolean) (b : Bool) :
    ∃ A : Set ℕ, ComputablePred (· ∈ A) ∧
      boundFiber f (booleanPoint b) = supportSubobject A (Set.subset_univ _) := by
  obtain ⟨g, hg, rfl⟩ := booleanArrow_surjective f
  exact ⟨{n | g n = b}, boolean_fiber_recursive g hg b, booleanArrow_boundFiber g hg b⟩

/-- A recursive support inclusion is the upper fiber of a Boolean arrow. -/
theorem recursive_support_is_boolean_fiber (A : Set ℕ)
    (hA : ComputablePred (· ∈ A)) :
    ∃ f : discrete Set.univ ⟶ boolean,
      boundFiber f (booleanPoint true) = supportSubobject A (Set.subset_univ _) := by
  obtain ⟨g, hg, he⟩ := ComputablePred.computable_iff.mp hA
  refine ⟨booleanArrow g hg, ?_⟩
  rw [booleanArrow_boundFiber]
  apply (supportSubobject_eq_iff _ _).mpr
  ext n
  exact (congrFun he n).symm.to_iff

/-- The upper fibers of Boolean arrows are exactly the recursive support inclusions. -/
theorem exists_boolean_fiber_iff_recursive_support (A : Subobject (discrete Set.univ)) :
    (∃ f : discrete Set.univ ⟶ boolean, boundFiber f (booleanPoint true) = A) ↔
      ∃ D : Set ℕ, ComputablePred (· ∈ D) ∧ supportSubobject D (Set.subset_univ _) = A := by
  constructor
  · rintro ⟨f, hf⟩
    obtain ⟨D, hD, hd⟩ := boolean_fiber_is_recursive_support f true
    exact ⟨D, hD, hd.symm.trans hf⟩
  · rintro ⟨D, hD, rfl⟩
    exact recursive_support_is_boolean_fiber D hD

end NumericalPER
end CategoricalEssentialIncompleteness
