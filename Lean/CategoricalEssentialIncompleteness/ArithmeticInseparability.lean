/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.ArithmeticRepresentationSection

/-!
# Arithmetic recursive inseparability from the internal diagonal theorem

The representation section makes the internal separator object have no global
points. A recursive separator of theorem and refutation indices would define
such a global point. Hence strong numeralwise definability of all recursive
sets implies recursive inseparability of those two sets of indices.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open CategoryTheory CategoryTheory.Limits
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace CategoricalEssentialIncompleteness
namespace ArithmeticSyntax

attribute [local instance] typeHomDistribLattice typeHomBoundedOrder

/-- A numerical separator is a constant global separator of the internal predicates. -/
theorem globalDomainPair_separates_iff (T : ArithmeticTheory) [Entailment.Consistent T]
    (a : ComplementaryPair (Numerical.Domain Numerical.nat)) :
    (internalDiagonalData T).Separates (globalDomainPair a) ↔
      Numerical.SeparatesSupports (theoremSupport T) (refutationSupport T) a := by
  change (_ ≤ _ ∧ _ ≤ _) ↔ (_ ≤ _ ∧ _ ≤ _)
  constructor
  · rintro ⟨hp, hn⟩
    constructor
    · have h := (Numerical.predicateSubobjectIdentification.app
        (Numerical.totalObject Numerical.nat)).monotone (hp default)
      change NumericalPER.supportSubobject (theoremSupport T) _ ≤
        Numerical.domainSubobject Numerical.nat
        (Numerical.enrichedDomainEquiv Numerical.nat
          ((Numerical.enrichedDomainEquiv Numerical.nat).symm a.pos)) at h
      simpa only [Equiv.apply_symm_apply] using h
    · have h := (Numerical.predicateSubobjectIdentification.app
        (Numerical.totalObject Numerical.nat)).monotone (hn default)
      change NumericalPER.supportSubobject (refutationSupport T) _ ≤
        Numerical.domainSubobject Numerical.nat
        (Numerical.enrichedDomainEquiv Numerical.nat
          ((Numerical.enrichedDomainEquiv Numerical.nat).symm a.neg)) at h
      simpa only [Equiv.apply_symm_apply] using h
  · rintro ⟨hp, hn⟩
    constructor
    · intro t
      change theoremPredicate T ≤ Numerical.domainSubobject Numerical.nat
        (Numerical.enrichedDomainEquiv Numerical.nat
          ((Numerical.enrichedDomainEquiv Numerical.nat).symm a.pos))
      erw [Equiv.apply_symm_apply]
      exact (Numerical.predicateSubobjectIdentification.app
        (Numerical.totalObject Numerical.nat)).symm.monotone hp
    · intro t
      change refutationPredicate T ≤ Numerical.domainSubobject Numerical.nat
        (Numerical.enrichedDomainEquiv Numerical.nat
          ((Numerical.enrichedDomainEquiv Numerical.nat).symm a.neg))
      erw [Equiv.apply_symm_apply]
      exact (Numerical.predicateSubobjectIdentification.app
        (Numerical.totalObject Numerical.nat)).symm.monotone hn

/-- The arithmetic representation section excludes every numerical domain separator. -/
theorem no_separator_of_representationSection (T : ArithmeticTheory)
    [Entailment.Consistent T] (σ : (internalDiagonalData T).RepresentationSection) :
    ¬ ∃ a : ComplementaryPair (Numerical.Domain Numerical.nat),
      Numerical.SeparatesSupports (theoremSupport T) (refutationSupport T) a := by
  have hEmpty := Numerical.enrichedRestriction.enriched_no_global_separator
    Numerical.enrichedProducts (internalDiagonalData T) σ Numerical.enriched_nat_nontrivial
  rintro ⟨a, ha⟩
  exact hEmpty.false ((internalDiagonalData T).liftSeparator (globalDomainPair a)
    ((globalDomainPair_separates_iff T a).mpr ha))

/-- Strong numeralwise definability of all recursive sets implies recursive
inseparability of theorem and refutation indices. -/
theorem supports_recursivelyInseparable_of_definability (T : ArithmeticTheory)
    [Entailment.Consistent T]
    (hdef : ∀ A : Set ℕ, ComputablePred (· ∈ A) →
      ∃ φ : ArithmeticSemisentence 1,
        ArithmeticRepresentation.StrongNumeralwise T (· ∈ A) φ) :
    Numerical.RecursivelyInseparable (theoremSupport T) (refutationSupport T) := by
  apply (Numerical.no_separator_iff_recursively_inseparable
    (theoremSupport T) (refutationSupport T) (supports_disjoint T)).mp
  exact no_separator_of_representationSection T (representationSectionOfDefinability T hdef)

/-- The theorem and refutation indices of every consistent extension of `PA⁻`
are recursively inseparable. -/
theorem supports_recursivelyInseparable (T : ArithmeticTheory) [𝗣𝗔⁻ ⪯ T]
    [Entailment.Consistent T] :
    Numerical.RecursivelyInseparable (theoremSupport T) (refutationSupport T) := by
  apply (Numerical.no_separator_iff_recursively_inseparable
    (theoremSupport T) (refutationSupport T) (supports_disjoint T)).mp
  exact no_separator_of_representationSection T (representationSection T)

end ArithmeticSyntax
end CategoricalEssentialIncompleteness
