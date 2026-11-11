/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.ArithmeticEnumerableSupports
public import CategoricalEssentialIncompleteness.ArithmeticInseparability

/-!
# Arithmetic essential incompleteness from recursive inseparability

A complete consistent arithmetic theory has complementary theorem and
refutation supports. If its axioms are recursively enumerable, both supports
are recursively enumerable, so the theorem support is recursive. Applied to
an extension, this recursive set separates the original theory's theorem and
refutation supports. Recursive inseparability therefore implies that every
consistent recursively enumerable extension is incomplete.

The categorical diagonal theorem supplies this inseparability whenever the
original theory strongly defines every recursive subset of the natural
numbers. In particular, it applies to consistent extensions of `PA⁻`.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic

namespace CategoricalEssentialIncompleteness
namespace ArithmeticSyntax

/-- In a complete consistent theory, refutation is the complement of provability. -/
theorem refutationSupport_eq_compl (T : ArithmeticTheory)
    [Entailment.Consistent T] [Entailment.Complete T] :
    refutationSupport T = (theoremSupport T)ᶜ := by
  ext n
  constructor
  · intro hn hp
    exact ArithmeticRepresentation.consistent_not_both T (sentenceEnumeration n) ⟨hp, hn⟩
  · intro hn
    exact (Entailment.Complete.con (𝓢 := T) (sentenceEnumeration n)).resolve_left hn

/-- A complete consistent c.e. theory has a recursive theorem support. -/
theorem theoremSupport_computable_of_complete (T : ArithmeticTheory) [T.RE]
    [Entailment.Consistent T] [Entailment.Complete T] :
    ComputablePred (· ∈ theoremSupport T) := by
  apply ComputablePred.computable_iff_re_compl_re'.mpr
  refine ⟨theoremSupport_enumerable T, ?_⟩
  have h := refutationSupport_enumerable T
  rw [refutationSupport_eq_compl T] at h
  exact h

/-- Recursive inseparability forces every consistent extension's theorem support
to be nonrecursive. -/
theorem extension_theoremSupport_not_computable_of_recursivelyInseparable
    (T T' : ArithmeticTheory) [Entailment.Consistent T']
    (hTT' : T ⪯ T')
    (hsep : Numerical.RecursivelyInseparable (theoremSupport T) (refutationSupport T)) :
    ¬ComputablePred (· ∈ theoremSupport T') := by
  intro hcomp
  apply hsep.2
  refine ⟨theoremSupport T', hcomp, theoremSupport_mono hTT', ?_⟩
  apply Set.disjoint_left.mpr
  intro n hp hn
  exact Set.disjoint_left.mp (supports_disjoint T') hp (refutationSupport_mono hTT' hn)

/-- Recursive inseparability excludes complete consistent c.e. extensions. -/
theorem extension_incomplete_of_recursivelyInseparable
    (T T' : ArithmeticTheory) [T'.RE] [Entailment.Consistent T']
    (hTT' : T ⪯ T')
    (hsep : Numerical.RecursivelyInseparable (theoremSupport T) (refutationSupport T)) :
    Entailment.Incomplete T' := by
  apply Entailment.not_complete_iff_incomplete.mp
  intro hc
  let := hc
  exact extension_theoremSupport_not_computable_of_recursivelyInseparable T T' hTT' hsep
    (theoremSupport_computable_of_complete T')

/-- Every consistent c.e. extension of a consistent theory strongly defining
all recursive sets is incomplete. -/
theorem extension_incomplete_of_definability
    (T T' : ArithmeticTheory) [Entailment.Consistent T]
    [T'.RE] [Entailment.Consistent T'] (hTT' : T ⪯ T')
    (hdef : ∀ A : Set ℕ, ComputablePred (· ∈ A) →
      ∃ φ : ArithmeticSemisentence 1,
        ArithmeticRepresentation.StrongNumeralwise T (· ∈ A) φ) :
    Entailment.Incomplete T' :=
  extension_incomplete_of_recursivelyInseparable T T' hTT'
    (supports_recursivelyInseparable_of_definability T hdef)

/-- Every consistent extension of a theory strongly defining all recursive
sets has a nonrecursive theorem support. -/
theorem essential_undecidability_of_definability
    (T : ArithmeticTheory) [Entailment.Consistent T]
    (hdef : ∀ A : Set ℕ, ComputablePred (· ∈ A) →
      ∃ φ : ArithmeticSemisentence 1,
        ArithmeticRepresentation.StrongNumeralwise T (· ∈ A) φ) :
    ∀ T' : ArithmeticTheory, T ⪯ T' → Entailment.Consistent T' →
      ¬ComputablePred (· ∈ theoremSupport T') := by
  intro T' hTT' hCon
  let := hCon
  exact extension_theoremSupport_not_computable_of_recursivelyInseparable T T' hTT'
    (supports_recursivelyInseparable_of_definability T hdef)

/-- Strong numeralwise definability implies arithmetic essential incompleteness. -/
theorem essential_incompleteness_of_definability
    (T : ArithmeticTheory) [Entailment.Consistent T]
    (hdef : ∀ A : Set ℕ, ComputablePred (· ∈ A) →
      ∃ φ : ArithmeticSemisentence 1,
        ArithmeticRepresentation.StrongNumeralwise T (· ∈ A) φ) :
    ∀ T' : ArithmeticTheory, T ⪯ T' → T'.RE →
      Entailment.Consistent T' → Entailment.Incomplete T' := by
  intro T' hTT' hRE hCon
  let := hRE
  let := hCon
  exact extension_incomplete_of_definability T T' hTT' hdef

/-- Every consistent c.e. extension of a consistent extension of `PA⁻` is incomplete. -/
theorem extension_incomplete_of_PAminus
    (T T' : ArithmeticTheory) [𝗣𝗔⁻ ⪯ T] [Entailment.Consistent T]
    [T'.RE] [Entailment.Consistent T'] (hTT' : T ⪯ T') :
    Entailment.Incomplete T' :=
  extension_incomplete_of_recursivelyInseparable T T' hTT'
    (supports_recursivelyInseparable T)

/-- Every consistent c.e. extension of `PA⁻` is incomplete. -/
theorem incomplete_of_PAminus (T : ArithmeticTheory)
    [𝗣𝗔⁻ ⪯ T] [T.RE] [Entailment.Consistent T] :
    Entailment.Incomplete T :=
  extension_incomplete_of_PAminus T T inferInstance

end ArithmeticSyntax
end CategoricalEssentialIncompleteness
