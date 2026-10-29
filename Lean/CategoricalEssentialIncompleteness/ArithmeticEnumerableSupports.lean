/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.ArithmeticSupports
import Foundation.FirstOrder.Arithmetic.Bootstrapping.Syntax.CraigTrick
import Foundation.FirstOrder.Arithmetic.Bootstrapping.DerivabilityCondition.D1

/-!
# Enumerable theorem and refutation supports

A recursively enumerable set of arithmetic axioms has recursively enumerable
theorem and refutation supports. The proof uses Craig's primitive recursive
axiomatization and its equivalence with the original theory. The corresponding
partial identities are numerical restriction domains.
-/

set_option autoImplicit false
noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping

namespace CategoricalEssentialIncompleteness
namespace ArithmeticSyntax

/-- The indices of theorems of a c.e. arithmetic theory form a c.e. set. -/
theorem theoremSupport_enumerable (T : ArithmeticTheory) [T.RE] :
    REPred (· ∈ theoremSupport T) := by
  have h : REPred (Provable T.craig (V := ℕ)) :=
    rePred_iff_sigma1.mpr inferInstance
  apply (h.comp sentenceCodeEnumeration_computable).of_eq
  intro b
  rw [← encode_sentenceEnumeration, ← Sentence.quote_eq_encode_nat,
    provable_iff_provable]
  exact ⟨fun h => (inferInstance : T.craig ⪯ T).wk h,
    fun h => (inferInstance : T ⪯ T.craig).wk h⟩

/-- The indices of refutable sentences of a c.e. arithmetic theory form a c.e. set. -/
theorem refutationSupport_enumerable (T : ArithmeticTheory) [T.RE] :
    REPred (· ∈ refutationSupport T) := by
  have hDef : 𝚺₁-Predicate fun a : ℕ => Provable T.craig (neg ℒₒᵣ a) := by
    definability
  have h := (rePred_iff_sigma1.mpr hDef).comp sentenceCodeEnumeration_computable
  apply h.of_eq
  intro b
  have hNeg : neg ℒₒᵣ (sentenceCodeEnumeration b) =
      (⌜∼(sentenceEnumeration b)⌝ : ℕ) := by
    rw [← encode_sentenceEnumeration, ← Sentence.quote_eq_encode_nat]
    simp [Sentence.quote_def, Semiformula.quote_def]
  rw [hNeg, provable_iff_provable]
  exact ⟨fun h => (inferInstance : T.craig ⪯ T).wk h,
    fun h => (inferInstance : T ⪯ T.craig).wk h⟩

/-- The partial identity on the theorem support. -/
def theoremDomain (T : ArithmeticTheory) [T.RE] : Numerical.Domain Numerical.nat :=
  Numerical.domainOfSupport ⟨theoremSupport T, theoremSupport_enumerable T,
    Set.subset_univ _⟩

/-- The partial identity on the refutation support. -/
def refutationDomain (T : ArithmeticTheory) [T.RE] : Numerical.Domain Numerical.nat :=
  Numerical.domainOfSupport ⟨refutationSupport T, refutationSupport_enumerable T,
    Set.subset_univ _⟩

@[simp] theorem theoremDomain_support (T : ArithmeticTheory) [T.RE] :
    (theoremDomain T).support = theoremSupport T :=
  Numerical.domainOfSupport_support _

@[simp] theorem refutationDomain_support (T : ArithmeticTheory) [T.RE] :
    (refutationDomain T).support = refutationSupport T :=
  Numerical.domainOfSupport_support _

@[simp] theorem theoremDomain_predicate (T : ArithmeticTheory) [T.RE] :
    Numerical.domainSubobject Numerical.nat (theoremDomain T) = theoremPredicate T := by
  change NumericalPER.supportSubobject (theoremDomain T).support _ =
    NumericalPER.supportSubobject (theoremSupport T) _
  exact (NumericalPER.supportSubobject_eq_iff _ _).mpr (theoremDomain_support T)

@[simp] theorem refutationDomain_predicate (T : ArithmeticTheory) [T.RE] :
    Numerical.domainSubobject Numerical.nat (refutationDomain T) = refutationPredicate T := by
  change NumericalPER.supportSubobject (refutationDomain T).support _ =
    NumericalPER.supportSubobject (refutationSupport T) _
  exact (NumericalPER.supportSubobject_eq_iff _ _).mpr (refutationDomain_support T)

end ArithmeticSyntax
end CategoricalEssentialIncompleteness
