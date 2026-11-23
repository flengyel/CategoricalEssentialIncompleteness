/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46JaniczakNativeDecision
public import CategoricalEssentialIncompleteness.V46JaniczakCraig

/-! # Janiczak's signed theory of a single equivalence relation

For a disjoint computably enumerable pair, the fixed class-size axioms give
a consistent recursively axiomatizable theory. Its essential undecidability
in Foundation's classical first-order proof calculus is equivalent to recursive
inseparability of the given pair. This is the numerical antecedent cited in
§1, from Murwanashyaka, Pakhomov and Visser, §4.4, p. 1169.
-/

@[expose] public section

set_option autoImplicit false

open FFL FFL.FirstOrder

namespace Janiczak.FOL

theorem signed_consistent_iff {P N : Set ℕ} :
    Entailment.Consistent (theory (Signed P N)) ↔ Disjoint P N := by
  rw [← consistent_iff]
  constructor
  · intro hc
    apply Set.disjoint_left.mpr
    intro i hp hn
    exact Consequence.compatible hc (Consequence.of_mem (Signed.pos hp))
      (Consequence.of_mem (Signed.neg hn))
  · exact Canonical.consistent_signed

/-- The same-language complete theory associated with a recursive separator
gives a consistent extension with recursive native theorem words. -/
theorem decidable_native_extension {P N C : Set ℕ} (hp : P ⊆ C) (hn : Disjoint C N)
    (hc : ComputablePred (· ∈ C)) :
    ∃ U : Theory L, theory (Signed P N) ⊆ U ∧ Entailment.Consistent U ∧
      ComputablePred (· ∈ TheoremWords U) :=
  ⟨NativeInput.completeTheory C,NativeInput.completeTheory_extends hp hn,
    NativeInput.completeTheory_consistent C,NativeInput.computable_completeTheory_words hc⟩

/-- For a disjoint pair the theory is essentially undecidable exactly when
the two sets of finite class sizes are recursively inseparable. -/
theorem signed_essentiallyUndecidable_iff {P N : Set ℕ} (hdis : Disjoint P N) :
    EssentiallyUndecidable (theory (Signed P N)) ↔
      CategoricalEssentialIncompleteness.Numerical.RecursivelyInseparable P N := by
  refine ⟨fun h ↦ ⟨hdis,?_⟩, essentiallyUndecidable_of_inseparable⟩
  rintro ⟨C,hc,hp,hn⟩
  obtain ⟨U,he,hu,hd⟩ := decidable_native_extension hp hn hc
  exact h U he hu hd

/-- A disjoint c.e. pair gives the consistent, recursively axiomatizable
first-order theory and the essential-undecidability biconditional cited in §1. -/
theorem signed_janiczak {P N : Set ℕ} (hd : Disjoint P N)
    (hp : REPred (· ∈ P)) (hn : REPred (· ∈ N)) :
    Entailment.Consistent (theory (Signed P N)) ∧
      REPred (· ∈ Encodable.encode '' theory (Signed P N)) ∧
      (∃ U : Theory L, PrimrecPred (fun w : ℕ ↦ w ∈ Encodable.encode '' U) ∧
        ∀ φ : Sentence L, (U ⊢ φ ↔ theory (Signed P N) ⊢ φ)) ∧
      (EssentiallyUndecidable (theory (Signed P N)) ↔
        CategoricalEssentialIncompleteness.Numerical.RecursivelyInseparable P N) :=
  ⟨signed_consistent_iff.mpr hd,signed_axiom_words_enumerable hp hn,
    signed_recursively_axiomatizable hp hn,signed_essentiallyUndecidable_iff hd⟩

end Janiczak.FOL
