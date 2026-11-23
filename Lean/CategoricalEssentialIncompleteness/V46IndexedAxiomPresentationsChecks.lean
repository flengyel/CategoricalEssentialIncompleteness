/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46IndexedAxiomPresentations

/-! # Numeral fibers of the indexed PA axiom predicate in §8.2 -/

@[expose] public section
noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
namespace CategoricalEssentialIncompleteness.V46.IndexedAxiomPresentations.Checks
open ArithmeticIndexedAxioms ArithmeticIndexedPAEnumeration

/-- Two numeral indices have the chosen PA axioms as their standard extension, whereas
the universal equivalence of the two binary-predicate instances has no PA proof. -/
theorem indexed_axiom_presentations :
    let Ax := axiomGraph axiomCodes
    ∃ e d : ℕ, e ≠ d ∧
      (∀ w : ℕ, Ax.val.Evalb ![e,w] ↔ axiomCodes.val.Evalb ![w]) ∧
      (∀ w : ℕ, Ax.val.Evalb ![d,w] ↔ axiomCodes.val.Evalb ![w]) ∧
      ¬ 𝗣𝗔 ⊢ “∀ z, !Ax.val !!e z ↔ !Ax.val !!d z” := by
  let Ax := axiomGraph axiomCodes
  have hf (k w : ℕ) : Ax.val.Evalb ![k,w] ↔ w ∈ standardAxioms k := by
    simp [Ax, standardAxioms, axiomPredicate, fiberAxioms, numeral_eq_natCast_app]
  obtain ⟨e, hne, heq, hnot⟩ := equal_standard_axioms_unprovable
  let d := FailureOfComposition.Kleene.emptyIndex
  refine ⟨e,d,hne,fun w => (hf e w).trans ?_, fun w => (hf d w).trans (emptyIndex_axioms w), ?_⟩
  · rw [heq, emptyIndex_axioms]
  · intro h
    apply hnot
    apply complete.{0} 𝗣𝗔
    intro M _ _
    have hM := consequence_iff.mp (Theory.Proof.sound h) M inferInstance
    simpa [models_iff, equivalenceSentence, axiomPredicate, fiberAxioms, Ax, d] using hM

end CategoricalEssentialIncompleteness.V46.IndexedAxiomPresentations.Checks

#print axioms CategoricalEssentialIncompleteness.V46.IndexedAxiomPresentations.Checks.indexed_axiom_presentations
