import CategoricalEssentialIncompleteness.V46JaniczakSignedTheory

open FFL FFL.FirstOrder FFL.Entailment
open CategoricalEssentialIncompleteness

namespace FirstReaderReconciliation

/-- Lemma 23 in Visser's terminology. Extension means inclusion of all
derivable sentences, allowing different axiom presentations. -/
theorem visser {L : Language} [Encodable (Sentence L)] (T : Theory L)
    (P N : Set ℕ) (inseparable : Numerical.RecursivelyInseparable P N)
    (assignment : ℕ → Sentence L) (computable : Computable (Encodable.encode ∘ assignment))
    (positive : ∀ n ∈ P, T ⊢ assignment n) (negative : ∀ n ∈ N, T ⊢ ∼(assignment n)) :
    ∀ U : Theory L, T ⪯ U → Entailment.Consistent U →
      ¬ ComputablePred (fun w : ℕ => ∃ p : Sentence L, Encodable.encode p = w ∧ U ⊢ p) := by
  intro U containsTheorems consistent decides
  let words (w : ℕ) := ∃ p : Sentence L, Encodable.encode p = w ∧ U ⊢ p
  let separates (n : ℕ) := words (Encodable.encode (assignment n))
  have decision : ComputablePred separates :=
    ComputablePred.computable_of_manyOneReducible
      (show ManyOneReducible separates words from ⟨_, computable, fun _ => Iff.rfl⟩) decides
  apply inseparable.2
  refine ⟨{n | separates n}, decision, ?_, Set.disjoint_left.mpr ?_⟩
  · intro n hn
    exact ⟨assignment n, rfl, containsTheorems.wk (positive n hn)⟩
  · intro n sep hn
    obtain ⟨p, equality, proved⟩ := sep
    have same : p = assignment n := Encodable.encode_inj.mp equality
    exact (consistent_iff_unprovable_bot.mp consistent)
      (neg_mdp (containsTheorems.wk (negative n hn)) (same ▸ proved))

#print axioms visser

end FirstReaderReconciliation
