/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46UniformTracePrimitiveCoding
import CategoricalEssentialIncompleteness.V46UniformTraceSpecializers
import CategoricalEssentialIncompleteness.V46UniformTraceComparison

/-! # The actual arithmetized-evaluation package for Lemma 5.1 -/

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment

namespace CategoricalEssentialIncompleteness.V46.UniformTrace

/-- All named functions and programs in this statement are the concrete
constructions in the preceding modules. No enumeration, composition,
specialization or evaluator conclusion is supplied as a hypothesis. -/
theorem arithmetized_evaluation :
    Nat.Primrec (fun n : ℕ =>
      traceCheck n.unpair.1 n.unpair.2.unpair.1 n.unpair.2.unpair.2) ∧
    PrimrecPred (fun p : ℕ × ℕ × ℕ => traceFormula.val.Evalb ![p.1,p.2.1,p.2.2]) ∧
    Nat.Primrec (out : ℕ → ℕ) ∧
    (𝗣𝗔 ⊢ traceProgramComparisonSentence) ∧
    (𝗣𝗔 ⊢ primitiveTraceGraphSentence) ∧
    (𝗣𝗔 ⊢ traceProgramTotalitySentence) ∧
    (𝗣𝗔 ⊢ functionalitySentence) ∧
    (𝗣𝗔 ⊢ universalSentence) ∧
    Nat.Primrec (Nat.unpaired (specialize : ℕ → ℕ → ℕ)) ∧
    Nat.Primrec (Nat.unpaired (compose : ℕ → ℕ → ℕ)) ∧
    (𝗣𝗔 ⊢ buildersTotalitySentence) ∧
    (𝗣𝗔 ⊢ specializationSentence) ∧
    (𝗣𝗔 ⊢ compositionSentence) ∧
    (∀ e : ℕ, (𝗣𝗔 ⊢ specializerSectionSentence e) ∧
      (𝗣𝗔 ⊢ specializerSectionTotalitySentence e)) := by
  exact ⟨traceCheck_natPrimrec, trace_primrec, out_natPrimrec,
    traceProgram_comparison_PA, primitive_trace_graph_PA,
    traceProgram_totality_PA, functionality_PA, universal_PA, specialize_natPrimrec,
    compose_natPrimrec, builders_totality_PA, specialization_PA, composition_PA,
    fun e => ⟨specializerSection_PA e, specializerSection_totality_PA e⟩⟩

end CategoricalEssentialIncompleteness.V46.UniformTrace
