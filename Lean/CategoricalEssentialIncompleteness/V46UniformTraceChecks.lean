import CategoricalEssentialIncompleteness.V46UniformTrace

/-! Uniform arithmetic index variables in the evaluator graph. -/
noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open FailureOfComposition.ProofSearch FailureOfComposition.ConcreteEvaluator
open CategoricalEssentialIncompleteness.V46

example : 𝗣𝗔 ⊢ UniformTrace.functionalitySentence := UniformTrace.functionality_PA
example : 𝗣𝗔 ⊢ UniformTrace.universalSentence := UniformTrace.universal_PA
example (e : ℕ) : 𝗣𝗔 ⊢ UniformTrace.sectionSentence e := UniformTrace.section_PA e
example : Uniform 𝗣𝗔 (eventualGraph UniformTrace.universalIndex) UniformTrace.universalGraph :=
  UniformTrace.universalIndex_uniform

example {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] (e x y z : M)
    (hy : UniformTrace.graph.val.Evalb ![e, x, y])
    (hz : UniformTrace.graph.val.Evalb ![e, x, z]) : y = z :=
  UniformTrace.output_unique e x y z hy hz

example {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] (e x y : M) :
    UniformTrace.graph.val.Evalb
        ![(UniformTrace.universalIndex : M), ExponentialPairing.code e x, y] ↔
      UniformTrace.graph.val.Evalb ![e, x, y] := UniformTrace.universal_eval e x y
