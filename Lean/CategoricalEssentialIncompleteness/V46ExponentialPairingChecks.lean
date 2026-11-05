import CategoricalEssentialIncompleteness.V46ExponentialPairing

/-! The printed exponential pairing has provable inverse equations in PA. -/
noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoricalEssentialIncompleteness.V46.ExponentialPairing

example : 𝗣𝗔 ⊢ totalSentence := total_PA
example : 𝗣𝗔 ⊢ inverseSentence := inverse_PA

variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

example (a b : M) : code a b = Exp.exp a * (2 * b + 1) - 1 := rfl
example (n a b : M) : graph.val.Evalb ![n, a, b] ↔ n = code a b := graph_eval n a b
example (n : M) : ∃ a b : M, n = code a b := code_surjective n
example (n : M) : ∃! p : M × M, graph.val.Evalb ![n, p.1, p.2] :=
  graph_inverse_existsUnique n
example {a b c d : M} (h : code a b = code c d) : a = c ∧ b = d := code_injective h
