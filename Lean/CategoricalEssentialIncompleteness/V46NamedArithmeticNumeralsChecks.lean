import CategoricalEssentialIncompleteness.V46NamedArithmeticNumerals
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.V46.NamedArithmeticNumerals
example : Primrec (numeralCode : ℕ → ℕ) := numeralCode_primrec
example {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] (out n : M) :
    numeralGraph.val.Evalb ![out,n] ↔ out = numeralCode n := numeralGraph_eval out n
