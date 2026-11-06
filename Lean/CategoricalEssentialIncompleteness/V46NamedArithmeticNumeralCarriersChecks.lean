import CategoricalEssentialIncompleteness.V46NamedArithmeticNumeralCarriers
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.V46.NamedArithmeticNumerals
example {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] (n : M) :
    termCarrier.val.Evalb ![numeralCode n] ∧ occurrences M (numeralCode n) = 0 :=
  numeralCode_carrier_closed n
