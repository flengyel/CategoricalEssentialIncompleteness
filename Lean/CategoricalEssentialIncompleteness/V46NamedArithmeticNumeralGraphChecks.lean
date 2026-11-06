import CategoricalEssentialIncompleteness.V46NamedArithmeticNumeralGraph
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.V46
open CategoricalEssentialIncompleteness.V46.NamedArithmeticNumerals
example : SyntacticPredicates.GraphMorphism 𝗣𝗔 NamedArithmeticSignature.variableSymbols closedTermCarrier := numeralMorphism
example (n : ℕ) : numeralCode n = NamedArithmeticSignature.termCode (NamedArithmeticSignature.numeral n) :=
  numeralCode_standard n
