import CategoricalEssentialIncompleteness.V46NamedArithmeticSignature
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.V46.NamedArithmeticSignature
example : zeroSymbol.val = 0 := rfl
example : oneSymbol.val = 1 := rfl
example : addSymbol.val = 0 := rfl
example : mulSymbol.val = 1 := rfl
example : ltSymbol.val = 1 := rfl
example (n : ℕ) : (numeral n).freeVariables = [] := numeral_freeVariables n
example {M : Type} [ORingStructure M] (x : M) :
    (functionSymbols 2).val.Evalb ![x] ↔ x = 0 ∨ x = 1 := functionSymbols_two_eval x
