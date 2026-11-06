import CategoricalEssentialIncompleteness.V46NamedArithmeticQuantifierOccurrences
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.V46
open SyntacticPredicates SyntacticSyntax NamedPostfixEncoding
example {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (σ π : ℕ → Carrier) (d : ℕ) (name body : M)
    (hn : variableCarrier.val.Evalb ![name])
    (hb : (Postfix.carrier true (termPolynomial σ d) (formulaPolynomial π d)).val.Evalb ![body]) :
    ConcreteNamedSubstitution.freeVariables variableCarrier σ π d
      (Coding.constructor true (formulaPolynomial π d)
        (NamedArithmeticModelCoding.allInput name body)) =
      ConcreteNamedSubstitution.delete name
        (ConcreteNamedSubstitution.freeVariables variableCarrier σ π d body) :=
  NamedArithmeticQuantifierOccurrences.quantifier_occurrences σ π d name body hn hb
