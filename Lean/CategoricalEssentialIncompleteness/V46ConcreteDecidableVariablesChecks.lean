import CategoricalEssentialIncompleteness.V46ConcreteDecidableVariables

/-! Concrete internal equality in the syntactic total and literal numerical categories. -/
noncomputable section
open CategoryTheory CategoryTheory.Limits
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoricalEssentialIncompleteness.V46
variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]

example (V : SyntacticPredicates.TotalSplit T) : DecidableVariables V :=
  ConcreteDecidableVariables.total T V

example (V : NumericalTuples.Object) : DecidableVariables V :=
  ConcreteDecidableVariables.numerical V

example (V : NumericalTuples.Object) :
    IsPullback (prod.lift (𝟙 V) (𝟙 V)) (terminal.from V)
      (ConcreteDecidableVariables.numerical V).test
      (coprod.inr : ⊤_ NumericalTuples.Object ⟶
        (⊤_ NumericalTuples.Object) ⨿ (⊤_ NumericalTuples.Object)) :=
  (ConcreteDecidableVariables.numerical V).diagonal
