import CategoricalEssentialIncompleteness.V46NumericalUnderlyingCoproducts
noncomputable section
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46

example : PreservesColimit (Functor.empty.{0} NumericalTuples.Object) NumericalUnderlying.functor :=
  inferInstance

example (n : ℕ) : PreservesColimitsOfShape (Discrete (Fin n)) NumericalUnderlying.functor :=
  inferInstance

example : IsEmpty (NumericalTuples.Point (⊥_ NumericalTuples.Object)) := inferInstance
