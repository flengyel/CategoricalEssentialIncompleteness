import CategoricalEssentialIncompleteness.V46NumericalStableLists

/-! Stable initiality in the actual numerical total category and all its slices. -/

noncomputable section
open CategoryTheory CategoryTheory.Limits
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoricalEssentialIncompleteness.LocalConnectedness
open CategoricalEssentialIncompleteness.V46
open NumericalStableLists

example : PreservesRestriction StandardTrueTheory.comparison := standardComparison_preserves
example : SyntacticPredicates.TotalSplit 𝗧𝗔 ≌ NumericalTuples.Object := numericalEquivalence
example (V : NumericalTuples.Object) : StableListAlgebra V := stableListAlgebra V

example (V : NumericalTuples.Object) :
    IsInitial (stableListAlgebra V).algebra.asAlgebra := (stableListAlgebra V).initial

example (V P : NumericalTuples.Object) :
    IsInitial ((stableListAlgebra V).algebra.withParameters P).asAlgebra :=
  (stableListAlgebra V).stable P
