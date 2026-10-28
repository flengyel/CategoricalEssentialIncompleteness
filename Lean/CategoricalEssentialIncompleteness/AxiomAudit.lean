import CategoricalEssentialIncompleteness

/-! Print the transitive axiom dependencies of the combined interface and all
nine proved solution declarations. The verification script rejects any axiom
other than `propext`, `Classical.choice`, and `Quot.sound`. -/

#print axioms CategoricalEssentialIncompleteness.arithmeticRecursionCategory
#print axioms CategoricalEssentialIncompleteness.arithmeticEvaluatorIsTuring
#print axioms FailureOfComposition.Palomar.obstruction_four_properties
#print axioms FailureOfComposition.Palomar.no_quotient_composition_productive
#print axioms FailureOfComposition.Palomar.no_quotient_composition_godel
#print axioms FailureOfComposition.Palomar.pi_one_characterization
#print axioms FailureOfComposition.Palomar.generated_congruence_classification
#print axioms FailureOfComposition.Palomar.weak_totality_counterexample
#print axioms FailureOfComposition.Palomar.range_counterexample_godel
#print axioms FailureOfComposition.Palomar.range_counterexample_productive
#print axioms FailureOfComposition.Palomar.generated_quotient_partial_recursive
