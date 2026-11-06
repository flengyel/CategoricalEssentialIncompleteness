import CategoricalEssentialIncompleteness.V46NamedArithmeticProofSearchPredicates

/-! # Uniform source equality and all-model interpretation checks -/
noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.RestrictionCategory
open CategoricalEssentialIncompleteness.LocalConnectedness
open CategoricalEssentialIncompleteness.LocalConnectedness.PartialFunctions
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.NamedArithmeticProofSearch

namespace CategoricalEssentialIncompleteness.V46.NamedArithmeticProofSearch.PredicateChecks

example (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] {C D : Carrier} (f : GraphMorphism T C D)
    (E : Carrier) :
    Idem.pull (omegaArrow T f.programClass) (predicateIdem T E) =
      predicateIdem T (graphPullCarrier T f E) :=
  graphPullCarrier_idem T f E

example (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] (C : Carrier) (M : Type)
    [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T] :
    (SyntacticModel.modelRangeFunctor T M).mapIdem (predicateIdem T C) =
      setIdem {x : M | C.val.Evalb ![x]} :=
  model_predicateIdem T C M

end CategoricalEssentialIncompleteness.V46.NamedArithmeticProofSearch.PredicateChecks
