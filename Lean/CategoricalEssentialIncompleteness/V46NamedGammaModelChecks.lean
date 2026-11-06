import CategoricalEssentialIncompleteness.V46NamedGammaModel
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
namespace CategoricalEssentialIncompleteness.V46.NamedGammaModel
open NamedArithmeticSignature SyntacticPredicates
example (A : Carrier) (hPA : ArithmeticNamedAxiomComparison.ExtendsPA A)
    (hc : Consistent (ArithmeticNamedProofConnectives.system A)) :
    Consistent (sourceTheory A) := source_consistent_of_extendsPA A hPA hc
example (A : Carrier) (hPA : ArithmeticNamedAxiomComparison.ExtendsPA A)
    (hc : Consistent (ArithmeticNamedProofConnectives.system A)) :
    ∃ (K : Type) (s : ORingStructure K), letI := s;
      ∀ φ : Formula, A.val.Evalb ![formulaCode φ] → φ.freeVariables = [] →
        φ.Holds ArithmeticNamedTranslation.functions ArithmeticNamedTranslation.relations
          (fun _ => (0 : K)) := exists_model A hPA hc
end CategoricalEssentialIncompleteness.V46.NamedGammaModel
