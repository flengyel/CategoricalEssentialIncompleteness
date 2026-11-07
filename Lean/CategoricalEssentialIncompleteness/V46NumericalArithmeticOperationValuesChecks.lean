import CategoricalEssentialIncompleteness.V46NumericalArithmeticOperationValues
noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness.V46.NumericalArithmetic.OperationValues.Checks
open Coordinates NamedArithmeticSignature
local notation "S" => numericalSyntax
example (q : NumericalTuples.Point ((S).algebra.a.1 ⨯ (S).substitutionParameters)) :
    (termIso.hom.toFun ((S).termSubstitution.toFun q)).val =
      ConcreteNamedSubstitution.substitutionResult (M := ℕ) variableSymbols functionSymbols relationSymbols bound
        (name ((prod.snd : (S).algebra.a.1 ⨯ (S).substitutionParameters ⟶ (S).substitutionParameters).toFun q))
        (replacement ((prod.snd : (S).algebra.a.1 ⨯ (S).substitutionParameters ⟶ (S).substitutionParameters).toFun q))
        (termIso.hom.toFun ((prod.fst : (S).algebra.a.1 ⨯ (S).substitutionParameters ⟶ (S).algebra.a.1).toFun q)).val :=
  term_substitution_value q
example (q : NumericalTuples.Point ((S).algebra.a.2 ⨯ (S).substitutionParameters)) :
    optionWord ((S).formulaSubstitutionOption.toFun q) =
      ConcreteNamedSubstitution.substitutionResult (M := ℕ) variableSymbols functionSymbols relationSymbols bound
        (name ((prod.snd : (S).algebra.a.2 ⨯ (S).substitutionParameters ⟶ (S).substitutionParameters).toFun q))
        (replacement ((prod.snd : (S).algebra.a.2 ⨯ (S).substitutionParameters ⟶ (S).substitutionParameters).toFun q))
        (formulaIso.hom.toFun ((prod.fst : (S).algebra.a.2 ⨯ (S).substitutionParameters ⟶ (S).algebra.a.2).toFun q)).val :=
  formula_option_value q
example (q : NumericalTuples.Point ((S).algebra.a.2 ⨯ (S).substitutionParameters)) :
    (∃ a, (S).admissibleInclusion.toFun a = q) ↔
      ConcreteNamedSubstitution.substitutionFreeFor (M := ℕ) variableSymbols functionSymbols relationSymbols bound
        (name ((prod.snd : (S).algebra.a.2 ⨯ (S).substitutionParameters ⟶ (S).substitutionParameters).toFun q))
        (replacement ((prod.snd : (S).algebra.a.2 ⨯ (S).substitutionParameters ⟶ (S).substitutionParameters).toFun q))
        (formulaIso.hom.toFun ((prod.fst : (S).algebra.a.2 ⨯ (S).substitutionParameters ⟶ (S).algebra.a.2).toFun q)).val = 1 :=
  admissible_iff q
example (a : NumericalTuples.Point (S).admissibleSubstitution) :
    let q := (S).admissibleInclusion.toFun a
    (formulaIso.hom.toFun ((S).formulaSubstitution.toFun a)).val =
      π₁ (ConcreteNamedSubstitution.substitutionResult (M := ℕ) variableSymbols functionSymbols relationSymbols bound
        (name ((prod.snd : (S).algebra.a.2 ⨯ (S).substitutionParameters ⟶ (S).substitutionParameters).toFun q))
        (replacement ((prod.snd : (S).algebra.a.2 ⨯ (S).substitutionParameters ⟶ (S).substitutionParameters).toFun q))
        (formulaIso.hom.toFun ((prod.fst : (S).algebra.a.2 ⨯ (S).substitutionParameters ⟶ (S).algebra.a.2).toFun q)).val) :=
  formula_substitution_value a
end CategoricalEssentialIncompleteness.V46.NumericalArithmetic.OperationValues.Checks
