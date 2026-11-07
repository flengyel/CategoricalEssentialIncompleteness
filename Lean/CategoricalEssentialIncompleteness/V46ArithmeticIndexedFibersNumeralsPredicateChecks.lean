import CategoricalEssentialIncompleteness.V46ArithmeticIndexedFibersNumeralsPredicate
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
namespace CategoricalEssentialIncompleteness.V46.ArithmeticIndexedFibers
open NamedArithmeticSignature
example (e : ℕ) : CategoryTheory.Iso (C := PredicateCategory 𝗣𝗔)
    (terminalCarrier ⨿ complementPredicate e) variableSymbols := predicateSplitIso e
example (e : ℕ) : coprod.inl ≫ (predicateSplitIso e).hom = numeralPredicate e := predicateSplitIso_inl e
example (e : ℕ) : coprod.inr ≫ (predicateSplitIso e).hom = complementPredicateInclusion e := predicateSplitIso_inr e
end CategoricalEssentialIncompleteness.V46.ArithmeticIndexedFibers
