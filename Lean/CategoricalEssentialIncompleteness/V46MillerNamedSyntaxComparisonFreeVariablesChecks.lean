import CategoricalEssentialIncompleteness.V46MillerNamedSyntaxComparisonFreeVariables
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.V46
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.Miller
variable (P : Uniform.Family) (V : PredicateCategory 𝗣𝗔) (σ π : ℕ → PredicateCategory 𝗣𝗔) (d : ℕ)
local notation "S₀" => NamedSyntaxComparison.sourceSyntax V σ π d
local notation "S₁" => NamedSyntaxComparison.presentedSyntax P V σ π d
example : (NamedSyntaxComparison.sourcePairIso P V σ π d).hom.1 ≫
    (Syntax.predicateFunctor P).map (S₀).termOccurrences=(S₁).termOccurrences :=
  NamedSyntaxComparison.termOccurrences_comparison P V σ π d
example : (NamedSyntaxComparison.sourcePairIso P V σ π d).hom.2 ≫
    (Syntax.predicateFunctor P).map (S₀).formulaOccurrences=(S₁).formulaOccurrences :=
  NamedSyntaxComparison.formulaOccurrences_comparison P V σ π d
example : NamedSyntaxComparison.castAlgebra
    (NamedSyntaxComparison.termExpression_mapped P V σ d)
    (NamedSyntaxComparison.formulaExpression_mapped P V π d)
    (Syntax.Polynomial.mappedAlgebra P (SyntaxPolynomial.termExpression V σ d)
      (SyntaxPolynomial.formulaExpression V π d) (S₀).occurrenceAlgebra) ≅ (S₁).occurrenceAlgebra :=
  NamedSyntaxComparison.occurrenceAlgebraIso P V σ π d

example : (NamedSyntaxComparison.explicitOccurrenceAlgebra P V σ π d).a =
    ((Syntax.predicateFunctor P).obj (SyntacticLists.stableListAlgebra 𝗣𝗔 V).algebra.carrier,
      (Syntax.predicateFunctor P).obj (SyntacticLists.stableListAlgebra 𝗣𝗔 V).algebra.carrier) := rfl
example : NamedSyntaxComparison.explicitOccurrenceAlgebra P V σ π d = (S₁).occurrenceAlgebra :=
  NamedSyntaxComparison.explicitOccurrenceAlgebra_eq P V σ π d
example : NamedSyntaxComparison.castAlgebra
    (NamedSyntaxComparison.termExpression_mapped P V σ d)
    (NamedSyntaxComparison.formulaExpression_mapped P V π d)
    (Syntax.Polynomial.mappedAlgebra P (SyntaxPolynomial.termExpression V σ d)
      (SyntaxPolynomial.formulaExpression V π d) (S₀).occurrenceAlgebra) ≅
      NamedSyntaxComparison.explicitOccurrenceAlgebra P V σ π d :=
  NamedSyntaxComparison.explicitOccurrenceAlgebraIso P V σ π d
example : (NamedSyntaxComparison.occurrenceAlgebraIso P V σ π d).hom.f =
    eqToHom (NamedSyntaxComparison.castAlgebra_carrier
      (NamedSyntaxComparison.termExpression_mapped P V σ d)
      (NamedSyntaxComparison.formulaExpression_mapped P V π d)
      (Syntax.Polynomial.mappedAlgebra P (SyntaxPolynomial.termExpression V σ d)
        (SyntaxPolynomial.formulaExpression V π d) (S₀).occurrenceAlgebra)) :=
  NamedSyntaxComparison.occurrenceAlgebraIso_hom P V σ π d
