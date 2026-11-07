import CategoricalEssentialIncompleteness.V46NumericalNamedLiteralSyntax

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness.V46.NumericalNamedLiteralSyntaxChecks
open NumericalNamed SyntaxOperationsTransport
variable (V : NumericalTuples.Object) (σ π : ℕ → NumericalTuples.Object) (d : ℕ)

example : IsInitial (literalCategoricalSyntax V σ π d).algebra :=
  (literalCategoricalSyntax V σ π d).initial
example (P : NumericalTuples.Object) :
    IsInitial (SyntaxPolynomial.algebraWithParameters
      (SyntaxPolynomial.termExpression V σ d) (SyntaxPolynomial.formulaExpression V π d)
      (literalCategoricalSyntax V σ π d).algebra P) :=
  (literalCategoricalSyntax V σ π d).stable P
example : (literalCategoricalSyntax V σ π d).algebra ≅
    (NumericalSyntax.categoricalSyntax V σ π d).algebra := literalOriginalAlgebraIso V σ π d

example : (SyntaxPolynomial.jointFunctor (SyntaxPolynomial.termExpression V σ d)
      (SyntaxPolynomial.formulaExpression V π d)).map (literalAlgebraIso V σ π d).hom.f ≫
      (literalCategoricalSyntax V σ π d).algebra.str =
    (mappedSyntaxAlgebra literalEquivalence V σ π d (literalSourceSyntax V σ π d)).str ≫
      (literalAlgebraIso V σ π d).hom.f := (literalAlgebraIso V σ π d).hom.h

end CategoricalEssentialIncompleteness.V46.NumericalNamedLiteralSyntaxChecks
