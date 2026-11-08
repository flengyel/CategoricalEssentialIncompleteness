import CategoricalEssentialIncompleteness.V46MillerNamedSyntaxCharts
noncomputable section
open CategoryTheory CategoryTheory.Limits
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.V46
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.Miller
variable (P : Uniform.Family) (a b : SyntacticSyntax.RawPolynomial)
example (formula : Bool) :
    Syntax.Raw.wordObject formula (Syntax.Polynomial.mapped P a) (Syntax.Polynomial.mapped P b) ≅
      (Syntax.predicateFunctor P).obj (SyntacticSyntax.Postfix.plainCarrier formula a b) :=
  NamedSyntaxComparison.wordIso P a b formula
example (formula : Bool) (word output : ℕ) :
    output∈Total.val (NamedSyntaxComparison.wordIso P a b formula).hom.hom word ↔
      word∈(Syntax.Raw.uniformWords formula (Syntax.Polynomial.mapped P a) (Syntax.Polynomial.mapped P b)).support ∧ output=word :=
  NamedSyntaxComparison.wordIso_graph P a b formula word output
example (X Y : PredicateCategory 𝗣𝗔) (X' Y' : Total.TotalCategory P)
    (iX : X' ≅ (Syntax.predicateFunctor P).obj X) (iY : Y' ≅ (Syntax.predicateFunctor P).obj Y)
    (p : SyntaxPolynomial (PredicateCategory 𝗣𝗔)) :
    Syntax.Raw.baseObject X' Y' (Syntax.Polynomial.mapped P p) ≅
      (Syntax.predicateFunctor P).obj (p.eval.obj (X,Y)) :=
  NamedSyntaxComparison.inputIso P X Y X' Y' iX iY p
