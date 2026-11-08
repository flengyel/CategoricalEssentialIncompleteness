import CategoricalEssentialIncompleteness.V46MillerNamedSyntaxComparisonNormalization
noncomputable section
open CategoryTheory CategoryTheory.Limits
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.V46
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.Miller
variable (P : Uniform.Family) (a b : SyntaxPolynomial (PredicateCategory 𝗣𝗔))
variable (r s : SyntaxPolynomial (Total.TotalCategory P))
variable (ha : Syntax.Polynomial.mapped P a=r) (hb : Syntax.Polynomial.mapped P b=s)
example (word output : ℕ) :
    output∈Total.val ((NamedSyntaxComparison.normalizedWordPairIso P a b r s ha hb).hom.1).hom word ↔
      word∈(Syntax.Raw.uniformWords false r s).support ∧ output=word :=
  NamedSyntaxComparison.normalizedWordPairIso_term_graph P a b r s ha hb word output
example (word output : ℕ) :
    output∈Total.val ((NamedSyntaxComparison.normalizedWordPairIso P a b r s ha hb).hom.2).hom word ↔
      word∈(Syntax.Raw.uniformWords true r s).support ∧ output=word :=
  NamedSyntaxComparison.normalizedWordPairIso_formula_graph P a b r s ha hb word output
