import CategoricalEssentialIncompleteness.V46MillerSyntaxUniformDecomposition
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace CategoricalEssentialIncompleteness.V46.Miller.Syntax.Raw.Checks
example {P : Uniform.Family} (p q : SyntaxPolynomial (Total.TotalCategory P)) (formula : Bool) {word : ℕ}
    (hw : word ∈ (uniformWords formula p q).support) :
    ∃ u : ℕ,u ∈ (carrier (uniformWords false p q) (uniformWords true p q)
      (if formula then q else p)).support ∧
      word=SyntacticSyntax.Coding.constructor formula (skeleton (if formula then q else p)) u :=
  uniformWords_decomposition p q formula hw
end CategoricalEssentialIncompleteness.V46.Miller.Syntax.Raw.Checks
