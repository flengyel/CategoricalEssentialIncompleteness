import CategoricalEssentialIncompleteness.V46CategoricalSubstitutionIdentityParameters

/-! Parameter change uses arbitrary arrows and arbitrary target families. -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u

open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness CategoricalEssentialIncompleteness.V46
open SyntaxParameterChange

variable {D : Type u} [Category.{v} D] [Regular D] [FinitaryExtensive D]
variable {V : D} {σ π : ℕ → D} {d : ℕ} (S : CategoricalSyntax V σ π d)
variable {P Q : D} (r : P ⟶ Q)
variable (B : Endofunctor.Algebra (SyntaxPolynomial.jointFunctor
  ((SyntaxPolynomial.termExpression V σ d).withParameters Q)
  ((SyntaxPolynomial.formulaExpression V π d).withParameters Q)))

example :
    ((Over.map r).obj (constantFamily P S.algebra.a.1),
      (Over.map r).obj (constantFamily P S.algebra.a.2)) ⟶ B.a :=
  S.crossParameterFold r B

example : mate r (A := S.parameterSyntaxFamilies P) (S.crossParameterFold r B) =
    S.foldWithParameters P (reindexAlgebra r (SyntaxPolynomial.termExpression V σ d)
      (SyntaxPolynomial.formulaExpression V π d) B) := S.fold_parameter_change r B

example : (reindexAlgebra r (SyntaxPolynomial.termExpression V σ d)
    (SyntaxPolynomial.formulaExpression V π d) B).a =
      ((Over.pullback r).obj B.a.1, (Over.pullback r).obj B.a.2) := rfl

example (X : D) : (baseMap r X).left = prod.map r (𝟙 X) := rfl
