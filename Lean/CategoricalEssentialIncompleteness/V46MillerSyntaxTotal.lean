import CategoricalEssentialIncompleteness.V46MillerSyntaxUniformInitial
import CategoricalEssentialIncompleteness.V46MillerListsStable
import CategoricalEssentialIncompleteness.V46MillerDerivationEquality
import CategoricalEssentialIncompleteness.V46MillerTotalRealization
import CategoricalEssentialIncompleteness.V46SyntacticSyntaxParameterTransport
import CategoricalEssentialIncompleteness.V46SyntacticSyntaxStableTransport
import CategoricalEssentialIncompleteness.V46SyntacticListsEquivalence
import CategoricalEssentialIncompleteness.V46DecidableVariablesTransport

/-! # The concrete syntax bundle in the actual Miller total splitting

Initiality is first constructed for arbitrary uniform coefficient carriers
and target families, then transported through the actual splitting
equivalence with its polynomial and slice comparisons. The equivalence is
not used to infer initiality in a larger, unproved morphism class.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v u
open CategoryTheory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness.V46.Miller.Syntax
variable {P : Uniform.Family}

def categoricalSyntax (V : Total.TotalCategory P) (σ π : ℕ → Total.TotalCategory P) (d : ℕ) :
    CategoricalSyntax V σ π d where
  decidableVariables := Derivation.equality V
  algebra := Raw.wordAlgebra (SyntaxPolynomial.termExpression V σ d)
    (SyntaxPolynomial.formulaExpression V π d)
  initial := Raw.wordInitial (SyntaxPolynomial.termExpression V σ d)
    (SyntaxPolynomial.formulaExpression V π d)
  stable R := Raw.wordWithParametersInitial R (SyntaxPolynomial.termExpression V σ d)
    (SyntaxPolynomial.formulaExpression V π d)
  lists := Lists.stable V.obj

variable {D : Type u} [Category.{v} D] [Regular D] [FinitaryExtensive D]

def mappedWordData (E : Total.TotalCategory P ≌ D) (p q : SyntaxPolynomial D) :
    Σ A : Endofunctor.Algebra (SyntaxPolynomial.jointFunctor p q),
      IsInitial A × (∀ R : D,IsInitial (SyntaxPolynomial.algebraWithParameters p q A R)) := by
  let a := p.mapCoefficients E.inverse.obj
  let b := q.mapCoefficients E.inverse.obj
  let A := Raw.wordAlgebra a b
  have h : Σ B : Endofunctor.Algebra (SyntaxPolynomial.jointFunctor
      (p.mapCoefficients id) (q.mapCoefficients id)),
      IsInitial B × (∀ R : D,IsInitial (SyntaxPolynomial.algebraWithParameters
        (p.mapCoefficients id) (q.mapCoefficients id) B R)) :=
    ⟨SyntacticSyntax.Transport.mappedAlgebra E E.inverse.obj id
        (fun X => E.counitIso.app X) p q A,
      SyntaxPolynomialTransport.initial E E.inverse.obj id
        (fun X => E.counitIso.app X) p q A (Raw.wordInitial a b),
      SyntacticSyntax.Transport.mappedStable E E.inverse.obj id
        (fun X => E.counitIso.app X) p q A
        (fun R => Raw.wordWithParametersInitial R a b)⟩
  let S := fun r s : SyntaxPolynomial D =>
    Σ B : Endofunctor.Algebra (SyntaxPolynomial.jointFunctor r s),
      IsInitial B × (∀ R : D,IsInitial (SyntaxPolynomial.algebraWithParameters r s B R))
  exact Eq.mp (congrArg₂ S (SyntacticSyntax.mapCoefficients_id p)
    (SyntacticSyntax.mapCoefficients_id q)) h

def mappedCategoricalSyntax (E : Total.TotalCategory P ≌ D) (V : D) (σ π : ℕ → D) (d : ℕ) :
    CategoricalSyntax V σ π d where
  decidableVariables := DecidableVariables.Transport.mapped E
    (Derivation.equality (E.inverse.obj V)) V (E.counitIso.app V)
  algebra := (mappedWordData E (SyntaxPolynomial.termExpression V σ d)
    (SyntaxPolynomial.formulaExpression V π d)).1
  initial := (mappedWordData E (SyntaxPolynomial.termExpression V σ d)
    (SyntaxPolynomial.formulaExpression V π d)).2.1
  stable := (mappedWordData E (SyntaxPolynomial.termExpression V σ d)
    (SyntaxPolynomial.formulaExpression V π d)).2.2
  lists := SyntacticLists.Transport.mappedStableListAlgebra E (E.inverse.obj V) V
    (E.counitIso.app V) (Lists.stable (E.inverse.obj V).obj)

/-- Syntax and lists in the actual Tot(Split(E_z)), including every parameter
object there, with the proved coefficient counit comparisons. -/
def canonicalCategoricalSyntax (z : Point) (V : Total.CanonicalTotal z)
    (σ π : ℕ → Total.CanonicalTotal z) (d : ℕ) : CategoricalSyntax V σ π d :=
  mappedCategoricalSyntax (Total.pointPresentation z) V σ π d

end CategoricalEssentialIncompleteness.V46.Miller.Syntax
