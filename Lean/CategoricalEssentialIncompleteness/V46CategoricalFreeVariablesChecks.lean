import CategoricalEssentialIncompleteness.V46CategoricalFreeVariables
import CategoricalEssentialIncompleteness.V46Inference

/-! Occurrence-list and sentence types and their common finite-power convention. -/

noncomputable section

universe v u

open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46

variable {D : Type u} [Category.{v} D] [Regular D] [FinitaryExtensive D]
variable {V : D} {σ π : ℕ → D} {d : ℕ} (S : CategoricalSyntax V σ π d)

example : S.algebra.a.1 ⟶ S.lists.algebra.carrier := S.termOccurrences

example : S.algebra.a.2 ⟶ S.lists.algebra.carrier := S.formulaOccurrences

example : S.sentenceObject = pullback S.formulaOccurrences S.lists.algebra.nil := rfl

example : Mono S.sentenceInclusion := inferInstance

example : S.sentenceNegation ≫ S.sentenceInclusion =
    S.sentenceInclusion ≫ S.negationConstructor := S.sentenceNegation_inclusion

example (p : SyntaxPolynomial D) (X : D × D) (n : ℕ) :
    (SyntaxPolynomial.power p n).eval.obj X = finitePower (p.eval.obj X) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    cases n with
    | zero => rfl
    | succ n =>
      simpa only [SyntaxPolynomial.power, SyntaxPolynomial.eval,
        SyntaxPolynomial.productFunctor, finitePower] using
          congrArg (fun Z => Z ⨯ p.eval.obj X) ih
