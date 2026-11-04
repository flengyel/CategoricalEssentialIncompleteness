import CategoricalEssentialIncompleteness.V46CategoricalFreeVariableLaws

/-! Constructor equations at arbitrary internal parameters and coefficient objects. -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u

open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness CategoricalEssentialIncompleteness.V46

variable {D : Type u} [Category.{v} D] [Regular D] [FinitaryExtensive D]
variable {V X : D} {σ π : ℕ → D} {d : ℕ} (S : CategoricalSyntax V σ π d)

example : S.variableConstructor ≫ S.termOccurrences = S.lists.singleton := S.variable_occurrences

example : S.functionConstructors ≫ S.termOccurrences =
    (SyntaxPolynomial.constructors σ d).eval.map (S.termOccurrences, S.formulaOccurrences) ≫
      S.lists.constructorOccurrences σ d := S.function_occurrences

example : S.relationConstructors ≫ S.formulaOccurrences =
    (SyntaxPolynomial.constructors π d).eval.map (S.termOccurrences, S.formulaOccurrences) ≫
      S.lists.constructorOccurrences π d := S.relation_occurrences

example : S.equalityConstructor ≫ S.formulaOccurrences =
    prod.map S.termOccurrences S.termOccurrences ≫ S.lists.append := S.equality_occurrences

example : S.implicationConstructor ≫ S.formulaOccurrences =
    prod.map S.formulaOccurrences S.formulaOccurrences ≫ S.lists.append := S.implication_occurrences

example : S.quantifierConstructor ≫ S.formulaOccurrences =
    prod.map (𝟙 V) S.formulaOccurrences ≫ S.lists.deletion S.decidableVariables :=
  S.quantifier_occurrences

example (x y : X ⟶ V) (φ : X ⟶ S.algebra.a.2) :
    prod.lift x (prod.lift y φ ≫ S.quantifierConstructor ≫ S.formulaOccurrences) ≫
        S.lists.membership S.decidableVariables =
      Two.binary Bool.and (Two.unary Bool.not (prod.lift x y ≫ S.decidableVariables.test))
        (prod.lift x (φ ≫ S.formulaOccurrences) ≫ S.lists.membership S.decidableVariables) :=
  S.quantifier_membership x y φ

example (y : X ⟶ V) (φ : X ⟶ S.algebra.a.2) :
    prod.lift y (prod.lift y φ ≫ S.quantifierConstructor ≫ S.formulaOccurrences) ≫
        S.lists.membership S.decidableVariables = Two.constant X false :=
  S.quantifier_bound_name_absent y φ

example (x y : X ⟶ V) :
    prod.lift x (y ≫ S.variableConstructor ≫ S.termOccurrences) ≫
        S.lists.membership S.decidableVariables = prod.lift x y ≫ S.decidableVariables.test :=
  S.variable_membership x y
