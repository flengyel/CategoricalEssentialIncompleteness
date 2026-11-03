import CategoricalEssentialIncompleteness.V46CategoricalSubstitution

/-! Explicit named-variable substitution types in an arbitrary category. -/

noncomputable section

universe v u

open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness CategoricalEssentialIncompleteness.V46

variable {D : Type u} [Category.{v} D] [Regular D] [FinitaryExtensive D]
variable {V : D} {σ π : ℕ → D} {d : ℕ} (S : CategoricalSyntax V σ π d)

example : S.algebra.a.1 ⨯ (V ⨯ S.algebra.a.1) ⟶ S.algebra.a.1 := S.termSubstitution

example : S.algebra.a.2 ⨯ (V ⨯ S.algebra.a.1) ⟶ (⊤_ D) ⨿ S.algebra.a.2 :=
  S.formulaSubstitutionOption

example : Mono S.admissibleInclusion := inferInstance

example : IsCompl (Subobject.mk S.admissibleInclusion)
    (Subobject.mk (pullback.fst S.formulaSubstitutionOption coprod.inl)) :=
  S.admissibility_complemented

example : S.admissibleInclusion ≫ S.formulaSubstitutionOption =
    S.formulaSubstitution ≫ coprod.inr := S.formulaSubstitution_square

example : S.substitutionFold ≫ S.substitutionOriginalHom.f =
    𝟙 (constantFamily S.substitutionParameters S.algebra.a.1,
      constantFamily S.substitutionParameters S.algebra.a.2) :=
  S.substitutionFold_original

example : Two.fiberι S.quantifierEquality true ≫ S.quantifierSubstitutionResult =
    Two.fiberι S.quantifierEquality true ≫ S.quantifierOriginal ≫ coprod.inr :=
  S.quantifierSubstitution_equal_branch
