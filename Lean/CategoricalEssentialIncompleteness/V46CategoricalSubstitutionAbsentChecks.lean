import CategoricalEssentialIncompleteness.V46CategoricalSubstitutionAbsent

/-! The manuscript's actual absent-variable fibers and admissibility factorization. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v u
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness CategoricalEssentialIncompleteness.V46
variable {D : Type u} [Category.{v} D] [Regular D] [FinitaryExtensive D]
variable {V : D} {σ π : ℕ → D} {d : ℕ} (S : CategoricalSyntax V σ π d)

example : S.termAbsentTest =
    prod.lift (prod.snd ≫ prod.fst) (prod.fst ≫ S.termOccurrences) ≫
      S.lists.membership S.decidableVariables := rfl
example : S.formulaAbsentTest =
    prod.lift (prod.snd ≫ prod.fst) (prod.fst ≫ S.formulaOccurrences) ≫
      S.lists.membership S.decidableVariables := rfl
example : S.termAbsentObject ⟶ S.algebra.a.1 ⨯ S.substitutionParameters := S.termAbsentInclusion
example : S.formulaAbsentObject ⟶ S.algebra.a.2 ⨯ S.substitutionParameters := S.formulaAbsentInclusion
example : Mono S.termAbsentInclusion := inferInstance
example : Mono S.formulaAbsentInclusion := inferInstance
example : IsPullback S.termAbsentInclusion (terminal.from _)
    S.termAbsentTest (Two.point false) := PresentationLemmas.bound_isPullback _ _
example : IsPullback S.formulaAbsentInclusion (terminal.from _)
    S.formulaAbsentTest (Two.point false) := PresentationLemmas.bound_isPullback _ _
example : S.termAbsentInclusion ≫ S.termSubstitution = S.termAbsentInclusion ≫ prod.fst :=
  S.termAbsent_fixed
example : S.formulaAbsentInclusion ≫ S.formulaSubstitutionOption =
    S.formulaAbsentInclusion ≫ prod.fst ≫ coprod.inr := S.formulaAbsent_success
example : S.formulaAbsentObject ⟶ S.admissibleSubstitution := S.formulaAbsentAdmissible
example : S.formulaAbsentAdmissible ≫ S.admissibleInclusion = S.formulaAbsentInclusion :=
  S.formulaAbsentAdmissible_inclusion
example : S.formulaAbsentAdmissible ≫ S.formulaSubstitution =
    S.formulaAbsentInclusion ≫ prod.fst := S.formulaAbsentAdmissible_result

example {X : D} (u t : X ⟶ S.algebra.a.1) (x : X ⟶ V)
    (ha : prod.lift x (u ≫ S.termOccurrences) ≫ S.lists.membership S.decidableVariables =
      Two.constant X false) :
    prod.lift u (prod.lift x t) ≫ S.termSubstitution = u :=
  S.term_substitution_absent_names u x t ha

example {X : D} (φ : X ⟶ S.algebra.a.2) (t : X ⟶ S.algebra.a.1) (x : X ⟶ V)
    (ha : prod.lift x (φ ≫ S.formulaOccurrences) ≫ S.lists.membership S.decidableVariables =
      Two.constant X false) :
    prod.lift φ (prod.lift x t) ≫ S.formulaSubstitutionOption = φ ≫ coprod.inr :=
  S.formula_substitution_absent_names φ x t ha
