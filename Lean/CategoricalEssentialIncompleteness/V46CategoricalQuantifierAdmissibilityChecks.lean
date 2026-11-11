/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46CategoricalQuantifierAdmissibility

/-! Exact domains, actual pullbacks, and the disjoint coproduct presentation. -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v u
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness CategoricalEssentialIncompleteness.V46
variable {D : Type u} [Category.{v} D] [Regular D] [FinitaryExtensive D]
variable {V : D} {σ π : ℕ → D} {d : ℕ} (S : CategoricalSyntax V σ π d)

example : (V ⨯ S.algebra.a.2) ⨯ S.substitutionParameters ⟶
    S.algebra.a.2 ⨯ S.substitutionParameters := S.quantifiedInput

example : S.quantifiedInput = prod.map S.quantifierConstructor (𝟙 _) := rfl

example : S.quantifiedBody = prod.lift (prod.fst ≫ prod.snd) prod.snd := rfl

example : S.quantifiedEquality =
    prod.lift (prod.fst ≫ prod.fst) (prod.snd ≫ prod.fst) ≫ S.decidableVariables.test := rfl

example : S.quantifiedCapture =
    Two.binary Bool.or
      (Two.unary Bool.not
        (prod.lift (prod.snd ≫ prod.fst)
          (prod.fst ≫ prod.snd ≫ S.formulaOccurrences) ≫
            S.lists.membership S.decidableVariables))
      (Two.unary Bool.not
        (prod.lift (prod.fst ≫ prod.fst)
          (prod.snd ≫ prod.snd ≫ S.termOccurrences) ≫
            S.lists.membership S.decidableVariables)) := rfl

example : IsPullback (Two.fiberι S.quantifiedEquality true) (terminal.from _)
    S.quantifiedEquality (Two.point true) :=
  PresentationLemmas.bound_isPullback _ _

example : S.quantifiedInput ≫ S.formulaSubstitutionOption =
    S.quantifiedFoldInput ≫ S.quantifierSubstitutionResult :=
  S.quantified_substitution_equation

example :
    (Subobject.pullback S.quantifiedInput).obj (Subobject.mk S.admissibleInclusion) =
      Two.fiberSubobject S.quantifiedEquality true ⊔
        (Two.fiberSubobject S.quantifiedEquality false ⊓
          Two.fiberSubobject S.quantifiedCapture true ⊓
            (Subobject.pullback S.quantifiedBody).obj (Subobject.mk S.admissibleInclusion)) :=
  S.quantified_admissibility_subobjects

example : Mono S.quantifiedAdmissibilityCoproduct := inferInstance

example : Subobject.mk S.quantifiedAdmissibilityCoproduct =
    (Subobject.pullback S.quantifiedInput).obj (Subobject.mk S.admissibleInclusion) :=
  S.quantified_admissibility_coproduct
