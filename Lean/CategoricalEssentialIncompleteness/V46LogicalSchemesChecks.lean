/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46LogicalSchemes

/-! Explicit categorical parameter types for the seven logical schemes. -/

@[expose] public section

noncomputable section

universe v u

open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness CategoricalEssentialIncompleteness.V46

variable {D : Type u} [Category.{v} D] [Regular D] [FinitaryExtensive D]
variable {V : D} {σ π : ℕ → D} {d : ℕ} (S : CategoricalSyntax V σ π d)

example : S.algebra.a.2 ⨯ S.algebra.a.2 ⟶ S.algebra.a.2 := S.hilbertOne

example : (S.algebra.a.2 ⨯ S.algebra.a.2) ⨯ S.algebra.a.2 ⟶ S.algebra.a.2 :=
  S.hilbertTwo

example : S.algebra.a.2 ⨯ S.algebra.a.2 ⟶ S.algebra.a.2 := S.hilbertThree

example : pullback S.instantiationInput S.admissibleInclusion ⟶ S.algebra.a.2 :=
  S.hilbertInstantiation

example : equalizer S.distributionAbsence
    (Two.constant (V ⨯ (S.algebra.a.2 ⨯ S.algebra.a.2)) false) ⟶ S.algebra.a.2 :=
  S.hilbertDistribution

example : S.algebra.a.1 ⟶ S.algebra.a.2 := S.hilbertReflexivity

example : pullback (pullback.fst S.equalityFirstInput S.admissibleInclusion)
    (pullback.fst S.equalitySecondInput S.admissibleInclusion) ⟶ S.algebra.a.2 :=
  S.hilbertEquality

example : S.logicalParameters ⟶ S.algebra.a.2 := S.logicalAxioms

example : Mono S.instantiationInclusion := inferInstance

example : S.instantiationInclusion ≫ S.instantiationInput =
    S.instantiationAdmissible ≫ S.admissibleInclusion := S.instantiation_admissible

example : S.distributionInclusion ≫ S.distributionAbsence =
    Two.constant S.distributionParameters false := S.distribution_absence

example : Mono S.equalitySchemeInclusion := inferInstance

example : S.equalitySchemeInclusion ≫ S.equalityFirstInput =
    S.equalityFirstAdmissible ≫ S.admissibleInclusion := S.equality_first_admissible

example : S.equalitySchemeInclusion ≫ S.equalitySecondInput =
    S.equalitySecondAdmissible ≫ S.admissibleInclusion := S.equality_second_admissible

example {A : D} (axioms : A ⟶ S.sentenceObject) :
    RulePresentation S.algebra.a.2 2 := S.logicalRules axioms
