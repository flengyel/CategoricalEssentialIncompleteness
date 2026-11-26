/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NullaryLogicalDistribution

/-! # The equality-substitution scheme under interpretation of propositional atoms -/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u
open CategoryTheory CategoryTheory.Limits

namespace CategoricalEssentialIncompleteness.V46.NullaryInterpretation

variable {D : Type u} [Category.{v} D] [Regular D] [FinitaryExtensive D]
variable {V X : D}
variable (S : CategoricalSyntax V (fun _ => ⊥_ D) (fun _ => X) 0)
variable {σ π : ℕ → D} {d : ℕ} (Q : CategoricalSyntax V σ π d)
variable (f : X ⟶ Q.sentenceObject)

def equalitySchemeBaseMap : S.equalitySchemeBase ⟶ Q.equalitySchemeBase :=
  prod.map (prod.map (𝟙 V) (interpretation S Q f).2)
    (prod.map (interpretation S Q f).1 (interpretation S Q f).1)

theorem equality_first_input_comparison :
    S.equalityFirstInput ≫
        prod.map (interpretation S Q f).2 (substitutionParameterMap S Q f) =
      equalitySchemeBaseMap S Q f ≫ Q.equalityFirstInput := by
  apply prod.hom_ext <;>
    simp [CategoricalSyntax.equalityFirstInput, equalitySchemeBaseMap,
      substitutionParameterMap, Category.assoc]

theorem equality_second_input_comparison :
    S.equalitySecondInput ≫
        prod.map (interpretation S Q f).2 (substitutionParameterMap S Q f) =
      equalitySchemeBaseMap S Q f ≫ Q.equalitySecondInput := by
  apply prod.hom_ext <;>
    simp [CategoricalSyntax.equalitySecondInput, equalitySchemeBaseMap,
      substitutionParameterMap, Category.assoc]

def equalityFirstParameterMap : pullback S.equalityFirstInput S.admissibleInclusion ⟶
    pullback Q.equalityFirstInput Q.admissibleInclusion :=
  pullback.map _ _ _ _ (equalitySchemeBaseMap S Q f) (admissibleInterpretation S Q f)
    (prod.map (interpretation S Q f).2 (substitutionParameterMap S Q f))
    (equality_first_input_comparison S Q f) (admissibleInterpretation_inclusion S Q f).symm

def equalitySecondParameterMap : pullback S.equalitySecondInput S.admissibleInclusion ⟶
    pullback Q.equalitySecondInput Q.admissibleInclusion :=
  pullback.map _ _ _ _ (equalitySchemeBaseMap S Q f) (admissibleInterpretation S Q f)
    (prod.map (interpretation S Q f).2 (substitutionParameterMap S Q f))
    (equality_second_input_comparison S Q f) (admissibleInterpretation_inclusion S Q f).symm

def equalitySchemeInterpretation : S.equalitySchemeParameters ⟶ Q.equalitySchemeParameters :=
  pullback.map _ _ _ _ (equalityFirstParameterMap S Q f) (equalitySecondParameterMap S Q f)
    (equalitySchemeBaseMap S Q f) (by simp [equalityFirstParameterMap, pullback.map])
    (by simp [equalitySecondParameterMap, pullback.map])

@[reassoc (attr := simp)] theorem equalitySchemeInterpretation_inclusion :
    equalitySchemeInterpretation S Q f ≫ Q.equalitySchemeInclusion =
      S.equalitySchemeInclusion ≫ equalitySchemeBaseMap S Q f := by
  simp [equalitySchemeInterpretation, equalityFirstParameterMap, pullback.map,
    CategoricalSyntax.equalitySchemeInclusion, Category.assoc]

@[reassoc (attr := simp)] theorem equalitySchemeInterpretation_first_admissible :
    equalitySchemeInterpretation S Q f ≫ Q.equalityFirstAdmissible =
      S.equalityFirstAdmissible ≫ admissibleInterpretation S Q f := by
  simp [equalitySchemeInterpretation, equalityFirstParameterMap, pullback.map,
    CategoricalSyntax.equalityFirstAdmissible, Category.assoc]

@[reassoc (attr := simp)] theorem equalitySchemeInterpretation_second_admissible :
    equalitySchemeInterpretation S Q f ≫ Q.equalitySecondAdmissible =
      S.equalitySecondAdmissible ≫ admissibleInterpretation S Q f := by
  simp [equalitySchemeInterpretation, equalitySecondParameterMap, pullback.map,
    CategoricalSyntax.equalitySecondAdmissible, Category.assoc]

theorem hilbert_equality_comparison :
    S.hilbertEquality ≫ (interpretation S Q f).2 =
      equalitySchemeInterpretation S Q f ≫ Q.hilbertEquality := by
  simp [CategoricalSyntax.hilbertEquality, equalitySchemeBaseMap,
    Category.assoc, implication S Q f, equality S Q f,
    prod.comp_lift_assoc, prod.lift_map_assoc]

end CategoricalEssentialIncompleteness.V46.NullaryInterpretation
