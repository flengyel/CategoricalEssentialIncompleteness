/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NullaryFormulaSubstitution
public import CategoricalEssentialIncompleteness.V46LogicalSchemes

/-! # Propositional and instantiation schemes under interpretation of propositional atoms -/

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

theorem hilbert_one_comparison :
    S.hilbertOne ≫ (interpretation S Q f).2 =
      prod.map (interpretation S Q f).2 (interpretation S Q f).2 ≫ Q.hilbertOne := by
  simp [CategoricalSyntax.hilbertOne, Category.assoc, implication S Q f,
    prod.comp_lift_assoc, prod.lift_map_assoc]

theorem hilbert_two_comparison :
    S.hilbertTwo ≫ (interpretation S Q f).2 =
      prod.map (prod.map (interpretation S Q f).2 (interpretation S Q f).2)
        (interpretation S Q f).2 ≫ Q.hilbertTwo := by
  simp [CategoricalSyntax.hilbertTwo, Category.assoc, implication S Q f,
    prod.comp_lift_assoc, prod.lift_map_assoc]

theorem hilbert_three_comparison :
    S.hilbertThree ≫ (interpretation S Q f).2 =
      prod.map (interpretation S Q f).2 (interpretation S Q f).2 ≫ Q.hilbertThree := by
  simp [CategoricalSyntax.hilbertThree, Category.assoc, implication S Q f, negation S Q f,
    prod.comp_lift_assoc, prod.lift_map_assoc]

def instantiationBaseMap : V ⨯ (S.algebra.a.2 ⨯ S.algebra.a.1) ⟶
    V ⨯ (Q.algebra.a.2 ⨯ Q.algebra.a.1) :=
  prod.map (𝟙 V) (prod.map (interpretation S Q f).2 (interpretation S Q f).1)

theorem instantiation_input_comparison :
    instantiationBaseMap S Q f ≫ Q.instantiationInput =
      S.instantiationInput ≫
        prod.map (interpretation S Q f).2 (substitutionParameterMap S Q f) := by
  apply prod.hom_ext <;>
    simp [instantiationBaseMap, CategoricalSyntax.instantiationInput,
      substitutionParameterMap, Category.assoc]

def instantiationInterpretation : S.instantiationParameters ⟶ Q.instantiationParameters :=
  pullback.lift (S.instantiationInclusion ≫ instantiationBaseMap S Q f)
    (S.instantiationAdmissible ≫ admissibleInterpretation S Q f) (by
      rw [Category.assoc, instantiation_input_comparison, ← Category.assoc,
        S.instantiation_admissible]
      simp only [Category.assoc, admissibleInterpretation_inclusion])

@[reassoc (attr := simp)] theorem instantiationInterpretation_inclusion :
    instantiationInterpretation S Q f ≫ Q.instantiationInclusion =
      S.instantiationInclusion ≫ instantiationBaseMap S Q f := pullback.lift_fst _ _ _

@[reassoc (attr := simp)] theorem instantiationInterpretation_admissible :
    instantiationInterpretation S Q f ≫ Q.instantiationAdmissible =
      S.instantiationAdmissible ≫ admissibleInterpretation S Q f := pullback.lift_snd _ _ _

theorem hilbert_instantiation_comparison :
    S.hilbertInstantiation ≫ (interpretation S Q f).2 =
      instantiationInterpretation S Q f ≫ Q.hilbertInstantiation := by
  simp [CategoricalSyntax.hilbertInstantiation, instantiationBaseMap,
    Category.assoc, implication S Q f, quantifier S Q f,
    prod.comp_lift_assoc, prod.lift_map_assoc]

theorem hilbert_reflexivity_comparison :
    S.hilbertReflexivity ≫ (interpretation S Q f).2 =
      (interpretation S Q f).1 ≫ Q.hilbertReflexivity := by
  simp [CategoricalSyntax.hilbertReflexivity, Category.assoc, equality S Q f,
    prod.comp_lift_assoc, prod.lift_map_assoc]

end CategoricalEssentialIncompleteness.V46.NullaryInterpretation
