/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NullaryLogicalInstantiation

/-! # Statement checks for instantiation under interpretation of propositional atoms -/

@[expose] public section

noncomputable section

universe v u
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness CategoricalEssentialIncompleteness.V46

variable {D : Type u} [Category.{v} D] [Regular D] [FinitaryExtensive D]
variable {V X : D}
variable (S : CategoricalSyntax V (fun _ => ⊥_ D) (fun _ => X) 0)
variable {σ π : ℕ → D} {d : ℕ} (Q : CategoricalSyntax V σ π d)
variable (f : X ⟶ Q.sentenceObject)
open NullaryInterpretation

example :
    S.hilbertOne ≫ (interpretation S Q f).2 =
      prod.map (interpretation S Q f).2 (interpretation S Q f).2 ≫ Q.hilbertOne :=
  NullaryInterpretation.hilbert_one_comparison S Q f

#print axioms
  CategoricalEssentialIncompleteness.V46.NullaryInterpretation.hilbert_one_comparison

example :
    S.hilbertTwo ≫ (interpretation S Q f).2 =
      prod.map (prod.map (interpretation S Q f).2 (interpretation S Q f).2)
        (interpretation S Q f).2 ≫ Q.hilbertTwo :=
  NullaryInterpretation.hilbert_two_comparison S Q f

#print axioms
  CategoricalEssentialIncompleteness.V46.NullaryInterpretation.hilbert_two_comparison

example :
    S.hilbertThree ≫ (interpretation S Q f).2 =
      prod.map (interpretation S Q f).2 (interpretation S Q f).2 ≫ Q.hilbertThree :=
  NullaryInterpretation.hilbert_three_comparison S Q f

#print axioms
  CategoricalEssentialIncompleteness.V46.NullaryInterpretation.hilbert_three_comparison

example :
    instantiationBaseMap S Q f ≫ Q.instantiationInput =
      S.instantiationInput ≫
        prod.map (interpretation S Q f).2 (substitutionParameterMap S Q f) :=
  NullaryInterpretation.instantiation_input_comparison S Q f

#print axioms
  CategoricalEssentialIncompleteness.V46.NullaryInterpretation.instantiation_input_comparison

example :
    instantiationInterpretation S Q f ≫ Q.instantiationInclusion =
      S.instantiationInclusion ≫ instantiationBaseMap S Q f :=
  NullaryInterpretation.instantiationInterpretation_inclusion S Q f

#print axioms
  CategoricalEssentialIncompleteness.V46.NullaryInterpretation.instantiationInterpretation_inclusion

example :
    instantiationInterpretation S Q f ≫ Q.instantiationAdmissible =
      S.instantiationAdmissible ≫ admissibleInterpretation S Q f :=
  NullaryInterpretation.instantiationInterpretation_admissible S Q f

#print axioms
  CategoricalEssentialIncompleteness.V46.NullaryInterpretation.instantiationInterpretation_admissible

example :
    S.hilbertInstantiation ≫ (interpretation S Q f).2 =
      instantiationInterpretation S Q f ≫ Q.hilbertInstantiation :=
  NullaryInterpretation.hilbert_instantiation_comparison S Q f

#print axioms
  CategoricalEssentialIncompleteness.V46.NullaryInterpretation.hilbert_instantiation_comparison

example :
    S.hilbertReflexivity ≫ (interpretation S Q f).2 =
      (interpretation S Q f).1 ≫ Q.hilbertReflexivity :=
  NullaryInterpretation.hilbert_reflexivity_comparison S Q f

#print axioms
  CategoricalEssentialIncompleteness.V46.NullaryInterpretation.hilbert_reflexivity_comparison
