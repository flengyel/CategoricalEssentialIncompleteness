/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NullaryLogicalEquality

/-! # Statement checks for equality under interpretation of propositional atoms -/

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
    S.equalityFirstInput ≫
        prod.map (interpretation S Q f).2 (substitutionParameterMap S Q f) =
      equalitySchemeBaseMap S Q f ≫ Q.equalityFirstInput :=
  NullaryInterpretation.equality_first_input_comparison S Q f

#print axioms
  CategoricalEssentialIncompleteness.V46.NullaryInterpretation.equality_first_input_comparison

example :
    S.equalitySecondInput ≫
        prod.map (interpretation S Q f).2 (substitutionParameterMap S Q f) =
      equalitySchemeBaseMap S Q f ≫ Q.equalitySecondInput :=
  NullaryInterpretation.equality_second_input_comparison S Q f

#print axioms
  CategoricalEssentialIncompleteness.V46.NullaryInterpretation.equality_second_input_comparison

example :
    equalitySchemeInterpretation S Q f ≫ Q.equalitySchemeInclusion =
      S.equalitySchemeInclusion ≫ equalitySchemeBaseMap S Q f :=
  NullaryInterpretation.equalitySchemeInterpretation_inclusion S Q f

#print axioms
  CategoricalEssentialIncompleteness.V46.NullaryInterpretation.equalitySchemeInterpretation_inclusion

example :
    equalitySchemeInterpretation S Q f ≫ Q.equalityFirstAdmissible =
      S.equalityFirstAdmissible ≫ admissibleInterpretation S Q f :=
  NullaryInterpretation.equalitySchemeInterpretation_first_admissible S Q f

#print axioms
  CategoricalEssentialIncompleteness.V46.NullaryInterpretation.equalitySchemeInterpretation_first_admissible

example :
    equalitySchemeInterpretation S Q f ≫ Q.equalitySecondAdmissible =
      S.equalitySecondAdmissible ≫ admissibleInterpretation S Q f :=
  NullaryInterpretation.equalitySchemeInterpretation_second_admissible S Q f

#print axioms
  CategoricalEssentialIncompleteness.V46.NullaryInterpretation.equalitySchemeInterpretation_second_admissible

example :
    S.hilbertEquality ≫ (interpretation S Q f).2 =
      equalitySchemeInterpretation S Q f ≫ Q.hilbertEquality :=
  NullaryInterpretation.hilbert_equality_comparison S Q f

#print axioms
  CategoricalEssentialIncompleteness.V46.NullaryInterpretation.hilbert_equality_comparison
