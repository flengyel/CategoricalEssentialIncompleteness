/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NullaryLogicalDistribution

/-! # Statement checks for quantifier distribution under interpretation of propositional atoms -/

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
    distributionBaseMap S Q f ≫ Q.distributionAbsence = S.distributionAbsence :=
  NullaryInterpretation.distribution_absence_comparison S Q f

#print axioms
  CategoricalEssentialIncompleteness.V46.NullaryInterpretation.distribution_absence_comparison

example :
    distributionInterpretation S Q f ≫ Q.distributionInclusion =
      S.distributionInclusion ≫ distributionBaseMap S Q f :=
  NullaryInterpretation.distributionInterpretation_inclusion S Q f

#print axioms
  CategoricalEssentialIncompleteness.V46.NullaryInterpretation.distributionInterpretation_inclusion

example :
    S.hilbertDistribution ≫ (interpretation S Q f).2 =
      distributionInterpretation S Q f ≫ Q.hilbertDistribution :=
  NullaryInterpretation.hilbert_distribution_comparison S Q f

#print axioms
  CategoricalEssentialIncompleteness.V46.NullaryInterpretation.hilbert_distribution_comparison
