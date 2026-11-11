/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NullaryLogicalInstantiation

/-! # The quantifier-distribution scheme under a nullary interpretation -/

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

def distributionBaseMap : V ⨯ (S.algebra.a.2 ⨯ S.algebra.a.2) ⟶
    V ⨯ (Q.algebra.a.2 ⨯ Q.algebra.a.2) :=
  prod.map (𝟙 V) (prod.map (interpretation S Q f).2 (interpretation S Q f).2)

theorem distribution_absence_comparison :
    distributionBaseMap S Q f ≫ Q.distributionAbsence = S.distributionAbsence := by
  have h := formula_membership S Q f
    (prod.fst : V ⨯ (S.algebra.a.2 ⨯ S.algebra.a.2) ⟶ V) (prod.snd ≫ prod.fst)
  simpa [distributionBaseMap, CategoricalSyntax.distributionAbsence,
    Category.assoc, prod.comp_lift_assoc] using h

def distributionInterpretation : S.distributionParameters ⟶ Q.distributionParameters :=
  equalizer.lift (S.distributionInclusion ≫ distributionBaseMap S Q f) (by
    simp only [Category.assoc, distribution_absence_comparison,
      S.distribution_absence, Two.comp_constant])

@[reassoc (attr := simp)] theorem distributionInterpretation_inclusion :
    distributionInterpretation S Q f ≫ Q.distributionInclusion =
      S.distributionInclusion ≫ distributionBaseMap S Q f := equalizer.lift_ι _ _

theorem hilbert_distribution_comparison :
    S.hilbertDistribution ≫ (interpretation S Q f).2 =
      distributionInterpretation S Q f ≫ Q.hilbertDistribution := by
  simp [CategoricalSyntax.hilbertDistribution, distributionBaseMap,
    Category.assoc, implication S Q f, quantifier S Q f,
    prod.comp_lift_assoc, prod.lift_map_assoc]

end CategoricalEssentialIncompleteness.V46.NullaryInterpretation
