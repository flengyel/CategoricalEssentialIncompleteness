/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ForkErasureClosure
public import CategoricalEssentialIncompleteness.V46ForkComparison
public import CategoricalEssentialIncompleteness.V46EquivalenceSubobjects
public import CategoricalEssentialIncompleteness.V46RestrictionSubobjectRanges
public import CategoricalEssentialIncompleteness.V46SignedFirstOrderIncompleteness

/-! # Consistency and essential incompleteness of the generated first-order fork theory -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.RestrictionCategory
open CategoricalEssentialIncompleteness.LocalConnectedness
namespace CategoricalEssentialIncompleteness.V46.ForkInternalIncompleteness
open ForkDerivation.Diagram ForkFirstOrderErasure ForkErasureClosure
local notation "S" => firstOrder
local notation "F" => ForkParameterizedDeduction.nullaryPresentations

theorem inverses : RestrictionSubobjects.MonoInverses EffectiveFork.Object :=
  fun m _ => ⟨PartialSpans.inverse m, PartialSpans.hom_inverse m, PartialSpans.inverse_hom m⟩

/-- The concrete c.e. domain subfunctor corresponds to its original
restriction idempotent under the total-subobject comparison. -/
theorem domain_inclusion {X : EffectiveFork.Object} (e : Idem X) :
    RestrictionSubobjects.domain inverses (Subobject.mk (EffectiveFork.domainInclusionTotal e)) = e := by
  let m := EffectiveFork.domainInclusionTotal e
  let r := EffectiveFork.domainRetraction e
  have hr : rst r = e.hom := by
    rw [← rst_comp_of_isTotal r m.property]
    exact (congrArg rst (EffectiveFork.retraction_inclusion e)).trans e.restriction
  have hs : SectionOf m.hom r := ⟨(EffectiveFork.retraction_inclusion e).trans hr.symm, by
    have hmr : m.hom ≫ r = 𝟙 _ := EffectiveFork.inclusion_retraction e
    rw [← Category.assoc, hmr, Category.id_comp]⟩
  rw [BooleanPartialDecision.domain_mk, RestrictionSubobjects.inverse_eq_span]
  have he : PartialSpans.inverse m = r := PartialMono.section_unique
    (PartialSpans.partialMono_of_mono m) (PartialSpans.inverse_section m) hs
  exact Idem.ext ((congrArg rst he).trans hr)

variable (a b : Idem EffectiveFork.V)

theorem prop_consistent (hd : a ⊓ b = ⊥) :
    propTheory a b ⊓ (Subobject.pullback negation).obj (propTheory a b) = ⊥ := by
  let X := ForkDerivation.sentenceObject
  let T := ForkDerivationImages.theoremSubobject a b
  let e := RestrictionSubobjects.orderIso inverses X
  have ht : RestrictionSubobjects.domain inverses T = ForkSyntax.t0 a b :=
    (RestrictionSubobjects.domain_image inverses (ForkDerivationImages.conclusion a b)).trans
      (ForkDerivationImages.theoremRange_eq_t0 a b)
  have hc : T ⊓ (Subobject.pullback ForkDerivation.negation).obj T = ⊥ := by
    apply e.injective
    rw [e.map_inf, e.map_bot]
    change RestrictionSubobjects.domain inverses T ⊓ RestrictionSubobjects.domain inverses _ = ⊥
    rw [RestrictionSubobjects.domain_pullback, ht]
    exact ForkSyntax.t0_consistency a b hd
  let d := EquivalenceSubobjects.orderIso equivalence X
  have hm : d T = propTheory a b := EquivalenceSubobjects.object_image equivalence _
  have hn : d ((Subobject.pullback ForkDerivation.negation).obj T) =
      (Subobject.pullback negation).obj (d T) :=
    FiniteLimitSubobjects.object_pullback realization ForkDerivation.negation T
  rw [← hm, ← hn, ← d.map_inf, hc, d.map_bot]

theorem formula_consistent (hd : a ⊓ b = ⊥) :
    formulaTheory a b ⊓ (Subobject.pullback (S).negationConstructor).obj (formulaTheory a b) = ⊥ := by
  have hn : (Subobject.pullback (S).negationConstructor).obj (erasedTheory a b) =
      (Subobject.pullback erase).obj ((Subobject.pullback negation).obj (propTheory a b)) := by
    rw [erasedTheory, ← Subobject.pullback_comp, negation_law, Subobject.pullback_comp]
  apply le_antisymm _ bot_le
  apply (inf_le_inf (formula_le a b) ((Subobject.pullback (S).negationConstructor).monotone
    (formula_le a b))).trans_eq
  change erasedTheory a b ⊓ (Subobject.pullback (S).negationConstructor).obj (erasedTheory a b) = ⊥
  rw [hn, erasedTheory, ← Subobject.inf_pullback, prop_consistent a b hd, PresentationLemmas.pullback_bot]

theorem consistent (hd : a ⊓ b = ⊥) :
    sentenceTheory a b ⊓ (Subobject.pullback (S).sentenceNegation).obj (sentenceTheory a b) = ⊥ := by
  rw [sentence_restriction, ← Subobject.pullback_comp,
    CategoricalSyntax.sentenceNegation_inclusion, Subobject.pullback_comp, ← Subobject.inf_pullback,
    formula_consistent a b hd, PresentationLemmas.pullback_bot]

def labelDomain (e : Idem EffectiveFork.V) : Subobject labels :=
  FiniteLimitSubobjects.object realization (Subobject.mk (EffectiveFork.domainInclusionTotal e))

theorem labelDomain_mk (e : Idem EffectiveFork.V) : labelDomain e =
    Subobject.mk (realization.map (EffectiveFork.domainInclusionTotal e)) :=
  FiniteLimitSubobjects.object_mk _ _

theorem signed_axioms : axiomImage a b = SignedFirstOrder.axioms (F) (labelDomain a) (labelDomain b) := by
  rw [signed_image, SignedFirstOrder.axioms, labelDomain_mk, labelDomain_mk,
    SubobjectImagePresentations.exists_mk, SubobjectImagePresentations.exists_mk]
  rfl

theorem signed_theory : sentenceTheory a b =
    (SignedFirstOrder.theory (F) (labelDomain a) (labelDomain b)).val := by
  unfold sentenceTheory
  rw [signed_axioms]
  rfl

theorem atomic_bounds :
    labelDomain a ≤ (Subobject.pullback (NullaryInterpretation.atomSentence (S))).obj (sentenceTheory a b) ∧
    labelDomain b ≤ (Subobject.pullback (NullaryInterpretation.atomSentence (S))).obj
      ((Subobject.pullback (S).sentenceNegation).obj (sentenceTheory a b)) := by
  rw [signed_theory]
  exact SignedFirstOrder.atomic_bounds (F) _ _

abbrev A := EffectiveFork.Recursion.toIdem EffectiveFork.Recursion.pair0
abbrev B := EffectiveFork.Recursion.toIdem EffectiveFork.Recursion.pair1

theorem inseparable : SubobjectInseparable (labelDomain A) (labelDomain B) := by
  apply EquivalenceSubobjects.inseparable equivalence
  apply (RestrictionSubobjects.inseparable_iff inverses _ _).mp
  rw [domain_inclusion, domain_inclusion]
  exact EffectiveFork.Recursion.image_pair_inseparable_v46

def theory : ((F).presentation labels).Theories :=
  SignedFirstOrder.theory (F) (labelDomain A) (labelDomain B)

theorem essentially_incomplete : ((F).presentation labels).EssentiallyIncomplete theory := by
  apply SignedFirstOrder.essential_incomplete_of_subobject_inseparable _ _ _ inseparable
  change theory.val ⊓ (Subobject.pullback (S).sentenceNegation).obj theory.val = ⊥
  rw [show theory.val = sentenceTheory A B from (signed_theory A B).symm]
  exact consistent A B EffectiveFork.Recursion.image_pair_inseparable_v46.disjoint

end CategoricalEssentialIncompleteness.V46.ForkInternalIncompleteness
