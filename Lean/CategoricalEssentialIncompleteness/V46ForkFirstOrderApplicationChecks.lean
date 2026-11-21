/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ForkFirstOrderApplication

/-! # Independent statement checks for v59 Proposition 10.8 -/

@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.RestrictionCategory
open CategoricalEssentialIncompleteness.LocalConnectedness
namespace CategoricalEssentialIncompleteness.V46.ForkFirstOrderApplicationChecks
open ForkDerivation.Diagram ForkFirstOrderErasure ForkErasureClosure
open ForkInternalIncompleteness (A B)
open ForkPropositionalEmbedding (embedding)
open ForkEndpointSentences (carrier node neg)
open ForkFirstOrderApplication (closureSet)
local notation "S" => firstOrder
local notation "T" => sentenceTheory A B

example (a b : Idem EffectiveFork.V) :
    axiomImage a b =
    imageSubobject (coprod.desc (labelInclusion a ≫ NullaryInterpretation.atomSentence (S))
      (labelInclusion b ≫ NullaryInterpretation.atomSentence (S) ≫ (S).sentenceNegation)) := rfl

example (a b : Idem EffectiveFork.V) :
    ClosedUnder ((S).logicalRules (axiomImage a b).arrow).inference
      ((Subobject.pullback erase).obj (propTheory a b)).arrow ∧
    formulaTheory a b ≤ (Subobject.pullback erase).obj (propTheory a b) :=
  ⟨closed a b, formula_le a b⟩

example (a b : Idem EffectiveFork.V) :
    ∃ f : realization.obj (ForkDerivation.proofObject a b) ⟶ (proofFamily (axiomImage a b)).a.left,
      f ≫ (proofFamily (axiomImage a b)).a.hom =
        realization.map (ForkDerivation.conclusion a b) ≫ embedding ≫ (S).sentenceInclusion :=
  ⟨_, ForkConservativeRestriction.embedDerivation_conclusion a b⟩

example (a b : Idem EffectiveFork.V) :
    (Subobject.pullback embedding).obj ((Subobject.pullback (S).sentenceInclusion).obj
      (formulaTheory a b)) = Subobject.mk (realization.map
        (EffectiveFork.domainInclusionTotal (ForkSyntax.t0 a b))) := by
  rw [← sentence_restriction]
  exact ForkConservativeRestriction.restriction_to_domain a b

example (a b : Idem EffectiveFork.V) (hd : a ⊓ b = ⊥) :
    sentenceTheory a b ⊓ (Subobject.pullback (S).sentenceNegation).obj (sentenceTheory a b) = ⊥ :=
  ForkInternalIncompleteness.consistent a b hd

example : SubobjectInseparable (ForkInternalIncompleteness.labelDomain A)
    (ForkInternalIncompleteness.labelDomain B) ∧
    ForkInternalIncompleteness.labelDomain A ≤
      (Subobject.pullback (NullaryInterpretation.atomSentence (S))).obj T ∧
    ForkInternalIncompleteness.labelDomain B ≤
      (Subobject.pullback (NullaryInterpretation.atomSentence (S))).obj
        ((Subobject.pullback (S).sentenceNegation).obj T) :=
  ⟨ForkInternalIncompleteness.inseparable, ForkInternalIncompleteness.atomic_bounds A B⟩

example (i : Bool) (U : Set ℕ) (hu : REPred (· ∈ U))
    (he : ∀ x ∈ Set.range ((T).arrow.app (node i)).toFun, NumericalTuples.code _ x.val ∈ U)
    (hc : ∀ x : NumericalTuples.Point (carrier i), NumericalTuples.code _ x.val ∈ U →
      NumericalTuples.code _ (((S).sentenceNegation.app (node i)).toFun x).val ∉ U) :
    ∃ x : NumericalTuples.Point (carrier i), NumericalTuples.code _ x.val ∉ U ∧
      NumericalTuples.code _ (((S).sentenceNegation.app (node i)).toFun x).val ∉ U :=
  ForkEndpointSentences.extension_incomplete i U hu he hc

/-- All clauses with the domain inclusion and local proof conclusions. -/
example :
    (T ⊓ (Subobject.pullback (S).sentenceNegation).obj T = ⊥) ∧
    (∀ W : FirstOrderReflection.Theory proofFamily, T ≤ W.val →
      W.val ⊓ (Subobject.pullback (S).sentenceNegation).obj W.val = ⊥ →
      W.val ⊔ (Subobject.pullback (S).sentenceNegation).obj W.val ≠ ⊤) ∧
    (Subobject.pullback embedding).obj T = Subobject.mk
      (realization.map (EffectiveFork.domainInclusionTotal ForkSyntax.categoricalTheory)) ∧
    ∀ (i : Bool) (Γ : Set (NumericalTuples.Tuple (carrier i).dimension)) (hΓ : REPred (· ∈ Γ)),
      let U := Set.range (ForkFirstOrderApplication.localConclusion i Γ hΓ).toFun
      Set.range ((T).arrow.app (node i)).toFun ⊆ U →
      (∀ x ∈ U, ((S).sentenceNegation.app (node i)).toFun x ∉ U) →
      ∃ x : NumericalTuples.Point (carrier i), x ∉ U ∧ ((S).sentenceNegation.app (node i)).toFun x ∉ U :=
  ForkFirstOrderApplication.printed_statement

#print axioms RuleClosureFactors.closed_iff
#print axioms RuleClosureFactors.firstOrder_closed
#print axioms RuleClosureFactors.propositional_mp
#print axioms ForkErasureClosure.signed_image
#print axioms ForkErasureClosure.signed_le
#print axioms ForkErasureClosure.generalization
#print axioms ForkErasureClosure.modus_ponens
#print axioms ForkErasureClosure.closed
#print axioms ForkErasureClosure.formula_le
#print axioms ForkErasureClosure.sentence_restriction
#print axioms ForkConservativeRestriction.translation
#print axioms ForkConservativeRestriction.embedDerivation_conclusion
#print axioms ForkConservativeRestriction.prop_le
#print axioms ForkConservativeRestriction.conservativity
#print axioms ForkConservativeRestriction.restriction_to_domain
#print axioms ForkInternalIncompleteness.domain_inclusion
#print axioms ForkInternalIncompleteness.prop_consistent
#print axioms ForkInternalIncompleteness.formula_consistent
#print axioms ForkInternalIncompleteness.consistent
#print axioms ForkInternalIncompleteness.signed_theory
#print axioms ForkInternalIncompleteness.atomic_bounds
#print axioms ForkInternalIncompleteness.inseparable
#print axioms ForkInternalIncompleteness.essentially_incomplete
#print axioms ForkEndpointSentences.embedded_neg
#print axioms ForkEndpointSentences.embeddedCode_computable
#print axioms ForkEndpointSentences.old_theorem
#print axioms ForkEndpointSentences.mem_codes
#print axioms ForkEndpointSentences.extension_incomplete
#print axioms ForkFirstOrderApplication.axiom_membership
#print axioms ForkFirstOrderApplication.localInitial
#print axioms ForkFirstOrderApplication.closure_image
#print axioms ForkFirstOrderApplication.closure_codes_re
#print axioms ForkFirstOrderApplication.endpoint
#print axioms ForkFirstOrderApplication.printed_statement

end CategoricalEssentialIncompleteness.V46.ForkFirstOrderApplicationChecks
