/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ForkConservativeRestriction
public import CategoricalEssentialIncompleteness.V46ForkInternalIncompleteness
public import CategoricalEssentialIncompleteness.V46AssociatedIncompleteness
public import CategoricalEssentialIncompleteness.V46SliceInseparability

/-! # First-order fork theories in the slice over a consistent extension -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness.V46.ForkAssociatedTheories
open ForkDerivation.Diagram ForkFirstOrderErasure ForkErasureClosure
open ForkInternalIncompleteness (A B)
open ForkPropositionalEmbedding (embedding)

abbrev presentation := ForkParameterizedDeduction.nullaryPresentations.presentation labels
abbrev base := sentenceTheory A B
abbrev refutation (U : Subobject firstOrder.sentenceObject) :=
  (Subobject.pullback firstOrder.sentenceNegation).obj U

/-- The chosen global theorem is the embedding of the original formal tautology. -/
def logicalTheorem : ⊤_ Object ⟶ firstOrder.sentenceObject := truth ≫ embedding

theorem logicalTheorem_factors : base.Factors logicalTheorem := by
  apply (pullback_factors_iff embedding base truth).mp
  rw [ForkConservativeRestriction.conservativity]
  let p := ForkPropositionalProofs.truth A B
  rw [← p.conclusion]
  exact imageSubobject_factors_comp_self _ _

variable (U : presentation.Theories) (hExt : base ≤ U.val)

def point : ⊤_ Object ⟶ (U.val : Object) :=
  U.val.factorThru logicalTheorem (Subobject.factors_of_le _ hExt logicalTheorem_factors)

theorem point_value : point U hExt ≫ U.val.arrow = truth ≫ embedding :=
  U.val.factorThru_arrow _ _

include hExt in
theorem base_domains (hc : U.val ⊓ refutation U.val = ⊥) :
    SubobjectInseparable U.val (refutation U.val) :=
  AssociatedCategory.extension_inseparable _ _ ForkInternalIncompleteness.inseparable
    (NullaryInterpretation.atomSentence firstOrder) firstOrder.sentenceNegation base U.val
    (ForkInternalIncompleteness.atomic_bounds A B).1
    (ForkInternalIncompleteness.atomic_bounds A B).2 hExt hc

local instance (P : Object) : Regular (Over P) := RegularSlices.regular P
local instance (P : Object) : FinitaryExtensive (Over P) := RegularSlices.finitaryExtensive P
local instance (P : Object) : PreservesFiniteLimits (constantFamilyFunctor P) :=
  SliceBaseChangeGeometry.constant_preservesFiniteLimits P

abbrev sliceProofs (P : Object) := ForkParameterizedDeduction.proofs labels P

def constantTheory : FirstOrderReflection.Theory (sliceProofs (U.val : Object)) :=
  AssociatedClosedTheories.constantTheory presentation (U.val : Object) (sliceProofs _)
    (ForkParameterizedDeduction.initial labels _) U

theorem constant_value : (constantTheory U).val =
    FiniteLimitSubobjects.object (constantFamilyFunctor (U.val : Object)) U.val := rfl

include hExt in
theorem essentially_incomplete (hc : U.val ⊓ refutation U.val = ⊥) :
    AssociatedClosedTheories.EssentiallyIncomplete presentation (U.val : Object)
      (sliceProofs _) (constantTheory U) := by
  apply (AssociatedClosedTheories.essential_incomplete_iff presentation (U.val : Object)
    (sliceProofs _) (ForkParameterizedDeduction.initial labels _)
    (point U hExt) terminalIsTerminal U hc).mp
  exact AssociatedCategory.essential_incomplete_of_reduction presentation _ _
    ForkInternalIncompleteness.inseparable (NullaryInterpretation.atomSentence firstOrder) base
    (ForkInternalIncompleteness.atomic_bounds A B).1
    (ForkInternalIncompleteness.atomic_bounds A B).2 U hExt hc

include hExt in
theorem slice_domains (hc : U.val ⊓ refutation U.val = ⊥) :
    SubobjectInseparable (constantTheory U).val
      ((Subobject.pullback ((constantFamilyFunctor (U.val : Object)).map
        firstOrder.sentenceNegation)).obj (constantTheory U).val) :=
  SliceInseparability.constant (point U hExt) terminalIsTerminal
    firstOrder.sentenceNegation U.val (base_domains U hExt hc)

local instance (P : Object) : Regular (PartialMaps.Tot (Over P)) :=
  SliceInseparability.PartialTotals.regular (Over P)
local instance (P : Object) : FinitaryExtensive (PartialMaps.Tot (Over P)) :=
  SliceInseparability.PartialTotals.extensive (Over P)

def theoremDomain := FiniteLimitSubobjects.object
  (PartialMaps.totalEquivalence (D := Over (U.val : Object))).functor (constantTheory U).val

def negation := (PartialMaps.totalEquivalence (D := Over (U.val : Object))).functor.map
  ((constantFamilyFunctor (U.val : Object)).map firstOrder.sentenceNegation)

include hExt in
theorem domains_inseparable (hc : U.val ⊓ refutation U.val = ⊥) :
    SubobjectInseparable (theoremDomain U)
      ((Subobject.pullback (negation U)).obj (theoremDomain U)) := by
  have h := SliceInseparability.PartialTotals.inseparable (Over (U.val : Object))
    _ _ (slice_domains U hExt hc)
  rw [FiniteLimitSubobjects.object_pullback] at h
  exact h

include hExt in
/-- The theorem and refutation subobjects of every consistent extension in the partial-map
category have join strictly below the top subobject. -/
theorem actual_incompleteness (hc : U.val ⊓ refutation U.val = ⊥) :
    (theoremDomain U ⊓ (Subobject.pullback (negation U)).obj (theoremDomain U) = ⊥) ∧
    ∀ W : Subobject ((PartialMaps.totalEquivalence (D := Over (U.val : Object))).functor.obj
        (constantFamily (U.val : Object) firstOrder.sentenceObject)),
      theoremDomain U ≤ W → W ⊓ (Subobject.pullback (negation U)).obj W = ⊥ →
        W ⊔ (Subobject.pullback (negation U)).obj W ≠ ⊤ := by
  have hi := domains_inseparable U hExt hc
  exact ⟨hi.1, fun W hW hcW => SliceInseparability.noncoverage (negation U) _ hi W hW hcW⟩

end CategoricalEssentialIncompleteness.V46.ForkAssociatedTheories
