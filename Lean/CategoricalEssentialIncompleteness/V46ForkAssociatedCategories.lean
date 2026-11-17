/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ForkAssociatedTheories
public import CategoricalEssentialIncompleteness.V46MonicPartialSliceComparison
public import CategoricalEssentialIncompleteness.V46TuringRestrictionEquivalence
public import CategoricalEssentialIncompleteness.V46NativeSplitSlices

/-! # The split Turing categories of first-order fork theory extensions -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory CategoryTheory.Limits CategoryTheory.RestrictionCategory
open CategoricalEssentialIncompleteness.LocalConnectedness
namespace CategoricalEssentialIncompleteness.V46.ForkAssociatedCategories
open RestrictionSubobjects

section Slice
variable {D C : Type u} [Category.{v} D] [Category.{v} C] [HasPullbacks D]
  [PCategoryStruct C] [PCategory C] [ρ : RestrictionCategory C]
  (hρ : PCategory.inducedRestriction = ρ) [Splits C] [HasPullbacks (Tot C)]
  (m : MonoInverses C) (E : D ≌ Tot C) (U : D)
  (Q : C) (τ : PCategoryStruct.nearProd Q Q ⟶ Q) (hτ : RecursionCategory.IsTuringMorphism τ)
  (hQ : ∀ X : C, ∃ (j : X ⟶ Q) (s : Q ⟶ X), isTotal j ∧ j ≫ s = 𝟙 X)

/-- Base equivalence induces an equivalence on the two actual partial-map
slices. Transport the parameterized evaluator and total retracts across it. -/
def sliceTuring : CompatibleSplitSlices.TuringData (PartialMaps.Par (Over U)) := by
  subst ρ
  let T := E.functor.obj U
  let H := Over T
  let e := PartialMaps.totalEquivalence (D := H)
  letI : HasPullbacks (PartialMaps.Tot H) :=
    Adjunction.hasLimitsOfShape_of_equivalence e.inverse
  let G := (Over.postEquiv U E).trans e
  let invs : MonoInverses (PartialMaps.Par H) := MonicPartialSliceComparison.inverses
  let k := MonicPartialMapEquivalence.equivalence invs G
  exact TuringRestrictionEquivalence.transport k
    (MonicPartialMapEquivalence.preserves_restrictions invs G)
    (PartialSliceProducts.restrictionProducts m T) (PartialSliceTuring.constantObject T Q)
    (SliceProductTuring.evaluator m T τ) (SliceProductTuring.evaluator_isTuring m T τ hτ)
    (PartialSliceRetractions.exists_total_retract m T hQ)
    (PartialSliceRetractions.terminalObject T) (PartialSliceRetractions.terminate m T)
    (PartialSliceRetractions.terminate_total m T) (PartialSliceRetractions.terminate_naturality m T)
    (PartialSliceRetractions.terminate_unique m T)
end Slice

open ForkDerivation.Diagram ForkFirstOrderErasure ForkAssociatedTheories

theorem restriction_eq : (PCategory.inducedRestriction : RestrictionCategory EffectiveFork.Object) =
    EffectiveFork.forkRestriction :=
  NativeSplitSlices.restriction_ext _ _ (fun f => EffectiveFork.induced_restriction f)

def turing (P : Object) : CompatibleSplitSlices.TuringData (PartialMaps.Par (Over P)) :=
  sliceTuring restriction_eq ForkInternalIncompleteness.inverses equivalence.symm P
    EffectiveFork.V EffectiveFork.tau EffectiveFork.tau_isTuring (fun X => by
      obtain ⟨j, s, hj, hjs, _⟩ := EffectiveFork.dominance X
      exact ⟨j, s, hj, hjs⟩)

variable (U : presentation.Theories)
local instance (P : Object) : Regular (Over P) := RegularSlices.regular P
local instance (P : Object) : FinitaryExtensive (Over P) := RegularSlices.finitaryExtensive P
local instance (P : Object) : PreservesFiniteLimits (constantFamilyFunctor P) :=
  SliceBaseChangeGeometry.constant_preservesFiniteLimits P
local instance (P : Object) : Regular (PartialMaps.Tot (Over P)) :=
  SliceInseparability.PartialTotals.regular (Over P)
local instance (P : Object) : FinitaryExtensive (PartialMaps.Tot (Over P)) :=
  SliceInseparability.PartialTotals.extensive (Over P)

variable (i : (base : Object) ⟶ (U.val : Object)) (hi : i ≫ U.val.arrow = base.arrow)

include hi in
theorem extension : base ≤ U.val := Subobject.le_of_comm i hi

abbrev comparison := MonicPartialSliceComparison.postcompose i

/-- The Boolean morphism on the actual total-category theorem and refutation domains. -/
def decision (hd : theoremDomain U ⊓ (Subobject.pullback (ForkAssociatedTheories.negation U)).obj
    (theoremDomain U) = ⊥) :=
  BooleanPartialDecision.decision MonicPartialSliceComparison.inverses (theoremDomain U)
    ((Subobject.pullback (ForkAssociatedTheories.negation U)).obj (theoremDomain U)) hd

include hi in
theorem boolean_obstruction (hc : U.val ⊓ refutation U.val = ⊥) :
    let a := theoremDomain U
    let b := (Subobject.pullback (ForkAssociatedTheories.negation U)).obj a
    ∃ hd : a ⊓ b = ⊥,
      rst (decision U hd) = (domain MonicPartialSliceComparison.inverses (a ⊔ b)).hom ∧
      a.arrow.hom ≫ decision U hd =
        (Two.constant (a : PartialMaps.Tot (Over (U.val : Object))) true).hom ∧
      b.arrow.hom ≫ decision U hd =
        (Two.constant (b : PartialMaps.Tot (Over (U.val : Object))) false).hom ∧
      ¬ RestrictionRetraction.HasTotalExtension (decision U hd) := by
  have h := domains_inseparable U (extension U i hi) hc
  let m : MonoInverses (PartialMaps.Par (Over (U.val : Object))) :=
    MonicPartialSliceComparison.inverses
  exact ⟨h.1, BooleanPartialDecision.domain_eq m _ _ h.1,
    BooleanPartialDecision.positive_value m _ _ h.1,
    BooleanPartialDecision.negative_value m _ _ h.1,
    (BooleanPartialDecision.inseparable_iff_noTotalExtension m _ _ h.1).mp h⟩

/-- The two Turing structures, the specified postcomposition functor and
the conclusions for the full slice over every consistent closed extension. -/
structure Application where
  source : CompatibleSplitSlices.TuringData (PartialMaps.Par (Over (base : Object)))
  target : CompatibleSplitSlices.TuringData (PartialMaps.Par (Over (U.val : Object)))
  full : (comparison U i).Full
  faithful : (comparison U i).Faithful
  proper : ¬ IsIso i → ¬ (comparison U i).EssSurj
  essential : AssociatedClosedTheories.EssentiallyIncomplete presentation (U.val : Object)
    (sliceProofs _) (constantTheory U)
  inseparable : SubobjectInseparable (theoremDomain U)
    ((Subobject.pullback (ForkAssociatedTheories.negation U)).obj (theoremDomain U))

variable [Mono i]

def printedStatement (hc : U.val ⊓ refutation U.val = ⊥) : Application U i where
  source := turing _
  target := turing _
  full := MonicPartialSliceComparison.full i
  faithful := MonicPartialSliceComparison.faithful i
  proper := MonicPartialSliceComparison.proper i
  essential := essentially_incomplete U (extension U i hi) hc
  inseparable := domains_inseparable U (extension U i hi) hc

end CategoricalEssentialIncompleteness.V46.ForkAssociatedCategories
