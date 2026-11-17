/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ForkAssociatedCategories

/-! # Independent statement checks for manuscript v60 Corollary 10.9 -/

@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.RestrictionCategory
open CategoricalEssentialIncompleteness.LocalConnectedness
namespace CategoricalEssentialIncompleteness.V46.ForkAssociatedCategoriesChecks
open ForkDerivation.Diagram ForkFirstOrderErasure ForkErasureClosure ForkAssociatedTheories
open ForkInternalIncompleteness (A B)
open ForkPropositionalEmbedding (embedding)
open ForkAssociatedCategories (comparison printedStatement)
local notation "T" => sentenceTheory A B
variable (U : (ForkParameterizedDeduction.nullaryPresentations.presentation labels).Theories)
variable (i : (T : Object) ⟶ (U.val : Object)) [Mono i] (hi : i ≫ U.val.arrow = (T).arrow)
variable (hc : U.val ⊓ (Subobject.pullback firstOrder.sentenceNegation).obj U.val = ⊥)

local notation "Bᵤ" => constantFamilyFunctor (U.val : Object)
local instance (P : Object) : Regular (Over P) := RegularSlices.regular P
local instance (P : Object) : FinitaryExtensive (Over P) := RegularSlices.finitaryExtensive P
local instance (P : Object) : PreservesFiniteLimits (constantFamilyFunctor P) :=
  SliceBaseChangeGeometry.constant_preservesFiniteLimits P
local instance (P : Object) : Regular (PartialMaps.Tot (Over P)) :=
  SliceInseparability.PartialTotals.regular (Over P)
local instance (P : Object) : FinitaryExtensive (PartialMaps.Tot (Over P)) :=
  SliceInseparability.PartialTotals.extensive (Over P)

omit [Mono i] in
include hi in
example : ∃ p : ⊤_ Object ⟶ (U.val : Object), p ≫ U.val.arrow = truth ≫ embedding :=
  ⟨point U (Subobject.le_of_comm i hi), point_value U _⟩

omit [Mono i] in
example (X : PartialMaps.Par (Over (T : Object))) :
    ((comparison U i).obj X).obj = (Over.map i).obj X.obj := rfl

omit [Mono i] in
example {X Y : PartialMaps.Par (Over (T : Object))} (f : X.obj ⟶ Y.obj) :
    (comparison U i).map (PartialMaps.ofTotal (X := X) (Y := Y) f) =
      PartialMaps.ofTotal ((Over.map i).map f) :=
  MonicPartialSliceComparison.postcompose_total i f

/-- The constant-family theorem subobject has the printed inclusion 1_U × u. -/
example : (constantTheory U).val = Subobject.mk ((Bᵤ).map U.val.arrow) := rfl

include hi hc in
example :
    Nonempty (CompatibleSplitSlices.TuringData (PartialMaps.Par (Over (T : Object)))) ∧
    Nonempty (CompatibleSplitSlices.TuringData (PartialMaps.Par (Over (U.val : Object)))) ∧
    (comparison U i).Full ∧ (comparison U i).Faithful ∧
    (¬ IsIso i → ¬ (comparison U i).EssSurj) ∧
    (let t := Subobject.mk ((Bᵤ).map U.val.arrow)
     let ν := (Bᵤ).map firstOrder.sentenceNegation
     t ⊓ (Subobject.pullback ν).obj t = ⊥ ∧
       ∀ W : FirstOrderReflection.Theory
           (ForkParameterizedDeduction.proofs labels (U.val : Object)),
         t ≤ W.val → W.val ⊓ (Subobject.pullback ν).obj W.val = ⊥ →
           W.val ⊔ (Subobject.pullback ν).obj W.val ≠ ⊤) ∧
    (let H := (PartialMaps.totalEquivalence (D := Over (U.val : Object))).functor
     let t := FiniteLimitSubobjects.object H (Subobject.mk ((Bᵤ).map U.val.arrow))
     SubobjectInseparable t
       ((Subobject.pullback (H.map ((Bᵤ).map firstOrder.sentenceNegation))).obj t)) := by
  let h := printedStatement U i hi hc
  exact ⟨⟨h.source⟩, ⟨h.target⟩, h.full, h.faithful, h.proper, h.essential, h.inseparable⟩

omit [Mono i] in
include hi hc in
example :
    let t := theoremDomain U
    let r := (Subobject.pullback (ForkAssociatedTheories.negation U)).obj t
    ∃ hd : t ⊓ r = ⊥,
      rst (ForkAssociatedCategories.decision U hd) =
        (RestrictionSubobjects.domain MonicPartialSliceComparison.inverses (t ⊔ r)).hom ∧
      t.arrow.hom ≫ ForkAssociatedCategories.decision U hd =
        (Two.constant (t : PartialMaps.Tot (Over (U.val : Object))) true).hom ∧
      r.arrow.hom ≫ ForkAssociatedCategories.decision U hd =
        (Two.constant (r : PartialMaps.Tot (Over (U.val : Object))) false).hom ∧
      ¬ RestrictionRetraction.HasTotalExtension (ForkAssociatedCategories.decision U hd) :=
  ForkAssociatedCategories.boolean_obstruction U i hi hc

#print axioms TuringRestrictionEquivalence.conjugate_turing
#print axioms TuringRestrictionEquivalence.transport
#print axioms MonicPartialSliceComparison.inverses
#print axioms MonicPartialSliceComparison.full
#print axioms MonicPartialSliceComparison.faithful
#print axioms MonicPartialSliceComparison.proper
#print axioms logicalTheorem_factors
#print axioms point_value
#print axioms base_domains
#print axioms essentially_incomplete
#print axioms domains_inseparable
#print axioms actual_incompleteness
#print axioms ForkAssociatedCategories.turing
#print axioms ForkAssociatedCategories.boolean_obstruction
#print axioms ForkAssociatedCategories.printedStatement

end CategoricalEssentialIncompleteness.V46.ForkAssociatedCategoriesChecks
