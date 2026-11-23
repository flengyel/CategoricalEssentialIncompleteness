/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46PartialMapFunctor
public import CategoricalEssentialIncompleteness.V46NumericalForkPartialMaps
public import CategoricalEssentialIncompleteness.V46MonicSpanValues
public import CategoricalEssentialIncompleteness.EffectiveForkEvaluation

/-! # Component evaluation of partial spans of numerical tuple diagrams

The functors of Proposition 10.1 evaluate both legs of an ordinary monic span.
The partial function represented by the resulting span is the corresponding
component of the numerical fork morphism.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.RestrictionCategory
open CategoricalEssentialIncompleteness.LocalConnectedness

namespace CategoricalEssentialIncompleteness.V46.ForkTupleEvaluation

abbrev Diagram := NumericalForkPartialMaps.Diagram
abbrev ForkSpans := PartialMaps.Par Diagram
abbrev TupleSpans := PartialMaps.Par NumericalTuples.Object
abbrev forkCode := NumericalForkPartialMaps.equivalence.functor
abbrev tupleCode := NumericalTuples.numericalPartialMapEquivalence.functor

abbrev evaluation (j : WalkingSpan) : ForkSpans ⥤ TupleSpans :=
  PartialMaps.inducedFunctor ((CategoryTheory.evaluation WalkingSpan NumericalTuples.Object).obj j)

theorem evaluation_span (j : WalkingSpan) {X Y : ForkSpans} (s : PartialMaps.Raw X Y) :
    (evaluation j).map (PartialMaps.ofSpan s) = PartialMaps.ofSpan
      (⟨s.apex.obj j, s.l.app j, s.r.app j, by infer_instance, by trivial⟩ :
        PartialMaps.Raw ((evaluation j).obj X) ((evaluation j).obj Y)) := rfl

theorem evaluation_restriction (j : WalkingSpan) : PreservesRestriction (evaluation j) :=
  fun f => PartialMaps.inducedFunctor_restriction _ f

def component {X Y : ForkSpans} (j : WalkingSpan) (f : forkCode.obj X ⟶ forkCode.obj Y) :
    tupleCode.obj ((evaluation j).obj X) ⟶ tupleCode.obj ((evaluation j).obj Y) := by
  rcases j with _ | (_ | _)
  exacts [f.center, f.left, f.right]

private theorem component_inverse {X Y : EffectiveFork.Total} (j : EffectiveFork.Component)
    (m : X ⟶ Y) [Mono m]
    (n : (⟨(EffectiveFork.evaluation j).obj X.obj⟩ : EnumerableCarriers.Total) ⟶
      ⟨(EffectiveFork.evaluation j).obj Y.obj⟩) [Mono n]
    (h : (EffectiveFork.evaluation j).map m.hom = n.hom) :
    (EffectiveFork.evaluation j).map (PartialSpans.inverse m) = PartialSpans.inverse n := by
  let F := EffectiveFork.evaluation j
  apply MonicSpanValues.partial_inverse_unique n.hom
  · rw [← h, ← F.map_comp, PartialSpans.hom_inverse, F.map_id]
  · rw [← h, ← F.map_comp, PartialSpans.inverse_hom]
    exact (EffectiveFork.evaluationRangeFunctor j).map_restrict _
  · exact PartialSpans.hom_inverse n
  · exact PartialSpans.inverse_hom n

private theorem component_span {X Y : ForkSpans} (s : PartialMaps.Raw X Y) (j : WalkingSpan) :
    tupleCode.map ((evaluation j).map (PartialMaps.ofSpan s)) =
      component j (forkCode.map (PartialMaps.ofSpan s)) := by
  let m := NumericalForkPartialMaps.totalEquivalence.functor.map s.l
  rcases j with _ | (_ | _)
  · let n := NumericalTuples.comparison.map (s.l.app .zero)
    change PartialSpans.inverse n ≫ _ = (PartialSpans.inverse m).center ≫ _
    rw [← component_inverse .center m n rfl]
    rfl
  · let n := NumericalTuples.comparison.map (s.l.app .left)
    change PartialSpans.inverse n ≫ _ = (PartialSpans.inverse m).left ≫ _
    rw [← component_inverse .left m n rfl]
    rfl
  · let n := NumericalTuples.comparison.map (s.l.app .right)
    change PartialSpans.inverse n ≫ _ = (PartialSpans.inverse m).right ≫ _
    rw [← component_inverse .right m n rfl]
    rfl

theorem evaluation_value {X Y : ForkSpans} (j : WalkingSpan) (f : X ⟶ Y) :
    tupleCode.map ((evaluation j).map f) = component j (forkCode.map f) := by
  induction f using Quotient.inductionOn with | _ s => exact component_span s j

theorem evaluation_range {X Y : ForkSpans} (j : WalkingSpan) (f : X ⟶ Y) :
    (evaluation j).map (Ranges.range f).hom = (Ranges.range ((evaluation j).map f)).hom := by
  apply tupleCode.map_injective
  have ht : tupleCode.map (Ranges.range ((evaluation j).map f)).hom =
      (Ranges.range (tupleCode.map ((evaluation j).map f))).hom :=
    PartialMapEquivalence.preserves_ranges NumericalTuples.equivalence _
  rw [ht, evaluation_value, evaluation_value, NumericalForkPartialMaps.preserves_ranges]
  rcases j with _ | (_ | _) <;> rfl

theorem tupleCode_restriction : PreservesRestriction tupleCode :=
  fun f => PartialMapEquivalence.preserves_restrictions NumericalTuples.equivalence f

theorem forkCode_restriction : PreservesRestriction forkCode :=
  fun f => NumericalForkPartialMaps.preserves_restrictions f

universe u v u' v'
section
variable {A : Type u} {B : Type u'} [Category.{v} A] [Category.{v'} B]
variable (F : A ⥤ B) [F.Full] [F.Faithful]

@[instance_reducible] def zeroMorphisms [HasZeroMorphisms B] : HasZeroMorphisms A where
  zero _ _ := ⟨F.preimage 0⟩
  comp_zero := by
    intro X Y f Z
    apply F.map_injective
    change F.map (f ≫ F.preimage 0) = F.map (F.preimage 0)
    rw [F.map_comp, F.map_preimage, F.map_preimage, comp_zero]
  zero_comp := by
    intro X Y Z f
    apply F.map_injective
    change F.map (F.preimage 0 ≫ f) = F.map (F.preimage 0)
    rw [F.map_comp, F.map_preimage, F.map_preimage, zero_comp]

variable [RestrictionCategory A] [RestrictionCategory B] (hF : PreservesRestriction F)

def idemOrderIso (X : A) : Idem X ≃o Idem (F.obj X) where
  toEquiv := hF.mapIdemEquiv X
  map_rel_iff' {a b} := by
    change F.map a.hom ≫ F.map b.hom = F.map a.hom ↔ a.hom ≫ b.hom = a.hom
    rw [← F.map_comp, F.map_injective.eq_iff]

@[instance_reducible] def binaryJoins [BinaryJoins B] : BinaryJoins A where
  join {X} a b := (idemOrderIso F hF X).symm (idemOrderIso F hF X a ⊔ idemOrderIso F hF X b)
  le_left {X} _ _ := (idemOrderIso F hF X).le_symm_apply.mpr le_sup_left
  le_right {X} _ _ := (idemOrderIso F hF X).le_symm_apply.mpr le_sup_right
  least {X} _ _ _ ha hb := (idemOrderIso F hF X).symm_apply_le.mpr
    (sup_le ((idemOrderIso F hF X).monotone ha) ((idemOrderIso F hF X).monotone hb))
end

instance : HasZeroMorphisms ForkSpans := zeroMorphisms forkCode
instance : HasZeroMorphisms TupleSpans := zeroMorphisms tupleCode
instance : BinaryJoins ForkSpans := binaryJoins forkCode forkCode_restriction
instance : BinaryJoins TupleSpans := binaryJoins tupleCode tupleCode_restriction

theorem evaluation_zero (j : WalkingSpan) (X Y : ForkSpans) :
    (evaluation j).map (0 : X ⟶ Y) = 0 := by
  apply tupleCode.map_injective
  rw [evaluation_value]
  change component j (forkCode.map (forkCode.preimage 0)) = tupleCode.map (tupleCode.preimage 0)
  rw [forkCode.map_preimage, tupleCode.map_preimage]
  rcases j with _ | (_ | _) <;> rfl

def componentIdem {X : ForkSpans} (j : WalkingSpan) (a : Idem (forkCode.obj X)) :
    Idem (tupleCode.obj ((evaluation j).obj X)) := by
  rcases j with _ | (_ | _)
  exacts [EffectiveFork.centerIdem a, EffectiveFork.leftIdem a, EffectiveFork.rightIdem a]

theorem componentIdem_hom {X : ForkSpans} (j : WalkingSpan) (a : Idem (forkCode.obj X)) :
    (componentIdem j a).hom = component j a.hom := by rcases j with _ | (_ | _) <;> rfl

theorem componentIdem_sup {X : ForkSpans} (j : WalkingSpan) (a b : Idem (forkCode.obj X)) :
    componentIdem j (a ⊔ b) = componentIdem j a ⊔ componentIdem j b := by
  rcases j with _ | (_ | _) <;> rfl

def evaluatedIdem {X : ForkSpans} (j : WalkingSpan) (a : Idem X) : Idem ((evaluation j).obj X) :=
  PreservesRestriction.mapIdem (F := evaluation j) (evaluation_restriction j) a

theorem evaluation_sup (j : WalkingSpan) {X : ForkSpans} (a b : Idem X) :
    evaluatedIdem j (a ⊔ b) =
      evaluatedIdem j a ⊔ evaluatedIdem j b := by
  let E := idemOrderIso tupleCode tupleCode_restriction ((evaluation j).obj X)
  let D := idemOrderIso forkCode forkCode_restriction X
  have he (c : Idem X) : E (evaluatedIdem j c) = componentIdem j (D c) := by
    apply Idem.ext
    rw [componentIdem_hom]
    exact evaluation_value j c.hom
  apply E.injective
  rw [E.map_sup, he, he, he, D.map_sup, componentIdem_sup]

end CategoricalEssentialIncompleteness.V46.ForkTupleEvaluation
