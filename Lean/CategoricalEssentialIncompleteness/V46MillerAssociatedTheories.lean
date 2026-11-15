/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module
public import CategoricalEssentialIncompleteness.V46MillerAssociatedData
public import CategoricalEssentialIncompleteness.V46RestrictionSubobjectRanges
public import CategoricalEssentialIncompleteness.V46RestrictionSubobjectInseparability

/-! # Miller incompleteness for every closed internal extension -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.RestrictionCategory
open CategoricalEssentialIncompleteness.LocalConnectedness
namespace CategoricalEssentialIncompleteness.V46.Miller.AssociatedTheories
open RestrictionSubobjects AssociatedData
variable (a : Point)

theorem inverses : MonoInverses (SplitObject (Uniform.PointObject a)) :=
  fun m => Total.mono_has_partial_inverse a m

local instance : WeakChoice (SplitObject (Uniform.PointObject a)) := weakChoice (inverses a)

theorem generated_domain (A : Subobject (syntaxData a).sentenceObject) :
    domain (inverses a) (FirstOrderReflection.generated (proofs a) A) =
      CanonicalAxiomIncompleteness.theoremIdem a A.arrow :=
  domain_image (inverses a) (FirstOrderReflection.conclusion (proofs a) A)

theorem theory_domain (U : Theory a) :
    CanonicalAxiomIncompleteness.theoremIdem a U.val.arrow = domain (inverses a) U.val := by
  rw [← generated_domain, U.property]

def refutation (U : Theory a) : Subobject (syntaxData a).sentenceObject :=
  (Subobject.pullback (syntaxData a).sentenceNegation).obj U.val

theorem refutation_domain (U : Theory a) :
    CanonicalAxiomIncompleteness.refutationIdem a U.val.arrow =
      domain (inverses a) (refutation a U) := by
  change Idem.pull (syntaxData a).sentenceNegation.hom
    (CanonicalAxiomIncompleteness.theoremIdem a U.val.arrow) = _
  rw [theory_domain]
  exact (domain_pullback (inverses a) (syntaxData a).sentenceNegation U.val).symm

theorem base_domain : domain (inverses a) (base a) =
    CanonicalIncompleteness.theoremIdem a (RealClosedAxioms.theoryAxioms a)
      (RealClosedAxioms.theoryAxioms_enumerable a) :=
  domain_image (inverses a) _

/-- The Miller assumption and the printed extension/consistency equations
suffice; generation and idempotent comparisons are proved above. -/
theorem global_incompleteness (ha : IsMiller a) (U : Theory a)
    (hExt : base a ≤ U.val)
    (hc : U.val ⊓ (refutation a U) = ⊥) :
    SubobjectInseparable U.val (refutation a U) ∧ U.val ⊔ refutation a U ≠ ⊤ := by
  let e := orderIso (inverses a) (syntaxData a).sentenceObject
  have ht := theory_domain a U
  have hr := refutation_domain a U
  have hx : CanonicalIncompleteness.theoremIdem a (RealClosedAxioms.theoryAxioms a)
      (RealClosedAxioms.theoryAxioms_enumerable a) ≤
      CanonicalAxiomIncompleteness.theoremIdem a U.val.arrow := by
    rw [ht, ← base_domain]
    exact (domain_le_iff (inverses a) _ _).mpr hExt
  have hc' : CanonicalAxiomIncompleteness.theoremIdem a U.val.arrow ⊓
      Idem.pull (syntaxData a).sentenceNegation.hom
        (CanonicalAxiomIncompleteness.theoremIdem a U.val.arrow) = ⊥ := by
    change CanonicalAxiomIncompleteness.theoremIdem a U.val.arrow ⊓
      CanonicalAxiomIncompleteness.refutationIdem a U.val.arrow = ⊥
    rw [ht, hr]
    change e U.val ⊓ e (refutation a U) = ⊥
    rw [← e.map_inf, hc, e.map_bot]
  have hh := CanonicalAxiomIncompleteness.printed_categorical_incompleteness a U.val.arrow ha hx hc'
  have hi : Inseparable (domain (inverses a) U.val) (domain (inverses a) (refutation a U)) := by
    simpa only [ht, hr] using hh.1
  refine ⟨(inseparable_iff (inverses a) _ _).mp hi, ?_⟩
  intro hcomplete
  apply hh.2
  rw [ht, hr]
  change e U.val ⊔ e (refutation a U) = ⊤
  rw [← e.map_sup, hcomplete, e.map_top]

end CategoricalEssentialIncompleteness.V46.Miller.AssociatedTheories
