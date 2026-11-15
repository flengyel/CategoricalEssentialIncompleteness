/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module
public import CategoricalEssentialIncompleteness.V46MillerAssociatedTheories
public import CategoricalEssentialIncompleteness.V46SliceInseparability
public import CategoricalEssentialIncompleteness.V46AssociatedClosedTheories

/-! # Miller essential incompleteness in every associated slice -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness.V46.Miller.AssociatedIncompleteness
open AssociatedData AssociatedTheories
variable (a : Point)
local instance (P : Total.CanonicalTotal a) : Regular (Over P) := RegularSlices.regular P
local instance (P : Total.CanonicalTotal a) : FinitaryExtensive (Over P) :=
  RegularSlices.finitaryExtensive P
local instance (P : Total.CanonicalTotal a) : PreservesFiniteLimits (constantFamilyFunctor P) :=
  SliceBaseChangeGeometry.constant_preservesFiniteLimits P
local instance {Z U : Total.CanonicalTotal a} (p : Z ⟶ U) (h : IsTerminal Z) :
    PreservesFiniteLimits (SliceBaseChangeGeometry.evaluation p h) :=
  SliceBaseChangeGeometry.evaluation_preservesFiniteLimits p h

abbrev sliceProofs (P : Total.CanonicalTotal a) := ParameterizedDeduction.proofs a (syntaxData a) P
abbrev sliceInitial (P : Total.CanonicalTotal a) := ParameterizedDeduction.initial a (syntaxData a) P
variable (U : Theory a)

def constantTheory : FirstOrderReflection.Theory (sliceProofs a (U.val : Total.CanonicalTotal a)) :=
  (SliceClosedTheories.constantTheoryFunctor (U.val : Total.CanonicalTotal a)
    (proofs a) (initial a) (sliceProofs a _) (sliceInitial a _)).obj U

theorem constantTheory_value : (constantTheory a U).val =
    FiniteLimitSubobjects.object (constantFamilyFunctor (U.val : Total.CanonicalTotal a)) U.val := rfl

def evaluatedTheory (W : FirstOrderReflection.Theory
    (sliceProofs a (U.val : Total.CanonicalTotal a))) : Theory a := by
  let A := SliceSubobjectPredicates.evaluate (point a U) (pointDomain_terminal a) W.val
  refine ⟨A, ?_⟩
  have h := RetractedClosedTheories.closed_back (constantFamilyFunctor (U.val : Total.CanonicalTotal a))
    (SliceBaseChangeGeometry.evaluation (point a U) (pointDomain_terminal a))
    (SliceBaseChangeGeometry.ordinaryRetraction (point a U) (pointDomain_terminal a))
    (proofs a) (initial a) (sliceProofs a _) (sliceInitial a _) W.val W.property
  have he := SliceSubobjectPredicates.evaluate_eq_retraction (point a U) (pointDomain_terminal a) W.val
  change FirstOrderReflection.generated (proofs a) A = A
  dsimp only [A]
  rw [he]
  exact h

/-- The quantified extension is an arbitrary closed slice theory, with
arbitrary dependence on U. -/
theorem every_consistent_extension_incomplete (ha : IsMiller a) (hExt : base a ≤ U.val)
    (W : FirstOrderReflection.Theory (sliceProofs a (U.val : Total.CanonicalTotal a)))
    (hW : (constantTheory a U).val ≤ W.val)
    (hcW : W.val ⊓ (Subobject.pullback
      ((constantFamilyFunctor (U.val : Total.CanonicalTotal a)).map
        (syntaxData a).sentenceNegation)).obj W.val = ⊥) :
    W.val ⊔ (Subobject.pullback ((constantFamilyFunctor (U.val : Total.CanonicalTotal a)).map
      (syntaxData a).sentenceNegation)).obj W.val ≠ ⊤ := by
  intro hcomplete
  let W₀ := evaluatedTheory a U W
  have hb : U.val ≤ W₀.val := by
    have h := SliceSubobjectPredicates.evaluate_monotone (point a U) (pointDomain_terminal a) hW
    rw [constantTheory_value, SliceSubobjectPredicates.evaluate_constant] at h
    exact h
  exact (global_incompleteness a ha W₀ (hExt.trans hb)
    (SliceSubobjectPredicates.evaluate_consistency (point a U) (pointDomain_terminal a)
      (syntaxData a).sentenceNegation W.val hcW)).2
    (SliceSubobjectPredicates.evaluate_completeness (point a U) (pointDomain_terminal a)
      (syntaxData a).sentenceNegation W.val hcomplete)

theorem essentially_incomplete (ha : IsMiller a) (hExt : base a ≤ U.val)
    (hc : U.val ⊓ (refutation a U) = ⊥) :
    ((constantTheory a U).val ⊓ (Subobject.pullback
      ((constantFamilyFunctor (U.val : Total.CanonicalTotal a)).map
        (syntaxData a).sentenceNegation)).obj (constantTheory a U).val = ⊥) ∧
    ∀ W : FirstOrderReflection.Theory (sliceProofs a (U.val : Total.CanonicalTotal a)),
      (constantTheory a U).val ≤ W.val →
      W.val ⊓ (Subobject.pullback ((constantFamilyFunctor (U.val : Total.CanonicalTotal a)).map
        (syntaxData a).sentenceNegation)).obj W.val = ⊥ →
      W.val ⊔ (Subobject.pullback ((constantFamilyFunctor (U.val : Total.CanonicalTotal a)).map
        (syntaxData a).sentenceNegation)).obj W.val ≠ ⊤ :=
  ⟨SliceSubobjectPredicates.constant_consistency (U.val : Total.CanonicalTotal a)
    (syntaxData a).sentenceNegation U.val hc,
    every_consistent_extension_incomplete a U ha hExt⟩

theorem constant_inseparable (ha : IsMiller a) (hExt : base a ≤ U.val)
    (hc : U.val ⊓ (refutation a U) = ⊥) :
    SubobjectInseparable (constantTheory a U).val
      ((Subobject.pullback ((constantFamilyFunctor (U.val : Total.CanonicalTotal a)).map
        (syntaxData a).sentenceNegation)).obj (constantTheory a U).val) :=
  SliceInseparability.constant (point a U) (pointDomain_terminal a)
    (syntaxData a).sentenceNegation U.val (global_incompleteness a ha U hExt hc).1

local instance partialTotalRegular (P : Total.CanonicalTotal a) :
    Regular (PartialMaps.Tot (Over P)) := SliceInseparability.PartialTotals.regular (Over P)
local instance partialTotalExtensive (P : Total.CanonicalTotal a) :
    FinitaryExtensive (PartialMaps.Tot (Over P)) :=
  SliceInseparability.PartialTotals.extensive (Over P)

/-- This is the actual theorem-domain subobject in the total category of
Par(D_a/U), under its canonical equivalence with D_a/U. -/
def actualTheoryDomain :=
  FiniteLimitSubobjects.object
    (PartialMaps.totalEquivalence (D := Over (U.val : Total.CanonicalTotal a))).functor
    (constantTheory a U).val

def actualNegation :=
  (PartialMaps.totalEquivalence (D := Over (U.val : Total.CanonicalTotal a))).functor.map
    ((constantFamilyFunctor (U.val : Total.CanonicalTotal a)).map (syntaxData a).sentenceNegation)

theorem actual_domains_inseparable (ha : IsMiller a) (hExt : base a ≤ U.val)
    (hc : U.val ⊓ (refutation a U) = ⊥) :
    SubobjectInseparable (actualTheoryDomain a U)
      ((Subobject.pullback (actualNegation a U)).obj (actualTheoryDomain a U)) := by
  have h := SliceInseparability.PartialTotals.inseparable (Over (U.val : Total.CanonicalTotal a))
    _ _ (constant_inseparable a U ha hExt hc)
  rw [FiniteLimitSubobjects.object_pullback] at h
  exact h

/-- This statement quantifies over all subobjects in the total category of
the actual associated partial-map category. In particular, no closed
consistent extension is required to be a constant family. -/
theorem actual_essentially_incomplete (ha : IsMiller a) (hExt : base a ≤ U.val)
    (hc : U.val ⊓ (refutation a U) = ⊥) :
    (actualTheoryDomain a U ⊓ (Subobject.pullback (actualNegation a U)).obj
      (actualTheoryDomain a U) = ⊥) ∧
    ∀ W : Subobject ((PartialMaps.totalEquivalence
        (D := Over (U.val : Total.CanonicalTotal a))).functor.obj
          (constantFamily (U.val : Total.CanonicalTotal a) (syntaxData a).sentenceObject)),
      actualTheoryDomain a U ≤ W →
      W ⊓ (Subobject.pullback (actualNegation a U)).obj W = ⊥ →
      W ⊔ (Subobject.pullback (actualNegation a U)).obj W ≠ ⊤ := by
  have hi := actual_domains_inseparable a U ha hExt hc
  exact ⟨hi.1, fun W hW hcW => SliceInseparability.noncoverage
    (actualNegation a U) (actualTheoryDomain a U) hi W hW hcW⟩

end CategoricalEssentialIncompleteness.V46.Miller.AssociatedIncompleteness
