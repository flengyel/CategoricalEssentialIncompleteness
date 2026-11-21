/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ForkEndpointSentences

/-! # Proposition 10.8 for the signed fork and each endpoint separately -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.RestrictionCategory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.LocalConnectedness
namespace CategoricalEssentialIncompleteness.V46.ForkFirstOrderApplication
open ForkFirstOrderErasure ForkErasureClosure ForkEndpointSentences
open ForkInternalIncompleteness (A B)
open NumericalTuples (Point Tuple)
local notation "S" => firstOrder

variable (i : Bool)
abbrev eval := (evaluation WalkingSpan NumericalTuples.Object).obj (node i)

def localRules (H : Subobject (carrier i)) :=
  firstOrderRules ((S).logicalAxioms.app (node i)) ((S).sentenceInclusion.app (node i)) H.arrow
    (FirstOrderRuleTransport.mappedAll (eval i) (S).quantifierConstructor)
    (FirstOrderRuleTransport.mappedImp (eval i) (S).implicationConstructor)

def localProofs (H : Subobject (carrier i)) : Endofunctor.Algebra (localRules i H).inference :=
  NumericalDerivation.derivationAlgebra _
def localInitial (H : Subobject (carrier i)) : IsInitial (localProofs i H) :=
  NumericalDerivation.derivationInitial _

variable (Γ : Set (Tuple (carrier i).dimension)) (hΓ : REPred (· ∈ Γ))

/-- Restrict the given c.e. tuple set to the endpoint sentence carrier. -/
def axiomObject : NumericalTuples.Object :=
  ⟨(carrier i).dimension, Γ ∩ (carrier i).support, hΓ.and (carrier i).enumerable⟩

def axiomMap : axiomObject i Γ hΓ ⟶ carrier i where
  toFun x := ⟨x.val, x.property.2⟩
  represented := ⟨Part.some, Partrec.some, fun _ => rfl⟩

theorem axiom_membership (x : Point (carrier i)) :
    x ∈ Set.range (axiomMap i Γ hΓ).toFun ↔ x.val ∈ Γ :=
  ⟨fun ⟨y, hy⟩ => hy ▸ y.property.1, fun h => ⟨⟨x.val, h, x.property⟩, rfl⟩⟩

def localConclusion := FirstOrderReflection.conclusion (localProofs i) (imageSubobject (axiomMap i Γ hΓ))

/-- Membership is witnessed by a finite derivation with a sentence conclusion. -/
def closureSet : Set (Point (carrier i)) := Set.range (localConclusion i Γ hΓ).toFun

theorem closure_image : imageSubobject (localConclusion i Γ hΓ) =
    FirstOrderReflection.generated (localProofs i) (imageSubobject (axiomMap i Γ hΓ)) := rfl

theorem closure_codes_re : REPred (· ∈ codes (localConclusion i Γ hΓ)) := codes_re _

theorem endpoint (he : theorems i ⊆ closureSet i Γ hΓ)
    (hc : ∀ x ∈ closureSet i Γ hΓ, (neg i).toFun x ∉ closureSet i Γ hΓ) :
    ∃ x : Point (carrier i), x ∉ closureSet i Γ hΓ ∧ (neg i).toFun x ∉ closureSet i Γ hΓ := by
  let c := localConclusion i Γ hΓ
  obtain ⟨x, h, hn⟩ := extension_incomplete i (codes c) (closure_codes_re i Γ hΓ)
    (fun x hx => (mem_codes c x).mpr (he hx))
    (fun x hx hn => hc x ((mem_codes c x).mp hx) ((mem_codes c _).mp hn))
  exact ⟨x, fun hx => h ((mem_codes c x).mpr hx), fun hx => hn ((mem_codes c _).mpr hx)⟩

/-- Consistency, all closed consistent internal extensions, conservative
restriction to the original domain, and the two independent local assertions. -/
theorem printed_statement :
    (sentenceTheory A B ⊓ (Subobject.pullback (S).sentenceNegation).obj (sentenceTheory A B) = ⊥) ∧
    (∀ U : FirstOrderReflection.Theory proofFamily, sentenceTheory A B ≤ U.val →
      U.val ⊓ (Subobject.pullback (S).sentenceNegation).obj U.val = ⊥ →
        U.val ⊔ (Subobject.pullback (S).sentenceNegation).obj U.val ≠ ⊤) ∧
    (Subobject.pullback ForkPropositionalEmbedding.embedding).obj (sentenceTheory A B) =
      Subobject.mk (ForkDerivationImages.LiteralDiagram.theoremInclusion A B) ∧
    ∀ (k : Bool) (Δ : Set (Tuple (carrier k).dimension)) (hΔ : REPred (· ∈ Δ)),
      theorems k ⊆ closureSet k Δ hΔ →
      (∀ x ∈ closureSet k Δ hΔ, (neg k).toFun x ∉ closureSet k Δ hΔ) →
      ∃ x : Point (carrier k), x ∉ closureSet k Δ hΔ ∧ (neg k).toFun x ∉ closureSet k Δ hΔ := by
  refine ⟨ForkInternalIncompleteness.consistent A B EffectiveFork.Recursion.image_pair_inseparable_v46.disjoint,
    ?_, ForkConservativeRestriction.restriction_to_domain A B, endpoint⟩
  intro U he hc
  rw [ForkInternalIncompleteness.signed_theory] at he
  exact ForkInternalIncompleteness.essentially_incomplete.2 U he hc

end CategoricalEssentialIncompleteness.V46.ForkFirstOrderApplication
