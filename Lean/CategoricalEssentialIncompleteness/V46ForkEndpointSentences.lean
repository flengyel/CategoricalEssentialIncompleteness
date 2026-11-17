/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ForkConservativeRestriction
public import CategoricalEssentialIncompleteness.V46ForkInternalIncompleteness

/-! # The two local sentence embeddings on the original endpoint codes -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.RestrictionCategory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.LocalConnectedness
namespace CategoricalEssentialIncompleteness.V46.ForkEndpointSentences
open ForkDerivation.Diagram ForkFirstOrderErasure ForkErasureClosure
open ForkInternalIncompleteness (A B)
open ForkPropositionalEmbedding (embedding)
open NumericalTuples (Point)
local notation "S" => firstOrder

def node (i : Bool) : WalkingSpan := if i then .left else .right
abbrev carrier (i : Bool) := (S).sentenceObject.obj (node i)
abbrev neg (i : Bool) := (S).sentenceNegation.app (node i)
def propPoint (i : Bool) (n : ℕ) : Point (sentences.obj (node i)) :=
  ⟨n, by cases i <;> exact Set.mem_univ _⟩
def embedded (i : Bool) (n : ℕ) : Point (carrier i) :=
  (embedding.app (node i)).toFun (propPoint i n)

theorem embedded_neg (i : Bool) (n : ℕ) :
    embedded i (ForkSyntax.negCode n) = (neg i).toFun (embedded i n) := by
  have hn : (negation.app (node i)).toFun (propPoint i n) = propPoint i (ForkSyntax.negCode n) := by
    apply Subtype.ext
    have h := ForkDerivation.component_map_mem (node i) ForkDerivation.negation (propPoint i n)
    cases i <;> exact (ForkSyntax.mem_natArrow ForkSyntax.negCode ForkSyntax.negCode_computable n _).mp h
  have he := NatTrans.congr_app ForkPropositionalEmbedding.negation (node i)
  exact (congrArg (embedding.app (node i)).toFun hn.symm).trans
    (congrArg (fun f => f.toFun (propPoint i n)) he)

def embeddedCode (i : Bool) (n : ℕ) : ℕ := NumericalTuples.code _ (embedded i n).val

theorem embeddedCode_computable (i : Bool) : Computable (embeddedCode i) := by
  apply (embedding.app (node i)).restrictedProgram_partrec.of_eq
  intro n
  exact (embedding.app (node i)).restrictedProgram_apply (propPoint i n)

/-- The component of the generated sentence theory at the selected endpoint. -/
def theorems (i : Bool) : Set (Point (carrier i)) :=
  Set.range ((sentenceTheory A B).arrow.app (node i)).toFun

theorem old_theorem (i : Bool) (n : ℕ)
    (hn : n ∈ EnumerableCarriers.support (ForkSyntax.endpointTheory i ForkSyntax.categoricalTheory)) :
    embedded i n ∈ theorems i := by
  let m := ForkDerivationImages.LiteralDiagram.theoremInclusion A B
  let T := sentenceTheory A B
  have h : ((Subobject.pullback embedding).obj T).Factors m := by
    rw [ForkConservativeRestriction.restriction_to_domain]
    exact Subobject.mk_factors_self _
  obtain ⟨k, hk⟩ := (Subobject.factors_iff _ _).mp ((pullback_factors_iff embedding T m).mp h)
  let x : Point ((ForkDerivationImages.LiteralDiagram.theoremObject A B).obj (node i)) :=
    ⟨n, by cases i <;> exact hn⟩
  have hx : (m.app (node i)).toFun x = propPoint i n := by
    apply Subtype.ext
    have hv := ForkDerivation.component_map_mem (node i)
      (EffectiveFork.domainInclusionTotal (ForkSyntax.t0 A B)) x
    cases i
    · change _ ∈ EnumerableCarriers.val (EnumerableCarriers.into
        (EffectiveFork.rightIdem (ForkSyntax.t0 A B))) n at hv
      rw [EnumerableCarriers.into, EnumerableCarriers.val_arrow] at hv
      exact ((EnumerableCarriers.mem_val_idem _ _ _).mp hv).2
    · change _ ∈ EnumerableCarriers.val (EnumerableCarriers.into
        (EffectiveFork.leftIdem (ForkSyntax.t0 A B))) n at hv
      rw [EnumerableCarriers.into, EnumerableCarriers.val_arrow] at hv
      exact ((EnumerableCarriers.mem_val_idem _ _ _).mp hv).2
  exact ⟨(k.app (node i)).toFun x, (congrArg (fun f => f.toFun x)
    (NatTrans.congr_app hk (node i))).trans (congrArg (embedding.app (node i)).toFun hx)⟩

/-- The exact coded range of any numerical presentation is c.e. -/
def codes {X Y : NumericalTuples.Object} (u : X ⟶ Y) : Set ℕ :=
  EnumerableCarriers.support (Ranges.range (NumericalTuples.comparisonMap u).hom)

theorem codes_re {X Y : NumericalTuples.Object} (u : X ⟶ Y) : REPred (· ∈ codes u) :=
  EnumerableCarriers.support_re _

theorem mem_codes {X Y : NumericalTuples.Object} (u : X ⟶ Y) (y : Point Y) :
    NumericalTuples.code _ y.val ∈ codes u ↔ y ∈ Set.range u.toFun := by
  rw [codes, EnumerableCarriers.support_range]
  constructor
  · rintro ⟨n, hn⟩
    obtain ⟨x, _, hx⟩ := (NumericalTuples.comparisonMap_graph u _ _).mp hn
    exact ⟨x, Subtype.ext (NumericalTuples.code_injective _ hx)⟩
  · rintro ⟨x, rfl⟩
    exact ⟨_, (NumericalTuples.comparisonMap_graph u _ _).mpr ⟨x, rfl, rfl⟩⟩

/-- Any c.e. local theorem set extending the selected component leaves a
sentence and its negation outside the set. -/
theorem extension_incomplete (i : Bool) (U : Set ℕ) (hu : REPred (· ∈ U))
    (he : ∀ x ∈ theorems i, NumericalTuples.code _ x.val ∈ U)
    (hc : ∀ x : Point (carrier i), NumericalTuples.code _ x.val ∈ U →
      NumericalTuples.code _ ((neg i).toFun x).val ∉ U) :
    ∃ x : Point (carrier i), NumericalTuples.code _ x.val ∉ U ∧
      NumericalTuples.code _ ((neg i).toFun x).val ∉ U := by
  let P : Set ℕ := (embeddedCode i) ⁻¹' U
  have hp : REPred (· ∈ P) := hu.comp (embeddedCode_computable i)
  obtain ⟨n, hn, hneg⟩ := ForkSyntax.endpoint_ce_extension_incomplete i P hp
    (fun n hn => he _ (old_theorem i n hn)) (by
      intro n h
      change NumericalTuples.code _ (embedded i (ForkSyntax.negCode n)).val ∉ U
      rw [embedded_neg]
      exact hc _ h)
  refine ⟨embedded i n, hn, ?_⟩
  rw [← embedded_neg]
  exact hneg

end CategoricalEssentialIncompleteness.V46.ForkEndpointSentences
