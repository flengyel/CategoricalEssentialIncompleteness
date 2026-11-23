/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ForkTupleEvaluationGraphs
public import CategoricalEssentialIncompleteness.V46ForkTupleEvaluationProducts

/-! # The Turing morphism of the numerical tuple diagram

Theorem B.7 applies to every ordinary partial span with a tuple diagram as parameter.
The endpoint evaluator uses the same acceptable numbering as the central evaluator.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.RestrictionCategory
open CategoricalEssentialIncompleteness.LocalConnectedness
namespace CategoricalEssentialIncompleteness.V46.ForkTupleEvaluation

open ForkDiagonalObstruction (tupleDiagram tupleSpace)
open EnumerableCarriers (val)
open FailureOfComposition.Kleene (eval)

abbrev universal : ForkSpans := ⟨tupleDiagram⟩
abbrev endpoint : TupleSpans := ⟨tupleSpace 2⟩

def endpointIso : tupleCode.obj endpoint ≅ EffectiveFork.natCarrier :=
  (PreservesRestriction.totalInclusion EnumerableCarriers.Carrier).mapIso (eqToIso codedEndpointEq)

def tau : forkProduct universal universal ⟶ universal :=
  FullRestrictionProducts.evaluator forkCode codedForkProducts _ forkProductIso universal
    (TuringRestrictionEquivalence.conjugate codedForkProducts labelIso EffectiveFork.tau)

def endpointTau : tupleProduct endpoint endpoint ⟶ endpoint :=
  FullRestrictionProducts.evaluator tupleCode codedTupleProducts _ tupleProductIso endpoint
    (TuringRestrictionEquivalence.conjugate codedTupleProducts endpointIso EffectiveFork.endpointEvaluator)

theorem tau_isTuring : @RecursionCategory.IsTuringMorphism ForkSpans _ forkProducts.pcategoryStruct
    forkProducts.pcategoryLaws universal universal universal tau :=
  FullRestrictionProducts.evaluator_isTuring _ forkCode_restriction _ _ _ _ _
    (TuringRestrictionEquivalence.conjugate_turing _ labelIso _ codedFork_turing)

theorem endpointTau_isTuring :
    @RecursionCategory.IsTuringMorphism TupleSpans _ tupleProducts.pcategoryStruct
      tupleProducts.pcategoryLaws endpoint endpoint endpoint endpointTau :=
  FullRestrictionProducts.evaluator_isTuring _ tupleCode_restriction _ _ _ _ _
    (TuringRestrictionEquivalence.conjugate_turing _ endpointIso _ codedEndpoint_turing)

theorem tau_code : forkCode.map tau = (forkProductIso universal universal).hom ≫
    EffectiveFork.productMap labelIso.hom labelIso.hom ≫ EffectiveFork.tau ≫ labelIso.inv :=
  forkCode.map_preimage _

theorem endpointTau_code : tupleCode.map endpointTau = (tupleProductIso endpoint endpoint).hom ≫
    EnumerableCarriers.partialProdMap endpointIso.hom endpointIso.hom ≫
      EffectiveFork.endpointEvaluator ≫ endpointIso.inv := tupleCode.map_preimage _

theorem val_eqToHom {A B : EnumerableCarriers.Total} (h : A = B) (n m : ℕ) :
    m ∈ val (eqToHom h).hom n ↔ n ∈ A.obj.support ∧ m = n := by
  subst B
  exact mem_supportIdentity _ _ _

private theorem endpointSupport (n : ℕ) : n ∈ (tupleCode.obj endpoint).support := by
  change n ∈ (NumericalTuples.codedObject (tupleSpace 2)).obj.support
  rw [codedEndpointEq]
  exact Set.mem_univ _

theorem labelCode_hom (n m : ℕ) : m ∈ val endpointIso.hom n ↔ m = n :=
  (val_eqToHom codedEndpointEq n m).trans (and_iff_right (endpointSupport n))

theorem labelCode_inv (n m : ℕ) : m ∈ val endpointIso.inv n ↔ m = n :=
  (val_eqToHom codedEndpointEq.symm n m).trans (and_iff_right (Set.mem_univ n))

/-- The numerical value on a pair of arguments in the two total-product charts. -/
def binaryValue {X Y Z : TupleSpans} (f : tupleProduct X Y ⟶ Z) (a b : ℕ) : Part ℕ :=
  val ((tupleProductIso X Y).inv ≫ tupleCode.map f) (Nat.pair a b)

theorem endpointTau_value (k p l x : ℕ) : binaryValue endpointTau (Nat.pair k p) (Nat.pair l x) =
    eval p (Nat.pair l x) := by
  apply Part.ext
  intro n
  unfold binaryValue
  rw [endpointTau_code, Iso.inv_hom_id_assoc]
  simp only [EnumerableCarriers.mem_val_comp, EnumerableCarriers.mem_partialProdMap_iff,
    labelCode_hom, labelCode_inv, Nat.unpair_pair]
  change (∃ m, ((Nat.unpair m).1 = Nat.pair k p ∧ (Nat.unpair m).2 = Nat.pair l x) ∧
    ∃ w, w ∈ EffectiveFork.endpointEval m ∧ n = w) ↔ _
  constructor
  · rintro ⟨m, ⟨hm, hn⟩, w, hw, rfl⟩
    simpa only [EffectiveFork.endpointEval, hm, hn, Nat.unpair_pair] using hw
  · intro h
    exact ⟨Nat.pair (Nat.pair k p) (Nat.pair l x), by simp only [Nat.unpair_pair, and_self],
      n, by simpa only [EffectiveFork.endpointEval, Nat.unpair_pair] using h, rfl⟩

def endpointProgram {Z : TupleSpans} (f : tupleProduct Z endpoint ⟶ endpoint) :
    EnumerableCarriers.product (tupleCode.obj Z) EffectiveFork.natCarrier ⟶ EffectiveFork.natCarrier :=
  EnumerableCarriers.partialProdMap (𝟙 _) endpointIso.inv ≫
    (tupleProductIso Z endpoint).inv ≫ tupleCode.map f ≫ endpointIso.hom

def endpointIndex {Z : TupleSpans} (f : tupleProduct Z endpoint ⟶ endpoint) (n : ℕ) : ℕ :=
  EffectiveFork.specialize (EffectiveFork.program (endpointProgram f)) n

theorem endpointIndex_computable {Z : TupleSpans} (f : tupleProduct Z endpoint ⟶ endpoint) :
    Computable (endpointIndex f) := EffectiveFork.specialize_computable _

def endpointParameter {Z : TupleSpans} (f : tupleProduct Z endpoint ⟶ endpoint) : Z ⟶ endpoint :=
  tupleCode.preimage (EffectiveFork.endpointEncoding (endpointIndex f) (endpointIndex_computable f) ≫
    endpointIso.inv)

theorem endpointParameter_total {Z : TupleSpans} (f : tupleProduct Z endpoint ⟶ endpoint) :
    isTotal (endpointParameter f) := by
  apply PreservesRestriction.reflects_total (F := tupleCode) tupleCode_restriction
  rw [endpointParameter, tupleCode.map_preimage]
  exact isTotal_comp (EnumerableCarriers.totalFromFunction_total _ _ _) (iso_total endpointIso.symm)

theorem endpointParameter_graph {Z : TupleSpans} (f : tupleProduct Z endpoint ⟶ endpoint)
    (z : NumericalTuples.Point Z.obj) (q : NumericalTuples.Point endpoint.obj) :
    Graph (endpointParameter f) z q ↔ q.val = (0, endpointIndex f (NumericalTuples.code _ z.val)) := by
  unfold Graph endpointParameter
  rw [tupleCode.map_preimage, EnumerableCarriers.mem_val_comp]
  change (∃ n, n ∈ val (EffectiveFork.endpointEncoding _ _) _ ∧ _ ∈ val endpointIso.inv n) ↔ _
  simp only [labelCode_inv, exists_eq_right']
  rw [EffectiveFork.mem_endpointEncoding]
  have hs := z.property
  have hc := (NumericalTuples.code_mem_codedSupport Z.obj z.val).mpr hs
  change _ ∈ NumericalTuples.codedSupport Z.obj ∧ _ = _ ↔ _
  rw [and_iff_right hc]
  change NumericalTuples.code 2 q.val =
    NumericalTuples.code 2 (0, endpointIndex f (NumericalTuples.code _ z.val)) ↔ _
  exact (NumericalTuples.code_injective 2).eq_iff

end CategoricalEssentialIncompleteness.V46.ForkTupleEvaluation
