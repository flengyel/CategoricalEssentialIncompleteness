/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ExponentialPairing
public import CategoricalEssentialIncompleteness.V46SyntacticLists

/-! # Predicate-product comparison for exponential pairing -/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.Limits
open FailureOfComposition.ProofSearch FailureOfComposition.CodedObjectMembership
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates

namespace CategoricalEssentialIncompleteness.V46.ExponentialProducts

def carrier (C D : Carrier) : Carrier :=
  let G := ExponentialPairing.graph
  .mkSigma “n. ∃ a b, !G.val n a b ∧ !C.val a ∧ !D.val b”

def encodeGraph (C D : Carrier) : Graph :=
  let G := ExponentialPairing.graph
  .mkSigma “source target. ∃ a b, !pairDef.val source a b ∧
    !C.val a ∧ !D.val b ∧ !G.val target a b”

def decodeGraph (C D : Carrier) : Graph :=
  let G := ExponentialPairing.graph
  .mkSigma “source target. ∃ a b, !G.val source a b ∧
    !pairDef.val target a b ∧ !C.val a ∧ !D.val b”

section Models
variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

@[simp] theorem carrier_eval (C D : Carrier) (n : M) :
    (carrier C D).val.Evalb ![n] ↔
      ∃ a b : M, n = ExponentialPairing.code a b ∧ C.val.Evalb ![a] ∧ D.val.Evalb ![b] := by
  simp [carrier]

@[simp] theorem encodeGraph_eval (C D : Carrier) (source target : M) :
    (encodeGraph C D).val.Evalb ![source, target] ↔
      ∃ a b : M, source = Arithmetic.pair a b ∧ C.val.Evalb ![a] ∧
        D.val.Evalb ![b] ∧ target = ExponentialPairing.code a b := by
  simp [encodeGraph]

@[simp] theorem decodeGraph_eval (C D : Carrier) (source target : M) :
    (decodeGraph C D).val.Evalb ![source, target] ↔
      ∃ a b : M, source = ExponentialPairing.code a b ∧ target = Arithmetic.pair a b ∧
        C.val.Evalb ![a] ∧ D.val.Evalb ![b] := by
  simp [decodeGraph]

@[simp] theorem encodeGraph_pair (C D : Carrier) (a b target : M) :
    (encodeGraph C D).val.Evalb ![Arithmetic.pair a b, target] ↔
      C.val.Evalb ![a] ∧ D.val.Evalb ![b] ∧ target = ExponentialPairing.code a b := by
  rw [encodeGraph_eval]
  constructor
  · rintro ⟨c, d, h, hc, hd, ht⟩
    obtain ⟨rfl, rfl⟩ := (pair_eq_pair_iff _ _ _ _).mp h
    exact ⟨hc, hd, ht⟩
  · rintro ⟨ha, hb, ht⟩
    exact ⟨a, b, rfl, ha, hb, ht⟩

end Models

variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]

def encode (C D : Carrier) : GraphMorphism T (productCarrier C D) (carrier C D) where
  graph := encodeGraph C D
  support := by
    apply complete.{0} T
    intro M _ _
    let : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 := models_of_subtheory (U := T) inferInstance
    rw [models_iff, supportSentence_eval]
    intro source target h
    obtain ⟨a, b, hs, ha, hb, ht⟩ := (encodeGraph_eval C D source target).mp h
    exact ⟨(productCarrier_eval C D source).mpr ⟨a, b, hs, ha, hb⟩,
      (carrier_eval C D target).mpr ⟨a, b, ht, ha, hb⟩⟩
  total := by
    apply complete.{0} T
    intro M _ _
    let : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 := models_of_subtheory (U := T) inferInstance
    rw [models_iff, totalSentence_eval]
    intro source hs
    obtain ⟨a, b, rfl, ha, hb⟩ := (productCarrier_eval C D source).mp hs
    refine ⟨ExponentialPairing.code a b, (encodeGraph_pair C D a b _).mpr ⟨ha, hb, rfl⟩, ?_⟩
    intro target htarget
    exact ((encodeGraph_pair C D a b target).mp htarget).2.2

def decode (C D : Carrier) : GraphMorphism T (carrier C D) (productCarrier C D) where
  graph := decodeGraph C D
  support := by
    apply complete.{0} T
    intro M _ _
    let : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 := models_of_subtheory (U := T) inferInstance
    rw [models_iff, supportSentence_eval]
    intro source target h
    obtain ⟨a, b, hs, ht, ha, hb⟩ := (decodeGraph_eval C D source target).mp h
    exact ⟨(carrier_eval C D source).mpr ⟨a, b, hs, ha, hb⟩,
      (productCarrier_eval C D target).mpr ⟨a, b, ht, ha, hb⟩⟩
  total := by
    apply complete.{0} T
    intro M _ _
    let : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 := models_of_subtheory (U := T) inferInstance
    rw [models_iff, totalSentence_eval]
    intro source hs
    obtain ⟨a, b, hs, ha, hb⟩ := (carrier_eval C D source).mp hs
    refine ⟨Arithmetic.pair a b,
      (decodeGraph_eval C D source _).mpr ⟨a, b, hs, rfl, ha, hb⟩, ?_⟩
    intro target htarget
    obtain ⟨c, d, hc, ht, _, _⟩ := (decodeGraph_eval C D source target).mp htarget
    obtain ⟨rfl, rfl⟩ := ExponentialPairing.code_injective (hc.symm.trans hs)
    exact ht

/-- Both code translations are morphisms modulo T-provable graph equality, for arbitrary
Sigma-one coefficient carriers. -/
def rawProductIso (C D : PredicateCategory T) :
    CategoryTheory.Iso (C := PredicateCategory T) (productCarrier C D) (carrier C D) where
  hom := representedArrow T (encode T C D)
  inv := representedArrow T (decode T C D)
  hom_inv_id := by
    apply SyntacticPredicates.hom_ext T
    intro M _ _ source target
    let : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 := models_of_subtheory (U := T) inferInstance
    simp only [relation_comp, relation_class, relation_id]
    change (∃ mid : M, (encodeGraph C D).val.Evalb ![source, mid] ∧
      (decodeGraph C D).val.Evalb ![mid, target]) ↔ _
    constructor
    · rintro ⟨mid, he, hd⟩
      obtain ⟨a, b, hs, ha, hb, hm⟩ := (encodeGraph_eval C D source mid).mp he
      obtain ⟨c, d, hm', ht, _, _⟩ := (decodeGraph_eval C D mid target).mp hd
      obtain ⟨rfl, rfl⟩ := ExponentialPairing.code_injective (hm.symm.trans hm')
      exact ⟨(productCarrier_eval C D source).mpr ⟨a, b, hs, ha, hb⟩, ht.trans hs.symm⟩
    · rintro ⟨hs, htarget⟩
      subst target
      obtain ⟨a, b, rfl, ha, hb⟩ := (productCarrier_eval C D source).mp hs
      exact ⟨ExponentialPairing.code a b,
        (encodeGraph_pair C D a b _).mpr ⟨ha, hb, rfl⟩,
        (decodeGraph_eval C D _ _).mpr ⟨a, b, rfl, rfl, ha, hb⟩⟩
  inv_hom_id := by
    apply SyntacticPredicates.hom_ext T
    intro M _ _ source target
    let : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 := models_of_subtheory (U := T) inferInstance
    simp only [relation_comp, relation_class, relation_id]
    change (∃ mid : M, (decodeGraph C D).val.Evalb ![source, mid] ∧
      (encodeGraph C D).val.Evalb ![mid, target]) ↔ _
    constructor
    · rintro ⟨mid, hd, he⟩
      obtain ⟨a, b, hs, hm, ha, hb⟩ := (decodeGraph_eval C D source mid).mp hd
      obtain ⟨c, d, hm', _, _, ht⟩ := (encodeGraph_eval C D mid target).mp he
      obtain ⟨rfl, rfl⟩ := (pair_eq_pair_iff _ _ _ _).mp (hm.symm.trans hm')
      exact ⟨(carrier_eval C D source).mpr ⟨a, b, hs, ha, hb⟩, ht.trans hs.symm⟩
    · rintro ⟨hs, htarget⟩
      subst target
      obtain ⟨a, b, rfl, ha, hb⟩ := (carrier_eval C D source).mp hs
      exact ⟨Arithmetic.pair a b,
        (decodeGraph_eval C D _ _).mpr ⟨a, b, rfl, rfl, ha, hb⟩,
        (encodeGraph_pair C D a b _).mpr ⟨ha, hb, rfl⟩⟩

def chosenRawProductIso (C D : PredicateCategory T) :
    CategoryTheory.Iso (C := PredicateCategory T) (C ⨯ D) (productCarrier C D) where
  hom := SyntacticLists.toRawProduct T C D
  inv := SyntacticLists.fromRawProduct T C D
  hom_inv_id := SyntacticLists.toRaw_fromRaw T C D
  inv_hom_id := SyntacticLists.fromRaw_toRaw T C D

/-- The categorical binary product has the exponential numerical realization, through two
proved morphism isomorphisms. -/
def productIso (C D : PredicateCategory T) :
    CategoryTheory.Iso (C := PredicateCategory T) (C ⨯ D) (carrier C D) :=
  chosenRawProductIso T C D ≪≫ rawProductIso T C D

end CategoricalEssentialIncompleteness.V46.ExponentialProducts
