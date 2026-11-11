/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.ClassicalSplitMaps
public import CategoricalEssentialIncompleteness.ArithmeticSyntax
public import CategoricalEssentialIncompleteness.ArithmeticEnumerableSupports

/-! # Sentence and finite-proof objects in `Split(Rec)`

For a c.e. theory we use finite LK derivations from its Craig presentation.
Craig axioms carry finite enumeration witnesses. The proof carrier is kept
distinct from raw original-theory proof codes; the comparison below identifies
its conclusion range exactly with the original theory's theorem codes.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open Encodable CategoryTheory CategoryTheory.RestrictionCategory
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic

namespace CategoricalEssentialIncompleteness.LocalConnectedness.ArithmeticApplication

open ClassicalPrograms PartialFunctions

abbrev sentenceSet := ArithmeticSyntax.validSentenceCodes
abbrev sentenceSet_re : REPred (· ∈ sentenceSet) := ArithmeticSyntax.validSentenceCodes_recursive.to_re

def sentenceObject : SplitObject Rec := ceObject sentenceSet sentenceSet_re

def theoremCodes (T : ArithmeticTheory) : Set ℕ :=
  {n | ∃ φ : ArithmeticSentence, encode φ = n ∧ T ⊢ φ}

@[simp] theorem mem_theoremCodes_encode (T : ArithmeticTheory) (φ : ArithmeticSentence) :
    encode φ ∈ theoremCodes T ↔ T ⊢ φ := by
  constructor
  · rintro ⟨ψ, he, hψ⟩
    exact encode_injective he ▸ hψ
  · intro h; exact ⟨φ, rfl, h⟩

theorem theoremCodes_subset (T : ArithmeticTheory) : theoremCodes T ⊆ sentenceSet := by
  rintro n ⟨φ, rfl, _⟩
  exact ⟨φ, rfl⟩

theorem theoremCodes_mono {T T' : ArithmeticTheory} [T ⪯ T'] : theoremCodes T ⊆ theoremCodes T' := by
  rintro n ⟨φ, he, hφ⟩
  exact ⟨φ, he, WeakerThan.pbl hφ⟩

theorem craig_proof_iff (T : ArithmeticTheory) [T.RE] (φ : ArithmeticSentence) :
    (∃ d : ℕ, Proof T.craig d (encode φ)) ↔ T ⊢ φ := by
  change Provable T.craig (encode φ) ↔ T ⊢ φ
  rw [← Sentence.quote_eq_encode_nat, provable_iff_provable]
  exact ⟨fun h => WeakerThan.pbl (𝓢 := T.craig) (𝓣 := T) h,
    fun h => WeakerThan.pbl (𝓢 := T) (𝓣 := T.craig) h⟩

theorem theoremCodes_re (T : ArithmeticTheory) [T.RE] : REPred (· ∈ theoremCodes T) := by
  have hp : REPred (Provable T.craig (V := ℕ)) := rePred_iff_sigma1.mpr inferInstance
  apply (sentenceSet_re.and hp).of_eq
  intro n
  constructor
  · rintro ⟨⟨φ, rfl⟩, hd⟩
    exact ⟨φ, rfl, (craig_proof_iff T φ).mp hd⟩
  · rintro ⟨φ, rfl, hφ⟩
    exact ⟨⟨φ, rfl⟩, (craig_proof_iff T φ).mpr hφ⟩

def craigProofCarrier (T : ArithmeticTheory) [T.RE] : Set ℕ :=
  {p | Arithmetic.pi₂ p ∈ sentenceSet ∧ Proof T.craig (Arithmetic.pi₁ p) (Arithmetic.pi₂ p)}

theorem conclusionFunction_computable : Computable (Arithmetic.pi₂ : ℕ → ℕ) :=
  computable_iff_sigma1.mpr inferInstance

theorem craigProofCarrier_re (T : ArithmeticTheory) [T.RE] : REPred (· ∈ craigProofCarrier T) := by
  have hp : 𝚺₁-Predicate fun p : ℕ => Proof T.craig (Arithmetic.pi₁ p) (Arithmetic.pi₂ p) := by
    definability
  exact (sentenceSet_re.comp conclusionFunction_computable).and (rePred_iff_sigma1.mpr hp)

def proofObject (T : ArithmeticTheory) [T.RE] : SplitObject Rec :=
  ceObject (craigProofCarrier T) (craigProofCarrier_re T)

def conclusion (T : ArithmeticTheory) [T.RE] : proofObject T ⟶ sentenceObject :=
  totalArrow (craigProofCarrier_re T) sentenceSet_re Arithmetic.pi₂ conclusionFunction_computable
    (fun _ h => h.1)

theorem conclusion_total (T : ArithmeticTheory) [T.RE] : isTotal (conclusion T) :=
  totalArrow_isTotal (craigProofCarrier_re T) sentenceSet_re Arithmetic.pi₂ conclusionFunction_computable
    (fun _ h => h.1)

theorem proof_conclusion_range (T : ArithmeticTheory) [T.RE] (n : ℕ) :
    (∃ p ∈ craigProofCarrier T, Arithmetic.pi₂ p = n) ↔ n ∈ theoremCodes T := by
  constructor
  · rintro ⟨p, ⟨hn, hp⟩, he⟩
    rw [he] at hn hp
    obtain ⟨φ, hφ⟩ := hn
    refine ⟨φ, hφ, (craig_proof_iff T φ).mp ?_⟩
    exact ⟨Arithmetic.pi₁ p, hφ ▸ hp⟩
  · rintro ⟨φ, rfl, hφ⟩
    obtain ⟨d, hd⟩ := (craig_proof_iff T φ).mpr hφ
    refine ⟨Arithmetic.pair d (encode φ), ?_, ?_⟩
    · simpa only [craigProofCarrier, Set.mem_setOf_eq, Arithmetic.pi₁_pair, Arithmetic.pi₂_pair]
        using And.intro (show encode φ ∈ sentenceSet from ⟨φ, rfl⟩) hd
    · exact Arithmetic.pi₂_pair _ _

def theoremIdem (T : ArithmeticTheory) [T.RE] : Idem sentenceObject :=
  SplitObject.relativeIdem (supportIdem (theoremCodes T) (theoremCodes_re T))
    (supportIdem_le (theoremCodes_re T) sentenceSet_re (theoremCodes_subset T))

theorem conclusion_range (T : ArithmeticTheory) [T.RE] :
    Ranges.range (conclusion T) = theoremIdem T := by
  apply SplitObject.baseIdem_injective
  apply Idem.ext
  apply J.map_injective
  change J.map ((Ranges.range ((conclusion T).hom)).hom) =
    J.map ((supportIdem (theoremCodes T) (theoremCodes_re T)).hom)
  have hr := inclusionRangeFunctor.map_range ((conclusion T).hom)
  change J.map ((Ranges.range ((conclusion T).hom)).hom) =
    (Ranges.range (J.map ((conclusion T).hom))).hom at hr
  rw [hr]
  apply PFun.ext
  intro x y
  rw [mem_range]
  change (∃ p, x ∈ restrictedFunction (craigProofCarrier T) Arithmetic.pi₂ p) ∧ y = x ↔
    y ∈ supportIdentity (theoremCodes T) x
  rw [mem_supportIdentity]
  apply and_congr_left
  intro _
  have he : (∃ p, x ∈ restrictedFunction (craigProofCarrier T) Arithmetic.pi₂ p) ↔
      ∃ p ∈ craigProofCarrier T, Arithmetic.pi₂ p = x := by
    constructor
    · rintro ⟨p, hp⟩
      obtain ⟨hC, he⟩ := (mem_restrictedFunction _ _ p x).mp hp
      exact ⟨p, hC, he.symm⟩
    · rintro ⟨p, hp, he⟩
      exact ⟨p, (mem_restrictedFunction _ _ p x).mpr ⟨hp, he.symm⟩⟩
  exact he.trans (proof_conclusion_range T x)

end CategoricalEssentialIncompleteness.LocalConnectedness.ArithmeticApplication
