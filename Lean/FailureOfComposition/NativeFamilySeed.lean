/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import FailureOfComposition.NativeFamilyFormulas

/-!
# A standard arithmetic seed for each fixed theory

PA proves the extraction sentence. Provability inclusion gives a proof in
the fixed target theory; the resulting standard code is then accepted in
every PA model. The theory quantifier precedes the seed witness.
-/

@[expose] public section

set_option autoImplicit false

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.Entailment
open scoped FFL.FirstOrder.Arithmetic

namespace FailureOfComposition.NativeFamilyExtraction

open FFL.FirstOrder.Arithmetic.Bootstrapping
open FailureOfComposition.NativeInternalGraphs
open FailureOfComposition.NativeInternalCorrectness
open FailureOfComposition.NativeInternalAxiomGraph

theorem exists_standard_extraction_seed
    (S : ArithmeticTheory) [S.Δ₁] [𝗣𝗔 ⪯ S]
    (M : 𝚺₁.Semisentence 1) (h k : ℕ) :
    ∃ seed : ℕ, ∀ (V : Type*) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔],
      (nativeProofCheckGraph (canonicalAxiomGraph S)).val.Evalb
        ![1, ORingStructure.numeral seed, (⌜extractionSeed M h k⌝ : V)] := by
  have hs : S ⊢ extractionSeed M h k := WeakerThan.pbl (extractionSeed_provable M h k)
  let d : S ⊢! extractionSeed M h k := hs.get
  refine ⟨(⌜d⌝ : ℕ), ?_⟩
  intro V _ _
  rw [nativeProofCheckGraph_correct (canonicalAxiomGraph_computational S)
    (canonicalAxiomGraph_theory S)]
  refine Or.inl ⟨rfl, ?_⟩
  rw [numeral_eq_natCast_app, coe_quote_proof_eq]
  exact proof_of_quote_proof d

end FailureOfComposition.NativeFamilyExtraction
