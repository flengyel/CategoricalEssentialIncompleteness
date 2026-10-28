/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import FailureOfComposition.NativeFamilyFormulas

/-!
# Internal proofs of true fixed Sigma-one instances

The formula is fixed externally; its valuation ranges over the entire PA
model. Formalized completeness supplies existence of a proof code, not a
primitive-recursive selection of such a code.
-/

set_option autoImplicit false

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic

namespace FailureOfComposition.NativeFamilyExtraction

open FFL.FirstOrder.Arithmetic.Bootstrapping
open FFL.FirstOrder.Arithmetic.Bootstrapping.Arithmetic
open FailureOfComposition.NativeInternalSyntax
open FailureOfComposition.NativeInternalGraphs
open FailureOfComposition.NativeInternalCorrectness
open FailureOfComposition.NativeInternalAxiomGraph

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]

/-- Literal numeral substitution, including nonstandard numerals. -/
noncomputable def instanceValue {n : ℕ} (phi : ArithmeticSemisentence n)
    (v : Fin n → V) : V := substNumerals (⌜phi⌝ : V) v

/-- The exact bridge to the typed substitution used in Foundation's D3. -/
theorem toNumVec_instance {n : ℕ} (phi : ArithmeticSemisentence n) (v : Fin n → V) :
    ((Bootstrapping.Semiformula.subst (toNumVec (k := 0) v)
      (⌜phi⌝ : Bootstrapping.Semiformula V ℒₒᵣ n)).val) = instanceValue phi v := by
  rfl

theorem instanceValue_nat {n : ℕ} (phi : ArithmeticSemisentence n) (v : Fin n → ℕ) :
    instanceValue phi v = Encodable.encode
      ((Rew.subst (fun i => (↑(v i) : ArithmeticSemiterm Empty 0))) ▹ phi) := by
  unfold instanceValue
  convert (substNumerals_app_quote (V := ℕ) phi v) using 1 <;>
    simp only [natCast_nat, Sentence.quote_eq_encode_nat]

/-- PA-minus provability inclusion suffices for the fixed-formula witness
theorem. All valuation entries, and the witness, are internal elements. -/
theorem exists_accepted_sigma_instance
    (S : ArithmeticTheory) [S.Δ₁] [𝗣𝗔⁻ ⪯ S]
    {A : 𝚺₁.Semisentence 2} (hA : ComputationalAxiomGraph (V := V) A)
    (hS : TheoryAxiomAgreement (V := V) A S)
    {n : ℕ} (phi : 𝚺₁.Semisentence n) (v : Fin n → V)
    (hv : phi.val.Evalb v) :
    ∃ p : V, (nativeProofCheckGraph A).val.Evalb ![1, p, instanceValue phi.val v] := by
  have hc := bold_sigma_one_complete S phi.sigma_prop hv
  have hp := (tprovable_iff_provable (T := S)).mp hc
  rw [toNumVec_instance] at hp
  obtain ⟨p, hp⟩ := hp
  refine ⟨p, ?_⟩
  rw [nativeProofCheckGraph_correct hA hS]
  exact Or.inl ⟨rfl, hp⟩

theorem exists_canonical_sigma_instance
    (S : ArithmeticTheory) [S.Δ₁] [𝗣𝗔⁻ ⪯ S]
    {n : ℕ} (phi : 𝚺₁.Semisentence n) (v : Fin n → V)
    (hv : phi.val.Evalb v) :
    ∃ p : V, (nativeProofCheckGraph (canonicalAxiomGraph S)).val.Evalb
      ![1, p, instanceValue phi.val v] :=
  exists_accepted_sigma_instance S (canonicalAxiomGraph_computational S)
    (canonicalAxiomGraph_theory S) phi v hv

end FailureOfComposition.NativeFamilyExtraction
