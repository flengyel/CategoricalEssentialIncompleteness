/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import FailureOfComposition.NativeMembershipPreservation
public import FailureOfComposition.NativeMembershipPR

/-!
# Native assembly from supplied totality and membership proofs

The fixed arithmetic schemas have standard seeds after the theory is fixed.
An internal proof of the acceptance assertion is supplied existentially by
Sigma-one completeness. The explicit constructor consumes that extra proof
`a`; the existence endpoint asserts no primitive-recursive selector `a(e)`.
The final hypotheses are proof acceptances only, not actual computation or
membership truth.
-/

@[expose] public section

set_option autoImplicit false

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open scoped FFL.FirstOrder.Arithmetic

namespace FailureOfComposition.NativeMembershipAssembly

open FFL.FirstOrder.Arithmetic.Bootstrapping
open FailureOfComposition.NativeFamilyExtraction
open FailureOfComposition.NativeInternalGraphs
open FailureOfComposition.NativeInternalCorrectness
open FailureOfComposition.NativeInternalAxiomGraph

private theorem exists_standard_seed_for (S : ArithmeticTheory) [S.Δ₁]
    (phi : ArithmeticSentence) (hphi : S ⊢ phi) :
    ∃ seed : ℕ, ∀ (V : Type*) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔],
      (nativeProofCheckGraph (canonicalAxiomGraph S)).val.Evalb
        ![1, ORingStructure.numeral seed, (⌜phi⌝ : V)] := by
  let d : S ⊢! phi := hphi.get
  refine ⟨(⌜d⌝ : ℕ), ?_⟩
  intro V _ _
  rw [nativeProofCheckGraph_correct (canonicalAxiomGraph_computational S)
    (canonicalAxiomGraph_theory S)]
  refine Or.inl ⟨rfl, ?_⟩
  rw [numeral_eq_natCast_app, coe_quote_proof_eq]
  exact proof_of_quote_proof d

theorem exists_standard_pointwise_seed (S : ArithmeticTheory) [S.Δ₁] [𝗣𝗔 ⪯ S]
    (M : 𝚺₁.Semisentence 1) (h k : ℕ) :
    ∃ seed : ℕ, ∀ (V : Type*) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔],
      (nativeProofCheckGraph (canonicalAxiomGraph S)).val.Evalb
        ![1, ORingStructure.numeral seed, (⌜pointwiseSchema S M h k⌝ : V)] :=
  exists_standard_seed_for S _ (WeakerThan.pbl (pointwiseSchema_provable S M h k))

theorem exists_standard_closure_seed (S : ArithmeticTheory) [S.Δ₁] [𝗣𝗔 ⪯ S]
    (M : 𝚺₁.Semisentence 1) (h k : ℕ) :
    ∃ seed : ℕ, ∀ (V : Type*) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔],
      (nativeProofCheckGraph (canonicalAxiomGraph S)).val.Evalb
        ![1, ORingStructure.numeral seed, (⌜closureSchema S M h k⌝ : V)] :=
  exists_standard_seed_for S _ (WeakerThan.pbl (closureSchema_provable S M h k))

section Internal

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]

private theorem accepted_iff_proof (S : ArithmeticTheory) [S.Δ₁] (p c : V) :
    (nativeProofCheckGraph (canonicalAxiomGraph S)).val.Evalb ![1, p, c] ↔ Proof S p c := by
  rw [nativeProofCheckGraph_correct (canonicalAxiomGraph_computational S)
    (canonicalAxiomGraph_theory S)]
  simp

theorem pointwiseGraph_preserves_acceptance (S : ArithmeticTheory) [S.Δ₁]
    (M : 𝚺₁.Semisentence 1) (h k : ℕ) {o seed a t m p e u d : V}
    (ho : (pointwiseGraph (pointwiseBodyCode S M h k)).val.Evalb
      ![o, seed, 0, a, t, m, p, e, u, d])
    (hs : (nativeProofCheckGraph (canonicalAxiomGraph S)).val.Evalb
      ![1, seed, (⌜pointwiseSchema S M h k⌝ : V)])
    (ha : (nativeProofCheckGraph (canonicalAxiomGraph S)).val.Evalb
      ![1, a, instanceValue (familyAcceptance S M h k).val ![e]])
    (ht : (nativeProofCheckGraph (canonicalAxiomGraph S)).val.Evalb ![1, t, (⌜totality M k⌝ : V)])
    (hm : (nativeProofCheckGraph (canonicalAxiomGraph S)).val.Evalb
      ![1, m, instanceValue M.val ![u]])
    (hp : (nativeProofCheckGraph (canonicalAxiomGraph S)).val.Evalb
      ![1, p, instanceValue (membershipFormula S h).val ![u, d]]) :
    (nativeProofCheckGraph (canonicalAxiomGraph S)).val.Evalb
      ![1, o, instanceValue (membershipFormula S k).val ![u, d]] := by
  apply (accepted_iff_proof S _ _).mpr
  rw [(pointwiseGraph_iff _ _ _ _ _ _ _ _ _ _ _).mp ho]
  exact proof_pointwiseValue S M h k ((accepted_iff_proof S _ _).mp hs)
    ((accepted_iff_proof S _ _).mp ha) ((accepted_iff_proof S _ _).mp ht)
    ((accepted_iff_proof S _ _).mp hm) ((accepted_iff_proof S _ _).mp hp)

theorem closureGraph_preserves_acceptance (S : ArithmeticTheory) [S.Δ₁]
    (M : 𝚺₁.Semisentence 1) (h k : ℕ) {o seed a t e d : V}
    (ho : (closureGraph (closureBodyCode S M h k)).val.Evalb ![o, seed, 0, a, t, e, d])
    (hs : (nativeProofCheckGraph (canonicalAxiomGraph S)).val.Evalb
      ![1, seed, (⌜closureSchema S M h k⌝ : V)])
    (ha : (nativeProofCheckGraph (canonicalAxiomGraph S)).val.Evalb
      ![1, a, instanceValue (familyAcceptance S M h k).val ![e]])
    (ht : (nativeProofCheckGraph (canonicalAxiomGraph S)).val.Evalb ![1, t, (⌜totality M k⌝ : V)]) :
    (nativeProofCheckGraph (canonicalAxiomGraph S)).val.Evalb
      ![1, o, instanceValue (transferClosure S M h k) ![d]] := by
  apply (accepted_iff_proof S _ _).mpr
  rw [(closureGraph_iff _ _ _ _ _ _ _ _).mp ho]
  exact proof_closureValue S M h k ((accepted_iff_proof S _ _).mp hs)
    ((accepted_iff_proof S _ _).mp ha) ((accepted_iff_proof S _ _).mp ht)

/-- Completeness supplies a proof of acceptance, not the original proof `e`. -/
theorem exists_acceptance_proof (S : ArithmeticTheory) [S.Δ₁] [𝗣𝗔⁻ ⪯ S]
    (M : 𝚺₁.Semisentence 1) (h k : ℕ) (e : V)
    (he : (nativeProofCheckGraph (canonicalAxiomGraph S)).val.Evalb
      ![1, e, (⌜familyEq M h k⌝ : V)]) :
    ∃ a : V, (nativeProofCheckGraph (canonicalAxiomGraph S)).val.Evalb
      ![1, a, instanceValue (familyAcceptance S M h k).val ![e]] :=
  exists_canonical_sigma_instance S (familyAcceptance S M h k) ![e]
    ((familyAcceptance_eval S M h k e).mpr he)

end Internal

/-- The stronger endpoint exposes both `a` and the exact constructor output. -/
theorem exists_pointwise_assembly (S : ArithmeticTheory) [S.Δ₁] [𝗣𝗔 ⪯ S]
    (M : 𝚺₁.Semisentence 1) (h k : ℕ) :
    ∃ seed : ℕ, ∀ (V : Type*) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
      (e t m p u d : V),
      (nativeProofCheckGraph (canonicalAxiomGraph S)).val.Evalb
        ![1, e, (⌜familyEq M h k⌝ : V)] →
      (nativeProofCheckGraph (canonicalAxiomGraph S)).val.Evalb ![1, t, (⌜totality M k⌝ : V)] →
      (nativeProofCheckGraph (canonicalAxiomGraph S)).val.Evalb ![1, m, instanceValue M.val ![u]] →
      (nativeProofCheckGraph (canonicalAxiomGraph S)).val.Evalb
        ![1, p, instanceValue (membershipFormula S h).val ![u, d]] →
      ∃ a o : V,
        (nativeProofCheckGraph (canonicalAxiomGraph S)).val.Evalb
          ![1, a, instanceValue (familyAcceptance S M h k).val ![e]] ∧
        (pointwiseGraph (pointwiseBodyCode S M h k)).val.Evalb
          ![o, ORingStructure.numeral seed, 0, a, t, m, p, e, u, d] ∧
        (nativeProofCheckGraph (canonicalAxiomGraph S)).val.Evalb
          ![1, o, instanceValue (membershipFormula S k).val ![u, d]] := by
  obtain ⟨seed, hs⟩ := exists_standard_pointwise_seed S M h k
  refine ⟨seed, ?_⟩
  intro V _ _ e t m p u d he ht hm hp
  have : 𝗣𝗔⁻ ⪯ S := WeakerThan.trans (inferInstance : 𝗣𝗔⁻ ⪯ 𝗣𝗔) inferInstance
  obtain ⟨a, ha⟩ := exists_acceptance_proof S M h k e he
  obtain ⟨o, ho⟩ := pointwiseGraph_total (pointwiseBodyCode S M h k)
    (ORingStructure.numeral seed : V) 0 a t m p e u d
  exact ⟨a, o, ha, ho, pointwiseGraph_preserves_acceptance S M h k ho (hs V) ha ht hm hp⟩

theorem exists_closure_assembly (S : ArithmeticTheory) [S.Δ₁] [𝗣𝗔 ⪯ S]
    (M : 𝚺₁.Semisentence 1) (h k : ℕ) :
    ∃ seed : ℕ, ∀ (V : Type*) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔] (e t d : V),
      (nativeProofCheckGraph (canonicalAxiomGraph S)).val.Evalb
        ![1, e, (⌜familyEq M h k⌝ : V)] →
      (nativeProofCheckGraph (canonicalAxiomGraph S)).val.Evalb ![1, t, (⌜totality M k⌝ : V)] →
      ∃ a o : V,
        (nativeProofCheckGraph (canonicalAxiomGraph S)).val.Evalb
          ![1, a, instanceValue (familyAcceptance S M h k).val ![e]] ∧
        (closureGraph (closureBodyCode S M h k)).val.Evalb
          ![o, ORingStructure.numeral seed, 0, a, t, e, d] ∧
        (nativeProofCheckGraph (canonicalAxiomGraph S)).val.Evalb
          ![1, o, instanceValue (transferClosure S M h k) ![d]] := by
  obtain ⟨seed, hs⟩ := exists_standard_closure_seed S M h k
  refine ⟨seed, ?_⟩
  intro V _ _ e t d he ht
  have : 𝗣𝗔⁻ ⪯ S := WeakerThan.trans (inferInstance : 𝗣𝗔⁻ ⪯ 𝗣𝗔) inferInstance
  obtain ⟨a, ha⟩ := exists_acceptance_proof S M h k e he
  obtain ⟨o, ho⟩ := closureGraph_total (closureBodyCode S M h k)
    (ORingStructure.numeral seed : V) 0 a t e d
  exact ⟨a, o, ha, ho, closureGraph_preserves_acceptance S M h k ho (hs V) ha ht⟩

section Consequences

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]

theorem exists_membership_proof (S : ArithmeticTheory) [S.Δ₁] [𝗣𝗔 ⪯ S]
    (M : 𝚺₁.Semisentence 1) (h k : ℕ) (e t m p u d : V)
    (he : (nativeProofCheckGraph (canonicalAxiomGraph S)).val.Evalb
      ![1, e, (⌜familyEq M h k⌝ : V)])
    (ht : (nativeProofCheckGraph (canonicalAxiomGraph S)).val.Evalb ![1, t, (⌜totality M k⌝ : V)])
    (hm : (nativeProofCheckGraph (canonicalAxiomGraph S)).val.Evalb
      ![1, m, instanceValue M.val ![u]])
    (hp : (nativeProofCheckGraph (canonicalAxiomGraph S)).val.Evalb
      ![1, p, instanceValue (membershipFormula S h).val ![u, d]]) :
    ∃ o : V, (nativeProofCheckGraph (canonicalAxiomGraph S)).val.Evalb
      ![1, o, instanceValue (membershipFormula S k).val ![u, d]] := by
  obtain ⟨_, hend⟩ := exists_pointwise_assembly S M h k
  obtain ⟨a, o, _, _, ho⟩ := hend V e t m p u d he ht hm hp
  exact ⟨o, ho⟩

theorem exists_transfer_closure_proof (S : ArithmeticTheory) [S.Δ₁] [𝗣𝗔 ⪯ S]
    (M : 𝚺₁.Semisentence 1) (h k : ℕ) (e t d : V)
    (he : (nativeProofCheckGraph (canonicalAxiomGraph S)).val.Evalb
      ![1, e, (⌜familyEq M h k⌝ : V)])
    (ht : (nativeProofCheckGraph (canonicalAxiomGraph S)).val.Evalb ![1, t, (⌜totality M k⌝ : V)]) :
    ∃ o : V, (nativeProofCheckGraph (canonicalAxiomGraph S)).val.Evalb
      ![1, o, instanceValue (transferClosure S M h k) ![d]] := by
  obtain ⟨_, hend⟩ := exists_closure_assembly S M h k
  obtain ⟨a, o, _, _, ho⟩ := hend V e t d he ht
  exact ⟨o, ho⟩

theorem exists_craig_membership_proof (T : ArithmeticTheory) [T.RE] [𝗣𝗔 ⪯ T]
    (M : 𝚺₁.Semisentence 1) (h k : ℕ) (e t m p u d : V)
    (he : (nativeProofCheckGraph (canonicalAxiomGraph T.craig)).val.Evalb
      ![1, e, (⌜familyEq M h k⌝ : V)])
    (ht : (nativeProofCheckGraph (canonicalAxiomGraph T.craig)).val.Evalb
      ![1, t, (⌜totality M k⌝ : V)])
    (hm : (nativeProofCheckGraph (canonicalAxiomGraph T.craig)).val.Evalb
      ![1, m, instanceValue M.val ![u]])
    (hp : (nativeProofCheckGraph (canonicalAxiomGraph T.craig)).val.Evalb
      ![1, p, instanceValue (membershipFormula T.craig h).val ![u, d]]) :
    ∃ o : V, (nativeProofCheckGraph (canonicalAxiomGraph T.craig)).val.Evalb
      ![1, o, instanceValue (membershipFormula T.craig k).val ![u, d]] := by
  have : 𝗣𝗔 ⪯ T.craig := WeakerThan.trans (inferInstance : 𝗣𝗔 ⪯ T)
    (inferInstance : T ⪯ T.craig)
  exact exists_membership_proof T.craig M h k e t m p u d he ht hm hp

theorem exists_craig_transfer_closure_proof (T : ArithmeticTheory) [T.RE] [𝗣𝗔 ⪯ T]
    (M : 𝚺₁.Semisentence 1) (h k : ℕ) (e t d : V)
    (he : (nativeProofCheckGraph (canonicalAxiomGraph T.craig)).val.Evalb
      ![1, e, (⌜familyEq M h k⌝ : V)])
    (ht : (nativeProofCheckGraph (canonicalAxiomGraph T.craig)).val.Evalb
      ![1, t, (⌜totality M k⌝ : V)]) :
    ∃ o : V, (nativeProofCheckGraph (canonicalAxiomGraph T.craig)).val.Evalb
      ![1, o, instanceValue (transferClosure T.craig M h k) ![d]] := by
  have : 𝗣𝗔 ⪯ T.craig := WeakerThan.trans (inferInstance : 𝗣𝗔 ⪯ T)
    (inferInstance : T ⪯ T.craig)
  exact exists_transfer_closure_proof T.craig M h k e t d he ht

end Consequences

theorem exists_membership_proof_nat (S : ArithmeticTheory) [S.Δ₁] [𝗣𝗔 ⪯ S]
    (M : 𝚺₁.Semisentence 1) (h k e t m p u d : ℕ)
    (he : (nativeProofCheckGraph (canonicalAxiomGraph S)).val.Evalb
      ![1, e, (⌜familyEq M h k⌝ : ℕ)])
    (ht : (nativeProofCheckGraph (canonicalAxiomGraph S)).val.Evalb ![1, t, (⌜totality M k⌝ : ℕ)])
    (hm : (nativeProofCheckGraph (canonicalAxiomGraph S)).val.Evalb
      ![1, m, Encodable.encode ((Rew.subst
        (fun i => (↑((![u] : Fin 1 → ℕ) i) : ArithmeticSemiterm Empty 0))) ▹ M.val)])
    (hp : (nativeProofCheckGraph (canonicalAxiomGraph S)).val.Evalb
      ![1, p, Encodable.encode ((Rew.subst
        (fun i => (↑((![u, d] : Fin 2 → ℕ) i) : ArithmeticSemiterm Empty 0))) ▹
        (membershipFormula S h).val)]) :
    ∃ o : ℕ, (nativeProofCheckGraph (canonicalAxiomGraph S)).val.Evalb
      ![1, o, Encodable.encode ((Rew.subst
        (fun i => (↑((![u, d] : Fin 2 → ℕ) i) : ArithmeticSemiterm Empty 0))) ▹
        (membershipFormula S k).val)] := by
  simpa only [instanceValue_nat] using exists_membership_proof S M h k e t m p u d he ht
    (by simpa only [instanceValue_nat] using hm)
    (by simpa only [instanceValue_nat] using hp)

theorem exists_transfer_closure_proof_nat (S : ArithmeticTheory) [S.Δ₁] [𝗣𝗔 ⪯ S]
    (M : 𝚺₁.Semisentence 1) (h k e t d : ℕ)
    (he : (nativeProofCheckGraph (canonicalAxiomGraph S)).val.Evalb
      ![1, e, (⌜familyEq M h k⌝ : ℕ)])
    (ht : (nativeProofCheckGraph (canonicalAxiomGraph S)).val.Evalb ![1, t, (⌜totality M k⌝ : ℕ)]) :
    ∃ o : ℕ, (nativeProofCheckGraph (canonicalAxiomGraph S)).val.Evalb
      ![1, o, Encodable.encode ((Rew.subst
        (fun i => (↑((![d] : Fin 1 → ℕ) i) : ArithmeticSemiterm Empty 0))) ▹
        transferClosure S M h k)] := by
  simpa only [instanceValue_nat] using exists_transfer_closure_proof S M h k e t d he ht

end FailureOfComposition.NativeMembershipAssembly
