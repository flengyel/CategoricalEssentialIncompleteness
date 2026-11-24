/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.ClassicalDiagonalArithmetic
public import CategoricalEssentialIncompleteness.OracleMissingLift
public import CategoricalEssentialIncompleteness.V46Comparison

/-! # Inverse images of the two summands in the oracle example of Appendix C -/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.RestrictionCategory
open CategoryTheory.CoprodStruct CategoryTheory.HasCoproducts
open CategoryTheory.PCategoryStruct (nearProd diag)

namespace CategoricalEssentialIncompleteness.LocalConnectedness

/-- Identify the restriction structure induced by the partial products before
applying the diagonal comparison to a proposed lift. -/
theorem no_lift_of_compatible_restriction {R : Type*} [Category R]
    [PCategoryStruct R] [PCategory R] [native : RestrictionCategory R]
    [Limits.HasZeroMorphisms R] [RestrictionZero R] [CoprodStruct R]
    [CategoryTheory.HasCoproducts R] [RestrictionCoproducts R] [Ranges R]
    (he : PCategory.inducedRestriction = native) (F : RangeFunctor R PartialFunctions.Pfn)
    {U : R} (τ : nearProd U U ⟶ U) (hτ : RecursionCategory.IsTuringMorphism τ)
    (b : U ≅ coprod U U) (hU : F.toFunctor.map (𝟙 U) ≠ 0)
    (P N : Idem (F.toFunctor.obj U)) (hPN : Complementary P N)
    (h₀ : F.mapIdem (Idem.pull (diag U ≫ τ ≫ b.hom) (summand0 U U)) ≤ P)
    (h₁ : F.mapIdem (Idem.pull (diag U ≫ τ ≫ b.hom) (summand1 U U)) ≤ N)
    (s : F.toFunctor.obj U ⟶ coprod (F.toFunctor.obj U) (F.toFunctor.obj U))
    (hs₀ : Idem.pull s (summand0 (F.toFunctor.obj U) (F.toFunctor.obj U)) = N)
    (hs₁ : Idem.pull s (summand1 (F.toFunctor.obj U) (F.toFunctor.obj U)) = P) :
    ¬ ∃ ℓ : U ⟶ coprod U U, F.toFunctor.map ℓ = s ≫ (F.comparison U U).hom := by
  cases he
  rintro ⟨ℓ, hℓ⟩
  exact no_lifted_complementary_separator F τ hτ b hU P N hPN h₀ h₁
    ⟨s, ℓ, hs₀, hs₁, hℓ⟩

namespace OracleComputation

/-- The simulation in Appendix C ignores its input, so the second coordinate
of the paired index does not affect its diagonal value. -/
theorem ordinaryDiagonal_simulation (n a : ℕ) :
    ordinaryDiagonal (Nat.pair (Encodable.encode (simulationCode n)) a) =
      (ordinaryEval n n).map (fun _ => 0) := by
  rw [← ordinaryDiagonal_reduction]
  simp only [K_reduction_A, ordinaryDiagonal, Nat.unpair_pair, ordinaryEval,
    Denumerable.ofNat_encode, simulationCode, Nat.Partrec.Code.eval, Nat.Partrec.Code.eval_const]

/-- The halting problem reduces to the even-output separator at each choice of
the second coordinate. -/
theorem K_iff_simulation_mem_A (n a : ℕ) :
    n ∈ K ↔ Nat.pair (Encodable.encode (simulationCode n)) a ∈ A := by
  rw [K_iff_reduction_A]
  change (∃ z, z ∈ ordinaryDiagonal (K_reduction_A n) ∧ z % 2 = 0) ↔
    ∃ z, z ∈ ordinaryDiagonal (Nat.pair (Encodable.encode (simulationCode n)) a) ∧ z % 2 = 0
  rw [ordinaryDiagonal_reduction, ordinaryDiagonal_simulation]

namespace Restricted

attribute [local instance 2000] nativeRestriction

/-- In Appendix C, every partial morphism with left inverse image the complement of
`A` and right inverse image `A` has no source lift through the coproduct comparison. -/
theorem no_lift_of_summand_inverse_images
    (s : PartialFun.of ℕ ⟶ coprod (PartialFun.of ℕ) (PartialFun.of ℕ))
    (h₀ : Idem.pull s (summand0 (PartialFun.of ℕ) (PartialFun.of ℕ)) =
      (rangeFunctor K).mapIdem separatorComplement)
    (h₁ : Idem.pull s (summand1 (PartialFun.of ℕ) (PartialFun.of ℕ)) =
      (rangeFunctor K).mapIdem separator) :
    ¬ ∃ ℓ : N K ⟶ coprod (N K) (N K),
      (inclusion K).map ℓ = s ≫ ((rangeFunctor K).comparison (N K) (N K)).hom :=
  no_lift_of_compatible_restriction (inducedRestriction_eq K) (rangeFunctor K)
    (tau K) (tau_isTuring K) (parityIso K) (inclusion_nonzero K) _ _
    ((rangeFunctor K).map_complementary separator_complementary)
    ((rangeFunctor K).map_mono pair0_le_separator)
    ((rangeFunctor K).map_mono pair1_le_separatorComplement) s h₀ h₁

/-- The two inverse images depend only on the summand of an output. Its numerical
value in that summand may be arbitrary. -/
theorem no_lift_of_output_summands (s : ℕ →. (ℕ ⊕ ℕ))
    (h₀ : ∀ n, (∃ y : ℕ, Sum.inl y ∈ s n) ↔ n ∉ A)
    (h₁ : ∀ n, (∃ y : ℕ, Sum.inr y ∈ s n) ↔ n ∈ A) :
    ¬ ∃ ℓ : N K ⟶ coprod (N K) (N K), (inclusion K).map ℓ = s := by
  let f : PartialFun.of ℕ ⟶ coprod (PartialFun.of ℕ) (PartialFun.of ℕ) := s
  have hleft : Idem.pull f (summand0 (PartialFun.of ℕ) (PartialFun.of ℕ)) =
      (rangeFunctor K).mapIdem separatorComplement := by
    apply PartialFunctions.support_injective
    change PartialFunctions.support (X := PartialFun.of ℕ) _ =
      PartialFunctions.support (PartialFunctions.setIdem (X := PartialFun.of ℕ) (Aᶜ : Set ℕ))
    rw [PartialFunctions.support_pull f _,
      PartialFunctions.support_setIdem (X := PartialFun.of ℕ) (Aᶜ : Set ℕ)]
    ext n
    change (∃ y : ℕ ⊕ ℕ, y ∈ s n ∧ y ∈ PartialFunctions.support
      (summand0 (PartialFun.of ℕ) (PartialFun.of ℕ))) ↔ n ∉ A
    simp only [ClassicalPrograms.mem_support_summand0]
    constructor
    · rintro ⟨_, hy, z, rfl⟩
      exact (h₀ n).mp ⟨z, hy⟩
    · intro hn
      obtain ⟨z, hz⟩ := (h₀ n).mpr hn
      exact ⟨_, hz, z, rfl⟩
  have hright : Idem.pull f (summand1 (PartialFun.of ℕ) (PartialFun.of ℕ)) =
      (rangeFunctor K).mapIdem separator := by
    apply PartialFunctions.support_injective
    change PartialFunctions.support (X := PartialFun.of ℕ) _ =
      PartialFunctions.support (PartialFunctions.setIdem (X := PartialFun.of ℕ) A)
    rw [PartialFunctions.support_pull f _,
      PartialFunctions.support_setIdem (X := PartialFun.of ℕ) A]
    ext n
    change (∃ y : ℕ ⊕ ℕ, y ∈ s n ∧ y ∈ PartialFunctions.support
      (summand1 (PartialFun.of ℕ) (PartialFun.of ℕ))) ↔ n ∈ A
    simp only [ClassicalPrograms.mem_support_summand1]
    constructor
    · rintro ⟨_, hy, z, rfl⟩
      exact (h₁ n).mp ⟨z, hy⟩
    · intro hn
      obtain ⟨z, hz⟩ := (h₁ n).mpr hn
      exact ⟨_, hz, z, rfl⟩
  rintro ⟨ℓ, hℓ⟩
  apply no_lift_of_summand_inverse_images f hleft hright
  refine ⟨ℓ, ?_⟩
  rw [rangeFunctor_comparison_hom]
  exact hℓ.trans (Category.comp_id f).symm

/-- The two summand inverse images cover the domain. An ordinary recursive
function with these inverse images would decide the separator by its output tag. -/
theorem total_and_noncomputable_of_output_summands (s : ℕ →. (ℕ ⊕ ℕ))
    (h₀ : ∀ n, (∃ y : ℕ, Sum.inl y ∈ s n) ↔ n ∉ A)
    (h₁ : ∀ n, (∃ y : ℕ, Sum.inr y ∈ s n) ↔ n ∈ A) :
    (∀ n, (s n).Dom) ∧ ¬ ∃ f : ℕ → ℕ ⊕ ℕ, Computable f ∧ s = fun n => Part.some (f n) := by
  constructor
  · intro n
    by_cases hn : n ∈ A
    · obtain ⟨y, hy⟩ := (h₁ n).mpr hn
      exact hy.1
    · obtain ⟨y, hy⟩ := (h₀ n).mpr hn
      exact hy.1
  · rintro ⟨f, hf, rfl⟩
    apply A_not_recursive
    have ht : Computable (fun n => (f n).isRight) := by
      apply (Computable.sumCasesOn hf (Computable.const false).to₂ (Computable.const true).to₂).of_eq
      intro n
      cases f n <;> rfl
    have hd : ComputablePred (fun n => (f n).isRight = true) := ⟨inferInstance, by simpa using ht⟩
    apply hd.of_eq
    intro n
    rw [← h₁ n]
    cases he : f n <;> simp [he]

/-- A preimage of the target endomorphism indexed in the comparison with
Lengyel's Theorem 4.1 would give a lift of the section by postcomposition. -/
theorem missingSection_endomorphism_has_no_lift :
    ¬ ∃ u : N K ⟶ N K, (inclusion K).map u =
      missingSection ≫ ((inclusion K).mapIso (parityIso K)).inv := by
  rintro ⟨u, hu⟩
  apply missingSection_has_no_lift
  refine ⟨u ≫ (parityIso K).hom, ?_⟩
  rw [Functor.map_comp, hu]
  let b := (inclusion K).mapIso (parityIso K)
  change (missingSection ≫ b.inv) ≫ b.hom = missingSection
  rw [Category.assoc, b.inv_hom_id, Category.comp_id]

end Restricted
end OracleComputation
end CategoricalEssentialIncompleteness.LocalConnectedness
