/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46OracleMachineDomains
public import CategoricalEssentialIncompleteness.V46OracleSeparatorLift

/-! # The Turing morphism with a transition-machine domain index -/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.RestrictionCategory CategoryTheory.CoprodStruct
open Encodable Denumerable
namespace CategoricalEssentialIncompleteness.LocalConnectedness.OracleComputation

/-- For each coded parameter the section uses the same domain-machine index. -/
theorem fixed_machine_index {α : Type} [Primcodable α] (S : Set ℕ) {p : α × ℕ → Prop}
    (hp : FiniteOracleRE S p) :
    ∃ d, ∀ z x, machineDomain S d (Nat.pair (encode z) x) ↔ p (z,x) := by
  obtain ⟨Q,hQ,_,hp⟩ := hp
  obtain ⟨c,hc⟩ := predicate_code hQ
  obtain ⟨tr, _, ht⟩ := exists_machine_compiler
  refine ⟨tr (encode c), fun z x => (ht S (encode c) _).trans ?_⟩
  change (∃ n, ((ofNat Nat.Partrec.Code (encode c)).eval (encode ((z,x),oraclePrefix S n))).Dom) ↔ _
  simp only [ofNat_encode, hc, ← hp]

namespace Restricted
attribute [instance 2000] nativeRestriction
variable (S : Set ℕ)

/-- At the literal input pair `(e,a)`, the first index supplies the ordinary value
and the second queries the oracle transition machine with index `a`. -/
def machineTau : product (N S) (N S) ⟶ N S := by
  let D (p : ℕ × ℕ) := machineDomain S p.1.unpair.2 p.2
  let f₀ (p : ℕ × ℕ) := ordinaryEval p.1.unpair.1 p.2
  have hD : FiniteOracleRE S D := by
    obtain ⟨tr, htr, ht⟩ := exists_prefix_compiler
    have hd : Computable (fun p : ℕ × ℕ => (tr p.1.unpair.2, p.2)) :=
      (htr.comp (Computable.snd.comp (Computable.unpair.comp Computable.fst))).pair Computable.snd
    exact (FiniteOracleRE.comp hd (oracleDomain_uniform S)).of_eq (fun p => ht S _ _)
  have hf : Partrec f₀ := ordinaryEval_partrec.comp
    (Computable.fst.comp (Computable.unpair.comp Computable.fst)) Computable.snd
  refine ⟨fun p => Part.assert (D p) (fun _ => f₀ p), ?_, ⟨f₀, hf, ?_⟩⟩
  · exact (hD.and (FiniteOracleRE.of_re hf.dom_re)).of_eq (fun p => by simp [Part.assert])
  · exact fun p y hy => (Part.mem_assert_iff.mp hy).choose_spec

theorem mem_machineTau (q x y : ℕ) : y ∈ (machineTau S).val (q,x) ↔
    machineDomain S q.unpair.2 x ∧ y ∈ ordinaryEval q.unpair.1 x := by
  simp only [machineTau, Part.mem_assert_iff, exists_prop]

/-- The ordinary parameter pairs the value index with the specialized transition machine. -/
theorem parameter_indices (Y : Restricted S) (v : product Y (N S) ⟶ N S) :
    ∃ (t : carrier S Y → ℕ) (d : ℕ), Computable t ∧
      (∀ z x, machineDomain S d (Nat.pair (encode z) x) ↔ (v.val (z,x)).Dom) ∧
      ∀ z x y, y ∈ (machineTau S).val (Nat.pair (t z) (sectionIndex d (encode z)),x) ↔
        y ∈ v.val (z,x) := by
  obtain ⟨f₀, hf, he⟩ := v.extension
  obtain ⟨t, ht, hv⟩ := ordinary_program_specialization (show Partrec (fun p : carrier S Y × ℕ => f₀ p) from hf)
  obtain ⟨d, hd⟩ := fixed_machine_index S (show FiniteOracleRE S (fun p : carrier S Y × ℕ => (v.val p).Dom) from v.domain)
  refine ⟨t,d,ht,hd,?_⟩
  intro z x y
  rw [mem_machineTau, Nat.unpair_pair, machine_section, hd, hv]
  exact (he.mem_iff (z,x) y).symm

theorem machineTau_isTuring : RecursionCategory.IsTuringMorphism (machineTau S) := by
  intro Y v
  obtain ⟨t, d, ht, _, h⟩ := parameter_indices S Y v
  let r : Y ⟶ N S := totalFromFunction (fun z => Nat.pair (t z) (sectionIndex d (encode z)))
    (Primrec₂.natPair.to_comp.comp ht (sectionIndex_computable.comp (Computable.const d) Computable.encode))
  refine ⟨r, ?_, ?_⟩
  · change PCategoryStruct.rst r = 𝟙 _
    rw [induced_restriction]
    exact totalFromFunction_total _ _
  · change productMap r (𝟙 (N S)) ≫ machineTau S = v
    apply hom_ext_mem
    rintro ⟨z,x⟩ y
    exact (show _ ↔ _ from by
      simpa only [comp_val,productMap_val,id_val,r,totalFromFunction,ofPartrec,
        Part.bind_some,Part.map_some] using h z x y)

def machinePair0 : Idem (N S) :=
  Idem.pull (diagonal (N S) ≫ machineTau S ≫ (parityIso S).hom) (summand0 (N S) (N S))
def machinePair1 : Idem (N S) :=
  Idem.pull (diagonal (N S) ≫ machineTau S ≫ (parityIso S).hom) (summand1 (N S) (N S))

theorem support_machinePair0 (q : ℕ) : q ∈ support (machinePair0 S) ↔
    machineDomain S (Nat.unpair q).2 q ∧
      ∃ z,z ∈ ordinaryEval (Nat.unpair q).1 q ∧ z%2=0 := by
  rw [machinePair0,support_pull]
  change (∃ s,s ∈ (diagonal (N S) ≫ machineTau S ≫ (parityIso S).hom).val q ∧
    s ∈ support (summand0 (N S) (N S))) ↔ _
  simp only [comp_val,diagonal_val,parityIso_val,Part.bind_some,
    Part.mem_bind_iff,Part.mem_some_iff,support_summand0]
  change (∃ s,(∃ z : ℕ,z ∈ (machineTau S).val (q,q) ∧
    s=(if z%2=0 then Sum.inl (z/2) else Sum.inr (z/2))) ∧ ∃ x,s=Sum.inl x) ↔ _
  simp only [mem_machineTau]
  constructor
  · rintro ⟨s,⟨z,⟨hd,hz⟩,rfl⟩,x,hx⟩
    refine ⟨hd,z,hz,?_⟩
    split_ifs at hx with he
    omega
  · rintro ⟨hd,z,hz,he⟩
    exact ⟨Sum.inl (z/2),⟨z,⟨hd,hz⟩,by simp [he]⟩,z/2,rfl⟩

theorem support_machinePair1 (q : ℕ) : q ∈ support (machinePair1 S) ↔
    machineDomain S (Nat.unpair q).2 q ∧
      ∃ z,z ∈ ordinaryEval (Nat.unpair q).1 q ∧ z%2=1 := by
  rw [machinePair1,support_pull]
  change (∃ s,s ∈ (diagonal (N S) ≫ machineTau S ≫ (parityIso S).hom).val q ∧
    s ∈ support (summand1 (N S) (N S))) ↔ _
  simp only [comp_val,diagonal_val,parityIso_val,Part.bind_some,
    Part.mem_bind_iff,Part.mem_some_iff,support_summand1]
  change (∃ s,(∃ z : ℕ,z ∈ (machineTau S).val (q,q) ∧
    s=(if z%2=0 then Sum.inl (z/2) else Sum.inr (z/2))) ∧ ∃ x,s=Sum.inr x) ↔ _
  simp only [mem_machineTau]
  constructor
  · rintro ⟨s,⟨z,⟨hd,hz⟩,rfl⟩,x,hx⟩
    refine ⟨hd,z,hz,?_⟩
    split_ifs at hx with he
    omega
  · rintro ⟨hd,z,hz,he⟩
    have hn : z%2≠0 := by omega
    exact ⟨Sum.inr (z/2),⟨z,⟨hd,hz⟩,by simp [hn]⟩,z/2,rfl⟩


theorem machine_separator_bounds :
    machinePair0 K ≤ separator ∧ machinePair1 K ≤ separatorComplement := by
  constructor
  · apply (support_le_iff _ _).mpr
    intro q hq
    rw [separator,support_setIdem]
    exact ((support_machinePair0 K q).mp hq).2
  · apply (support_le_iff _ _).mpr
    intro q hq
    rw [separatorComplement,support_setIdem]
    obtain ⟨_, z,hz,he⟩ := (support_machinePair1 K q).mp hq
    rintro ⟨w,hw,he'⟩
    have eqn : z = w := Part.mem_unique hz hw
    omega

theorem machine_pair_separated : ¬ Inseparable (machinePair0 K) (machinePair1 K) := by
  intro hi
  exact hi.no_separator ⟨separator, separatorComplement, separator_complementary,
    machine_separator_bounds.1, machine_separator_bounds.2⟩

/-- The comparison theorem excludes every lift with the switched summand inverse images
for the diagonal formed using the literal transition-machine evaluator. -/
theorem machine_no_lift (s : PartialFun.of ℕ ⟶ coprod (PartialFun.of ℕ) (PartialFun.of ℕ))
    (h₀ : Idem.pull s (summand0 (PartialFun.of ℕ) (PartialFun.of ℕ)) = (rangeFunctor K).mapIdem separatorComplement)
    (h₁ : Idem.pull s (summand1 (PartialFun.of ℕ) (PartialFun.of ℕ)) = (rangeFunctor K).mapIdem separator) :
    ¬ ∃ ℓ : N K ⟶ coprod (N K) (N K),
      (inclusion K).map ℓ = s ≫ ((rangeFunctor K).comparison (N K) (N K)).hom :=
  no_lift_of_compatible_restriction (inducedRestriction_eq K) (rangeFunctor K)
    (machineTau K) (machineTau_isTuring K) (parityIso K) (inclusion_nonzero K) _ _
    ((rangeFunctor K).map_complementary separator_complementary)
    ((rangeFunctor K).map_mono machine_separator_bounds.1)
    ((rangeFunctor K).map_mono machine_separator_bounds.2) s h₀ h₁

end Restricted
end CategoricalEssentialIncompleteness.LocalConnectedness.OracleComputation
