/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import FailureOfComposition.NativeNumeralComparisonGraph
public import FailureOfComposition.NativeNumeralPreservation

/-!
# Same-context preservation of numeral comparisons

All eight seed derivations have the same coded context `Gamma`. The four
conditional results require, respectively, equality, disequality, strict
order, or reversed weak order of the numeral values. The signed results need
no comparison hypothesis. The theory need only be delta-one definable;
arithmetic inclusion is used later to obtain standard seeds.
-/

@[expose] public section

set_option autoImplicit false

open Encodable FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic

namespace FailureOfComposition.NativeNumeralComparison

open FFL.FirstOrder.Arithmetic.Bootstrapping
open FFL.FirstOrder.Arithmetic.Bootstrapping.Arithmetic
open FailureOfComposition.NativeNumeralArithmetic
open FailureOfComposition.NativeEqualityTransport

open FailureOfComposition.NativeContextSpecialization
open FailureOfComposition.NativeSubstitution
open FailureOfComposition.NativeFamilyExtraction

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]

structure SeedsIn (S : ArithmeticTheory) [S.Δ₁]
    (Γ r0 z1 refl as ltBridge nltBridge neForward neReverse : V) : Prop where
  r0_valid : DerivationOf S r0 (insert (⌜r0Sentence⌝ : V) Γ)
  z1_valid : DerivationOf S z1 (insert (⌜z1Sentence⌝ : V) Γ)
  refl_valid : DerivationOf S refl (insert (⌜reflSentence⌝ : V) Γ)
  as_valid : DerivationOf S as (insert (⌜asSentence⌝ : V) Γ)
  lt_valid : DerivationOf S ltBridge (insert (⌜ltBridgeSentence⌝ : V) Γ)
  nlt_valid : DerivationOf S nltBridge (insert (⌜nltBridgeSentence⌝ : V) Γ)
  forward_valid : DerivationOf S neForward (insert (⌜neForwardSentence⌝ : V) Γ)
  reverse_valid : DerivationOf S neReverse (insert (⌜neReverseSentence⌝ : V) Γ)

theorem lt_difference {n m : V} (h : n < m) : (m - (n + 1)) + n + 1 = m := by
  rw [add_assoc]
  exact sub_add_self_of_le (succ_le_iff_lt.mpr h)

theorem nlt_difference {n m : V} (h : m ≤ n) : (n - m) + m = n :=
  sub_add_self_of_le h

theorem ltBridge_literal {n m : V} (h : n < m) :
    instance4Value (ltBridgeBodyCode : V) n (m - (n + 1)) ((m - (n + 1)) + n) m =
      imp ℒₒᵣ (addEq (m - (n + 1)) n)
        (imp ℒₒᵣ (addEq ((m - (n + 1)) + n) 1) (ltTarget n m)) := by
  rw [ltBridge_instance]
  simp only [addEq, lt_difference h]

theorem nltBridge_literal {n m : V} (h : m ≤ n) :
    instance3Value (nltBridgeBodyCode : V) m (n - m) n =
      imp ℒₒᵣ (addEq (n - m) m) (nltTarget n m) := by
  rw [nltBridge_instance]
  simp only [addEq, nlt_difference h]

variable (S : ArithmeticTheory) [S.Δ₁]
    {r0 z1 refl as ltBridge nltBridge neForward neReverse Γ n m : V}

theorem derivationOf_eqValue (hs : SeedsIn S Γ r0 z1 refl as ltBridge nltBridge neForward
  neReverse) (h : n = m) :
    DerivationOf S (eqValue r0 z1 refl as ltBridge nltBridge neForward neReverse Γ n m) (insert
      (eqTarget n m) Γ) := by
  subst m
  have hrefl : (⌜reflSentence⌝ : V) = ^∀ (reflBodyCode : V) := by
    rw [reflSentence, all_quote, reflBodyCode, Sentence.quote_eq_encode]
  have hd : DerivationOf S
      (specializeCtxValue Γ (reflBodyCode : V) (Arithmetic.numeral n) refl)
      (insert (subst1Value (Arithmetic.numeral n) (reflBodyCode : V)) Γ) :=
    derivationOf_specializeNumeral S (u := n)
      (by simpa only [hrefl] using hs.refl_valid)
  have hinst : subst1Value (Arithmetic.numeral n) (reflBodyCode : V) = eqTarget n n := by
    simpa only [typedNumeral, eqTarget] using refl_instance (typedNumeral n)
  rw [hinst] at hd
  exact hd

theorem derivationOf_ltValue (hs : SeedsIn S Γ r0 z1 refl as ltBridge nltBridge neForward
  neReverse) (h : n < m) :
    DerivationOf S (ltValue r0 z1 refl as ltBridge nltBridge neForward neReverse Γ n m) (insert
      (ltTarget n m) Γ) := by
  have hd := derivationOf_specialize4 S
    (⌜ltBridgeMatrix⌝ : Bootstrapping.Semiformula V ℒₒᵣ 4)
    (x := n) (y := m - (n + 1)) (z := (m - (n + 1)) + n) (w := m)
    (by simpa only [ltBridgeSentence_literal] using hs.lt_valid)
  have he : DerivationOf S
      (specialize4Value (ltBridgeBodyCode : V) Γ ltBridge n (m - (n + 1))
        ((m - (n + 1)) + n) m)
      (insert (imp ℒₒᵣ (addEq (m - (n + 1)) n)
        (imp ℒₒᵣ (addEq ((m - (n + 1)) + n) 1) (ltTarget n m))) Γ) := by
    rw [← ltBridge_literal h, ltBridgeBody_cast, Sentence.quote_eq ltBridgeMatrix]
    exact hd
  have ha := derivationOf_addValue S (n := m - (n + 1)) (m := n)
    hs.r0_valid hs.z1_valid hs.refl_valid hs.as_valid
  have hb := derivationOf_addValue S (n := (m - (n + 1)) + n) (m := 1)
    hs.r0_valid hs.z1_valid hs.refl_valid hs.as_valid
  have ho := derivationOf_applyCtxValue S (derivationOf_applyCtxValue S he ha) hb
  simpa only [ltValue, ltBridge_literal h, consequentValue_imp] using ho

theorem derivationOf_nltValue (hs : SeedsIn S Γ r0 z1 refl as ltBridge nltBridge neForward
  neReverse) (h : m ≤ n) :
    DerivationOf S (nltValue r0 z1 refl as ltBridge nltBridge neForward neReverse Γ n m) (insert
      (nltTarget n m) Γ) := by
  have hd := derivationOf_specialize3 S
    (⌜nltBridgeMatrix⌝ : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (x := m) (y := n - m) (z := n)
    (by simpa only [nltBridgeSentence_literal] using hs.nlt_valid)
  have he : DerivationOf S
      (specialize3Value (nltBridgeBodyCode : V) Γ nltBridge m (n - m) n)
      (insert (imp ℒₒᵣ (addEq (n - m) m) (nltTarget n m)) Γ) := by
    rw [← nltBridge_literal h, nltBridgeBody_cast, Sentence.quote_eq nltBridgeMatrix]
    exact hd
  have ha := derivationOf_addValue S (n := n - m) (m := m)
    hs.r0_valid hs.z1_valid hs.refl_valid hs.as_valid
  have ho := derivationOf_applyCtxValue S he ha
  simpa only [nltValue, nltBridge_literal h] using ho

theorem derivationOf_neValue (hs : SeedsIn S Γ r0 z1 refl as ltBridge nltBridge neForward
  neReverse) (h : n ≠ m) :
    DerivationOf S (neValue r0 z1 refl as ltBridge nltBridge neForward neReverse Γ n m) (insert
      (neTarget n m) Γ) := by
  by_cases hlt : n < m
  · have hd := derivationOf_specialize2 S
      (⌜neForwardMatrix⌝ : Bootstrapping.Semiformula V ℒₒᵣ 2) (x := n) (y := m)
      (by simpa only [neForwardSentence_literal] using hs.forward_valid)
    have he : DerivationOf S (specialize2Value (neForwardBodyCode : V) Γ neForward n m)
        (insert (imp ℒₒᵣ (ltTarget n m) (neTarget n m)) Γ) := by
      rw [← neForward_instance, neForwardBody_cast, Sentence.quote_eq neForwardMatrix]
      exact hd
    have ho := derivationOf_applyCtxValue S he (derivationOf_ltValue S hs hlt)
    simpa only [neValue, ite_eq_left hlt, neForward_instance] using ho
  · have hrev : m < n := lt_of_le_of_ne (not_lt.mp hlt) (Ne.symm h)
    have hd := derivationOf_specialize2 S
      (⌜neReverseMatrix⌝ : Bootstrapping.Semiformula V ℒₒᵣ 2) (x := n) (y := m)
      (by simpa only [neReverseSentence_literal] using hs.reverse_valid)
    have he : DerivationOf S (specialize2Value (neReverseBodyCode : V) Γ neReverse n m)
        (insert (imp ℒₒᵣ (ltTarget m n) (neTarget n m)) Γ) := by
      rw [← neReverse_instance, neReverseBody_cast, Sentence.quote_eq neReverseMatrix]
      exact hd
    have ho := derivationOf_applyCtxValue S he (derivationOf_ltValue S hs hrev)
    simpa only [neValue, ite_eq_right hlt, neReverse_instance] using ho

theorem derivationOf_signedEqValue (hs : SeedsIn S Γ r0 z1 refl as ltBridge nltBridge neForward
  neReverse) :
    DerivationOf S (signedEqValue r0 z1 refl as ltBridge nltBridge neForward neReverse Γ n m)
      (insert (signedEqTarget n m) Γ) := by
  by_cases h : n = m
  · simpa only [signedEqValue, signedEqTarget, ite_eq_left h] using derivationOf_eqValue S hs h
  · simpa only [signedEqValue, signedEqTarget, ite_eq_right h] using derivationOf_neValue S hs h

theorem derivationOf_signedLtValue (hs : SeedsIn S Γ r0 z1 refl as ltBridge nltBridge neForward
  neReverse) :
    DerivationOf S (signedLtValue r0 z1 refl as ltBridge nltBridge neForward neReverse Γ n m)
      (insert (signedLtTarget n m) Γ) := by
  by_cases h : n < m
  · simpa only [signedLtValue, signedLtTarget, ite_eq_left h] using derivationOf_ltValue S hs h
  · simpa only [signedLtValue, signedLtTarget, ite_eq_right h] using
      derivationOf_nltValue S hs (not_lt.mp h)

theorem eqGraph_preserves_derivationOf {o : V}
    (ho : eqGraph.val.Evalb ![o, r0, z1, refl, as, ltBridge, nltBridge, neForward, neReverse, Γ,
      n, m])
    (hs : SeedsIn S Γ r0 z1 refl as ltBridge nltBridge neForward neReverse) (h : n = m) :
    DerivationOf S o (insert (eqTarget n m) Γ) := by
  rw [(eqGraph_iff _ _ _ _ _ _ _ _ _ _ _ _).mp ho]
  exact derivationOf_eqValue S hs h

theorem ltGraph_preserves_derivationOf {o : V}
    (ho : ltGraph.val.Evalb ![o, r0, z1, refl, as, ltBridge, nltBridge, neForward, neReverse, Γ,
      n, m])
    (hs : SeedsIn S Γ r0 z1 refl as ltBridge nltBridge neForward neReverse) (h : n < m) :
    DerivationOf S o (insert (ltTarget n m) Γ) := by
  rw [(ltGraph_iff _ _ _ _ _ _ _ _ _ _ _ _).mp ho]
  exact derivationOf_ltValue S hs h

theorem nltGraph_preserves_derivationOf {o : V}
    (ho : nltGraph.val.Evalb ![o, r0, z1, refl, as, ltBridge, nltBridge, neForward, neReverse,
      Γ, n, m])
    (hs : SeedsIn S Γ r0 z1 refl as ltBridge nltBridge neForward neReverse) (h : m ≤ n) :
    DerivationOf S o (insert (nltTarget n m) Γ) := by
  rw [(nltGraph_iff _ _ _ _ _ _ _ _ _ _ _ _).mp ho]
  exact derivationOf_nltValue S hs h

theorem neGraph_preserves_derivationOf {o : V}
    (ho : neGraph.val.Evalb ![o, r0, z1, refl, as, ltBridge, nltBridge, neForward, neReverse, Γ,
      n, m])
    (hs : SeedsIn S Γ r0 z1 refl as ltBridge nltBridge neForward neReverse) (h : n ≠ m) :
    DerivationOf S o (insert (neTarget n m) Γ) := by
  rw [(neGraph_iff _ _ _ _ _ _ _ _ _ _ _ _).mp ho]
  exact derivationOf_neValue S hs h

theorem signedEqGraph_preserves_derivationOf {o : V}
    (ho : signedEqGraph.val.Evalb ![o, r0, z1, refl, as, ltBridge, nltBridge, neForward,
      neReverse, Γ, n, m])
    (hs : SeedsIn S Γ r0 z1 refl as ltBridge nltBridge neForward neReverse) :
    DerivationOf S o (insert (signedEqTarget n m) Γ) := by
  rw [(signedEqGraph_iff _ _ _ _ _ _ _ _ _ _ _ _).mp ho]
  exact derivationOf_signedEqValue S hs

theorem signedLtGraph_preserves_derivationOf {o : V}
    (ho : signedLtGraph.val.Evalb ![o, r0, z1, refl, as, ltBridge, nltBridge, neForward,
      neReverse, Γ, n, m])
    (hs : SeedsIn S Γ r0 z1 refl as ltBridge nltBridge neForward neReverse) :
    DerivationOf S o (insert (signedLtTarget n m) Γ) := by
  rw [(signedLtGraph_iff _ _ _ _ _ _ _ _ _ _ _ _).mp ho]
  exact derivationOf_signedLtValue S hs

theorem derivationOf_lt_zero_one (hs : SeedsIn S Γ r0 z1 refl as ltBridge nltBridge neForward
  neReverse) :
    DerivationOf S (ltValue r0 z1 refl as ltBridge nltBridge neForward neReverse Γ 0 1)
      (insert (ltTarget 0 1) Γ) :=
  derivationOf_ltValue S hs (by simp)

theorem derivationOf_nlt_self (hs : SeedsIn S Γ r0 z1 refl as ltBridge nltBridge neForward
  neReverse) :
    DerivationOf S (nltValue r0 z1 refl as ltBridge nltBridge neForward neReverse Γ n n)
      (insert (nltTarget n n) Γ) :=
  derivationOf_nltValue S hs (by rfl)

theorem derivationOf_nlt_zero_zero (hs : SeedsIn S Γ r0 z1 refl as ltBridge nltBridge neForward
  neReverse) :
    DerivationOf S (nltValue r0 z1 refl as ltBridge nltBridge neForward neReverse Γ 0 0)
      (insert (nltTarget 0 0) Γ) :=
  derivationOf_nltValue S hs (by rfl)

theorem signed_comparisons_singleton {c : V}
    (hs : SeedsIn S (insert c 0) r0 z1 refl as ltBridge nltBridge neForward neReverse) :
    DerivationOf S
      (signedEqValue r0 z1 refl as ltBridge nltBridge neForward neReverse (insert c 0) n m)
      (insert (signedEqTarget n m) (insert c 0)) ∧
    DerivationOf S
      (signedLtValue r0 z1 refl as ltBridge nltBridge neForward neReverse (insert c 0) n m)
      (insert (signedLtTarget n m) (insert c 0)) :=
  ⟨derivationOf_signedEqValue S hs, derivationOf_signedLtValue S hs⟩

end FailureOfComposition.NativeNumeralComparison
