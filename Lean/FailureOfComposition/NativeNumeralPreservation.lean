/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import FailureOfComposition.NativeNumeralMultiplicationGraph
import FailureOfComposition.NativeNumeralInstances

/-!
# Context-preserving arithmetic derivations at internal numerals

The seed derivations share a coded context. Their validity supplies the
context's validity; no arithmetic inclusion, consistency, or soundness
assumption is added to these conditional theorems. Definable induction proves
correctness of the actual recurrence output at every internal numeral value.
In the multiplication step, the second premise is the output of addition's
already-proved recurrence.
-/

set_option autoImplicit false

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic

namespace FailureOfComposition.NativeNumeralArithmetic

open FFL.FirstOrder.Arithmetic.Bootstrapping
open FFL.FirstOrder.Arithmetic.Bootstrapping.Arithmetic
open FailureOfComposition.NativeContextSpecialization
open FailureOfComposition.NativeSubstitution
open FailureOfComposition.NativeFamilyExtraction

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]

private instance addValue_fixed_definable (r0 z1 refl as Γ n : V) :
    𝚺₁-Function₁[V] (addValue r0 z1 refl as Γ n) := by
  refine ⟨⟨(.mkSigma “o m. !(addGraph.rew Rew.emb).val o &r0 &z1 &refl &as &Γ &n m” :
    𝚺₁.Semiformula V 2), ?_⟩⟩
  intro v
  simp

private instance mulValue_fixed_definable (r0 z1 refl as m0 m1 ms Γ n : V) :
    𝚺₁-Function₁[V] (mulValue r0 z1 refl as m0 m1 ms Γ n) := by
  refine ⟨⟨(.mkSigma “o m.
    !(mulGraph.rew Rew.emb).val o &r0 &z1 &refl &as &m0 &m1 &ms &Γ &n m” :
      𝚺₁.Semiformula V 2), ?_⟩⟩
  intro v
  simp

private theorem seed_all_literal (phi : ArithmeticSemisentence 1) :
    (⌜∀¹ phi⌝ : V) = ^∀ (Encodable.encode phi : V) := by
  rw [all_quote, Sentence.quote_eq_encode]

private theorem derivationOf_specializeTerm (S : ArithmeticTheory) [S.Δ₁]
    {Γ body d t : V} (ht : IsSemiterm ℒₒᵣ 0 t)
    (hd : DerivationOf S d (insert (^∀ body) Γ)) :
    DerivationOf S (specializeCtxValue Γ body t d) (insert (subst1Value t body) Γ) := by
  have hb : IsSemiformula ℒₒᵣ 1 body := by
    simpa using (IsFormulaSet.insert_iff.mp hd.isFormulaSet).1
  rw [subst1Value_eq_substs1 ht hb]
  exact derivationOf_specializeCtxValue S ht hd

theorem derivationOf_addOneValue (S : ArithmeticTheory) [S.Δ₁]
    {Γ z1 refl n : V}
    (hz : DerivationOf S z1 (insert (⌜z1Sentence⌝ : V) Γ))
    (hr : DerivationOf S refl (insert (⌜reflSentence⌝ : V) Γ)) :
    DerivationOf S (addOneValue z1 refl Γ n) (insert (addEq n 1) Γ) := by
  rcases eq_zero_or_pos n with (rfl | hn)
  · simpa [addOneValue, z1_literal] using hz
  · let t : Bootstrapping.Semiterm V ℒₒᵣ 0 := typedNumeral n + typedNumeral 1
    have hd : DerivationOf S (specializeCtxValue Γ (reflBodyCode : V) t.val refl)
        (insert (subst1Value t.val (reflBodyCode : V)) Γ) :=
      derivationOf_specializeTerm S t.isSemiterm
        (by simpa only [reflSentence, seed_all_literal, reflBodyCode] using hr)
    rw [refl_instance t] at hd
    simpa [addOneValue, ne_of_gt hn, t, addEq, numeral_succ_pos hn] using hd

theorem derivationOf_addPositiveValue (S : ArithmeticTheory) [S.Δ₁]
    {Γ as n k ih : V} (hk : 0 < k)
    (hs : DerivationOf S as (insert (⌜asSentence⌝ : V) Γ))
    (hi : DerivationOf S ih (insert (addEq n k) Γ)) :
    DerivationOf S (addPositiveValue as Γ n k ih) (insert (addEq n (k + 1)) Γ) := by
  have hd := derivationOf_specialize3 S (⌜asMatrix⌝ : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (x := n) (y := k) (z := n + k)
    (by simpa only [asSentence_literal] using hs)
  have hd' : DerivationOf S (specialize3Value (asBodyCode : V) Γ as n k (n + k))
      (insert (imp ℒₒᵣ (addEq n k) (addEq n (k + 1))) Γ) := by
    rw [← as_positive_literal n k hk, asBody_cast, Sentence.quote_eq asMatrix]
    exact hd
  have ho := derivationOf_applyCtxValue S hd' hi
  simpa only [addPositiveValue, as_positive_literal n k hk] using ho

theorem derivationOf_addValue (S : ArithmeticTheory) [S.Δ₁]
    {r0 z1 refl as Γ n m : V}
    (h0 : DerivationOf S r0 (insert (⌜r0Sentence⌝ : V) Γ))
    (h1 : DerivationOf S z1 (insert (⌜z1Sentence⌝ : V) Γ))
    (hr : DerivationOf S refl (insert (⌜reflSentence⌝ : V) Γ))
    (ha : DerivationOf S as (insert (⌜asSentence⌝ : V) Γ)) :
    DerivationOf S (addValue r0 z1 refl as Γ n m) (insert (addEq n m) Γ) := by
  induction m using sigma1_pos_succ_induction
  · simp only [addEq]
    definability
  case zero =>
    rw [addValue_zero]
    have hd : DerivationOf S (specializeCtxValue Γ (r0BodyCode : V) (Arithmetic.numeral n) r0)
        (insert (subst1Value (Arithmetic.numeral n) (r0BodyCode : V)) Γ) :=
      derivationOf_specializeNumeral S (u := n)
        (by simpa only [r0Sentence, seed_all_literal, r0BodyCode] using h0)
    simpa only [r0_instance] using hd
  case one =>
    rw [addValue_one]
    exact derivationOf_addOneValue S h1 hr
  case succ k ih =>
    have hk : 0 < k + 1 := by simp
    have hd := derivationOf_addPositiveValue S hk ha ih
    rw [← addValue_succ r0 z1 refl as Γ n (k + 1) hk] at hd
    simpa [← one_add_one_eq_two, ← add_assoc] using hd

theorem derivationOf_mulPositiveValue (S : ArithmeticTheory) [S.Δ₁]
    {r0 z1 refl as ms Γ n k ih : V} (hk : 0 < k)
    (h0 : DerivationOf S r0 (insert (⌜r0Sentence⌝ : V) Γ))
    (h1 : DerivationOf S z1 (insert (⌜z1Sentence⌝ : V) Γ))
    (hr : DerivationOf S refl (insert (⌜reflSentence⌝ : V) Γ))
    (ha : DerivationOf S as (insert (⌜asSentence⌝ : V) Γ))
    (hs : DerivationOf S ms (insert (⌜msSentence⌝ : V) Γ))
    (hi : DerivationOf S ih (insert (mulEq n k) Γ)) :
    DerivationOf S (mulPositiveValue r0 z1 refl as ms Γ n k ih) (insert (mulEq n (k + 1)) Γ) := by
  have hd := derivationOf_specialize4 S (⌜msMatrix⌝ : Bootstrapping.Semiformula V ℒₒᵣ 4)
    (x := n) (y := k) (z := n * k) (w := n * k + n)
    (by simpa only [msSentence_literal] using hs)
  have hd' : DerivationOf S (specialize4Value (msBodyCode : V) Γ ms n k (n * k) (n * k + n))
      (insert (imp ℒₒᵣ (mulEq n k) (imp ℒₒᵣ (addEq (n * k) n) (mulEq n (k + 1)))) Γ) := by
    rw [← ms_positive_literal n k hk, msBody_cast, Sentence.quote_eq msMatrix]
    exact hd
  have he := derivationOf_applyCtxValue S hd' hi
  have hadd := derivationOf_addValue S (n := n * k) (m := n) h0 h1 hr ha
  have ho := derivationOf_applyCtxValue S he hadd
  simpa only [mulPositiveValue, ms_positive_literal n k hk, consequentValue_imp] using ho

theorem derivationOf_mulValue (S : ArithmeticTheory) [S.Δ₁]
    {r0 z1 refl as m0 m1 ms Γ n m : V}
    (h0 : DerivationOf S r0 (insert (⌜r0Sentence⌝ : V) Γ))
    (h1 : DerivationOf S z1 (insert (⌜z1Sentence⌝ : V) Γ))
    (hr : DerivationOf S refl (insert (⌜reflSentence⌝ : V) Γ))
    (ha : DerivationOf S as (insert (⌜asSentence⌝ : V) Γ))
    (hm0 : DerivationOf S m0 (insert (⌜m0Sentence⌝ : V) Γ))
    (hm1 : DerivationOf S m1 (insert (⌜m1Sentence⌝ : V) Γ))
    (hms : DerivationOf S ms (insert (⌜msSentence⌝ : V) Γ)) :
    DerivationOf S (mulValue r0 z1 refl as m0 m1 ms Γ n m) (insert (mulEq n m) Γ) := by
  induction m using sigma1_pos_succ_induction
  · simp only [mulEq]
    definability
  case zero =>
    rw [mulValue_zero]
    have hd : DerivationOf S (specializeCtxValue Γ (m0BodyCode : V) (Arithmetic.numeral n) m0)
        (insert (subst1Value (Arithmetic.numeral n) (m0BodyCode : V)) Γ) :=
      derivationOf_specializeNumeral S (u := n)
        (by simpa only [m0Sentence, seed_all_literal, m0BodyCode] using hm0)
    simpa only [m0_instance] using hd
  case one =>
    rw [mulValue_one]
    have hd : DerivationOf S (specializeCtxValue Γ (m1BodyCode : V) (Arithmetic.numeral n) m1)
        (insert (subst1Value (Arithmetic.numeral n) (m1BodyCode : V)) Γ) :=
      derivationOf_specializeNumeral S (u := n)
        (by simpa only [m1Sentence, seed_all_literal, m1BodyCode] using hm1)
    simpa only [m1_instance] using hd
  case succ k ih =>
    have hk : 0 < k + 1 := by simp
    have hd := derivationOf_mulPositiveValue S hk h0 h1 hr ha hms ih
    rw [← mulValue_succ r0 z1 refl as m0 m1 ms Γ n (k + 1) hk] at hd
    simpa [← one_add_one_eq_two, ← add_assoc] using hd

theorem addGraph_preserves_derivationOf (S : ArithmeticTheory) [S.Δ₁]
    {o r0 z1 refl as Γ n m : V}
    (ho : addGraph.val.Evalb ![o, r0, z1, refl, as, Γ, n, m])
    (h0 : DerivationOf S r0 (insert (⌜r0Sentence⌝ : V) Γ))
    (h1 : DerivationOf S z1 (insert (⌜z1Sentence⌝ : V) Γ))
    (hr : DerivationOf S refl (insert (⌜reflSentence⌝ : V) Γ))
    (ha : DerivationOf S as (insert (⌜asSentence⌝ : V) Γ)) :
    DerivationOf S o (insert (addEq n m) Γ) := by
  rw [(addGraph_iff _ _ _ _ _ _ _ _).mp ho]
  exact derivationOf_addValue S h0 h1 hr ha

theorem mulGraph_preserves_derivationOf (S : ArithmeticTheory) [S.Δ₁]
    {o r0 z1 refl as m0 m1 ms Γ n m : V}
    (ho : mulGraph.val.Evalb ![o, r0, z1, refl, as, m0, m1, ms, Γ, n, m])
    (h0 : DerivationOf S r0 (insert (⌜r0Sentence⌝ : V) Γ))
    (h1 : DerivationOf S z1 (insert (⌜z1Sentence⌝ : V) Γ))
    (hr : DerivationOf S refl (insert (⌜reflSentence⌝ : V) Γ))
    (ha : DerivationOf S as (insert (⌜asSentence⌝ : V) Γ))
    (hm0 : DerivationOf S m0 (insert (⌜m0Sentence⌝ : V) Γ))
    (hm1 : DerivationOf S m1 (insert (⌜m1Sentence⌝ : V) Γ))
    (hms : DerivationOf S ms (insert (⌜msSentence⌝ : V) Γ)) :
    DerivationOf S o (insert (mulEq n m) Γ) := by
  rw [(mulGraph_iff _ _ _ _ _ _ _ _ _ _ _).mp ho]
  exact derivationOf_mulValue S h0 h1 hr ha hm0 hm1 hms

end FailureOfComposition.NativeNumeralArithmetic
