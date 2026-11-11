/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import FailureOfComposition.NativeFamilyInstances
public import FailureOfComposition.NativeFamilyConstructor

/-!
# Context-preserving internal extraction

The five supplied derivations share the one-sided context `Gamma`.
Its validity follows from those derivations. The constructor theorem needs
no arithmetic-strength, consistency, soundness, or totality hypothesis:
the supplied seed already supplies the required arithmetic argument.
-/

@[expose] public section

set_option autoImplicit false

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic

namespace FailureOfComposition.NativeFamilyExtraction

open FFL.FirstOrder.Arithmetic.Bootstrapping
open FailureOfComposition.NativeContextMP
open FailureOfComposition.NativeContextSpecialization
open FailureOfComposition.NativeEqualityTransport

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]

theorem derivationOf_specializeNumeral (S : ArithmeticTheory) [S.Δ₁]
    {Γ body d u : V} (hd : DerivationOf S d (insert (^∀ body) Γ)) :
    DerivationOf S (specializeCtxValue Γ body (Arithmetic.numeral u) d)
      (insert (FailureOfComposition.NativeSubstitution.subst1Value
        (Arithmetic.numeral u) body) Γ) := by
  have hb : IsSemiformula ℒₒᵣ 1 body := by
    simpa using (IsFormulaSet.insert_iff.mp hd.isFormulaSet).1
  rw [FailureOfComposition.NativeSubstitution.subst1Value_eq_substs1 (by simp) hb]
  exact derivationOf_specializeCtxValue S (by simp) hd


theorem derivationOf_applyCtxValue (S : ArithmeticTheory) [S.Δ₁]
    {Γ a b e p : V} (he : DerivationOf S e (insert (imp ℒₒᵣ a b) Γ))
    (hp : DerivationOf S p (insert a Γ)) :
    DerivationOf S (applyCtxValue Γ (imp ℒₒᵣ a b) e p) (insert b Γ) := by
  have ha : IsFormula ℒₒᵣ a := (IsFormulaSet.insert_iff.mp hp.isFormulaSet).1
  simpa only [applyCtxValue, antecedentValue_imp ha, consequentValue_imp] using
    derivationOf_mpCtxValue S he hp

/-- All nine constructor inputs, and its output, are internal model elements. -/
theorem derivationOf_extractValue (S : ArithmeticTheory) [S.Δ₁]
    (M : 𝚺₁.Semisentence 1) (h k : ℕ) {seed Γ e m pH pK u y r : V}
    (hs : DerivationOf S seed (insert (⌜extractionSeed M h k⌝ : V) Γ))
    (he : DerivationOf S e (insert (⌜familyEq M h k⌝ : V) Γ))
    (hm : DerivationOf S m (insert (instanceValue M.val ![u]) Γ))
    (hh : DerivationOf S pH (insert (instanceValue (outputGraph h).val ![u, y]) Γ))
    (hk : DerivationOf S pK (insert (instanceValue (outputGraph k).val ![u, r]) Γ)) :
    DerivationOf S (extractValue (extractionBodyCode M h k) seed Γ e m pH pK u y r)
      (insert (eqValue y r) Γ) := by
  let b₁ : V := (⌜extractionBodyU M h k⌝ : V)
  let b₂ : V := ^∀ (matrixAfterU M h k u).val
  let b₃ : V := (matrixAfterY M h k u y).val
  let d₁ := specializeCtxValue Γ b₁ (Arithmetic.numeral u) seed
  let d₂ := specializeCtxValue Γ b₂ (Arithmetic.numeral y) d₁
  let d₃ := specializeCtxValue Γ b₃ (Arithmetic.numeral r) d₂
  let a₀ : V := (⌜familyEq M h k⌝ : V)
  let a₁ := instanceValue M.val ![u]
  let a₂ := instanceValue (outputGraph h).val ![u, y]
  let a₃ := instanceValue (outputGraph k).val ![u, r]
  let a₄ := eqValue y r
  let c₃ := imp ℒₒᵣ a₃ a₄
  let c₂ := imp ℒₒᵣ a₂ c₃
  let c₁ := imp ℒₒᵣ a₁ c₂
  let c₀ := imp ℒₒᵣ a₀ c₁
  have hd₁ : DerivationOf S d₁ (insert (^∀ b₂) Γ) := by
    have hd := derivationOf_specializeNumeral S (u := u)
      (by simpa only [seed_quote] using hs)
    simpa only [b₁, b₂, d₁, first_specialization] using hd
  have hd₂ : DerivationOf S d₂ (insert (^∀ b₃) Γ) := by
    have hd := derivationOf_specializeNumeral S (u := y) hd₁
    simpa only [b₂, b₃, d₂, second_specialization] using hd
  have hd₃ : DerivationOf S d₃ (insert c₀ Γ) := by
    have hd := derivationOf_specializeNumeral S (u := r) hd₂
    simpa only [b₃, d₃, third_specialization, matrix_instance] using hd
  have hd₄ := derivationOf_applyCtxValue S hd₃ he
  have hd₅ := derivationOf_applyCtxValue S hd₄ hm
  have hd₆ := derivationOf_applyCtxValue S hd₅ hh
  have hd₇ := derivationOf_applyCtxValue S hd₆ hk
  simpa only [extractValue, seedBody_quote, first_specialization, allBodyValue_all,
    second_specialization, third_specialization, matrix_instance, consequentValue_imp,
    b₁, b₂, b₃, d₁, d₂, d₃, a₀, a₁, a₂, a₃, a₄, c₀, c₁, c₂, c₃] using hd₇

theorem extractGraph_preserves_derivationOf (S : ArithmeticTheory) [S.Δ₁]
    (M : 𝚺₁.Semisentence 1) (h k : ℕ) {o seed Γ e m pH pK u y r : V}
    (ho : (extractGraph (extractionBodyCode M h k)).val.Evalb
      ![o, seed, Γ, e, m, pH, pK, u, y, r])
    (hs : DerivationOf S seed (insert (⌜extractionSeed M h k⌝ : V) Γ))
    (he : DerivationOf S e (insert (⌜familyEq M h k⌝ : V) Γ))
    (hm : DerivationOf S m (insert (instanceValue M.val ![u]) Γ))
    (hh : DerivationOf S pH (insert (instanceValue (outputGraph h).val ![u, y]) Γ))
    (hk : DerivationOf S pK (insert (instanceValue (outputGraph k).val ![u, r]) Γ)) :
    DerivationOf S o (insert (eqValue y r) Γ) := by
  rw [(extractGraph_iff _ _ _ _ _ _ _ _ _ _ _).mp ho]
  exact derivationOf_extractValue S M h k hs he hm hh hk

theorem proof_extractValue (S : ArithmeticTheory) [S.Δ₁]
    (M : 𝚺₁.Semisentence 1) (h k : ℕ) {seed e m pH pK u y r : V}
    (hs : Proof S seed (⌜extractionSeed M h k⌝ : V))
    (he : Proof S e (⌜familyEq M h k⌝ : V))
    (hm : Proof S m (instanceValue M.val ![u]))
    (hh : Proof S pH (instanceValue (outputGraph h).val ![u, y]))
    (hk : Proof S pK (instanceValue (outputGraph k).val ![u, r])) :
    Proof S (extractValue (extractionBodyCode M h k) seed 0 e m pH pK u y r)
      (eqValue y r) := by
  simpa only [Proof, singleton_eq_insert, emptyset_def] using
    derivationOf_extractValue S M h k
      (by simpa only [Proof, singleton_eq_insert, emptyset_def] using hs)
      (by simpa only [Proof, singleton_eq_insert, emptyset_def] using he)
      (by simpa only [Proof, singleton_eq_insert, emptyset_def] using hm)
      (by simpa only [Proof, singleton_eq_insert, emptyset_def] using hh)
      (by simpa only [Proof, singleton_eq_insert, emptyset_def] using hk)

end FailureOfComposition.NativeFamilyExtraction
