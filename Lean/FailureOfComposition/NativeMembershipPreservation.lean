/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import FailureOfComposition.NativeMembershipInstances
import FailureOfComposition.NativeMembershipConstructor

/-!
# Same-context preservation for native membership assembly

The supplied seed carries the arithmetic argument. The conditional inference
theorems use only same-context derivations, without assumptions of actual
totality, source membership, soundness, or consistency. Formula instances are
closed by internal numerals; this is not a general free-variable compiler.
-/

set_option autoImplicit false

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic

namespace FailureOfComposition.NativeMembershipAssembly

open FFL.FirstOrder.Arithmetic.Bootstrapping
open FailureOfComposition.NativeFamilyExtraction
open FailureOfComposition.NativeContextSpecialization

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]

theorem derivationOf_pointwiseValue (S : ArithmeticTheory) [S.Δ₁]
    (M : 𝚺₁.Semisentence 1) (h k : ℕ) {seed Γ a t m p e u d : V}
    (hs : DerivationOf S seed (insert (⌜pointwiseSchema S M h k⌝ : V) Γ))
    (ha : DerivationOf S a (insert (instanceValue (familyAcceptance S M h k).val ![e]) Γ))
    (ht : DerivationOf S t (insert (⌜totality M k⌝ : V) Γ))
    (hm : DerivationOf S m (insert (instanceValue M.val ![u]) Γ))
    (hp : DerivationOf S p (insert (instanceValue (membershipFormula S h).val ![u, d]) Γ)) :
    DerivationOf S (pointwiseValue (pointwiseBodyCode S M h k) seed Γ a t m p e u d)
      (insert (instanceValue (membershipFormula S k).val ![u, d]) Γ) := by
  let b₁ : V := (⌜pointwiseBodyE S M h k⌝ : V)
  let b₂ : V := ^∀ (pointwiseAfterE S M h k e).val
  let b₃ : V := (pointwiseAfterU S M h k e u).val
  let d₁ := specializeCtxValue Γ b₁ (Arithmetic.numeral e) seed
  let d₂ := specializeCtxValue Γ b₂ (Arithmetic.numeral u) d₁
  let d₃ := specializeCtxValue Γ b₃ (Arithmetic.numeral d) d₂
  let a₀ := instanceValue (familyAcceptance S M h k).val ![e]
  let a₁ : V := (⌜totality M k⌝ : V)
  let a₂ := instanceValue M.val ![u]
  let a₃ := instanceValue (membershipFormula S h).val ![u, d]
  let a₄ := instanceValue (membershipFormula S k).val ![u, d]
  let c₃ := imp ℒₒᵣ a₃ a₄
  let c₂ := imp ℒₒᵣ a₂ c₃
  let c₁ := imp ℒₒᵣ a₁ c₂
  let c₀ := imp ℒₒᵣ a₀ c₁
  have hd₁ : DerivationOf S d₁ (insert (^∀ b₂) Γ) := by
    have hd := derivationOf_specializeNumeral S (u := e)
      (by simpa only [pointwiseSchema_quote] using hs)
    simpa only [b₁, b₂, d₁, pointwise_first] using hd
  have hd₂ : DerivationOf S d₂ (insert (^∀ b₃) Γ) := by
    have hd := derivationOf_specializeNumeral S (u := u) hd₁
    simpa only [b₂, b₃, d₂, pointwise_second] using hd
  have hd₃ : DerivationOf S d₃ (insert c₀ Γ) := by
    have hd := derivationOf_specializeNumeral S (u := d) hd₂
    simpa only [b₃, d₃, pointwise_third, pointwise_matrix_instance] using hd
  have hd₄ := derivationOf_applyCtxValue S hd₃ ha
  have hd₅ := derivationOf_applyCtxValue S hd₄ ht
  have hd₆ := derivationOf_applyCtxValue S hd₅ hm
  have hd₇ := derivationOf_applyCtxValue S hd₆ hp
  simpa only [pointwiseValue, extractValue, pointwiseBody_quote, pointwise_first,
    allBodyValue_all, pointwise_second, pointwise_third, pointwise_matrix_instance,
    consequentValue_imp, b₁, b₂, b₃, d₁, d₂, d₃, a₀, a₁, a₂, a₃, a₄,
    c₀, c₁, c₂, c₃] using hd₇

theorem pointwiseGraph_preserves_derivationOf (S : ArithmeticTheory) [S.Δ₁]
    (M : 𝚺₁.Semisentence 1) (h k : ℕ) {o seed Γ a t m p e u d : V}
    (ho : (pointwiseGraph (pointwiseBodyCode S M h k)).val.Evalb
      ![o, seed, Γ, a, t, m, p, e, u, d])
    (hs : DerivationOf S seed (insert (⌜pointwiseSchema S M h k⌝ : V) Γ))
    (ha : DerivationOf S a (insert (instanceValue (familyAcceptance S M h k).val ![e]) Γ))
    (ht : DerivationOf S t (insert (⌜totality M k⌝ : V) Γ))
    (hm : DerivationOf S m (insert (instanceValue M.val ![u]) Γ))
    (hp : DerivationOf S p (insert (instanceValue (membershipFormula S h).val ![u, d]) Γ)) :
    DerivationOf S o (insert (instanceValue (membershipFormula S k).val ![u, d]) Γ) := by
  rw [(pointwiseGraph_iff _ _ _ _ _ _ _ _ _ _ _).mp ho]
  exact derivationOf_pointwiseValue S M h k hs ha ht hm hp

theorem derivationOf_closureValue (S : ArithmeticTheory) [S.Δ₁]
    (M : 𝚺₁.Semisentence 1) (h k : ℕ) {seed Γ a t e d : V}
    (hs : DerivationOf S seed (insert (⌜closureSchema S M h k⌝ : V) Γ))
    (ha : DerivationOf S a (insert (instanceValue (familyAcceptance S M h k).val ![e]) Γ))
    (ht : DerivationOf S t (insert (⌜totality M k⌝ : V) Γ)) :
    DerivationOf S (closureValue (closureBodyCode S M h k) seed Γ a t e d)
      (insert (instanceValue (transferClosure S M h k) ![d]) Γ) := by
  let b₁ : V := (⌜closureBodyE S M h k⌝ : V)
  let b₂ : V := (closureAfterE S M h k e).val
  let d₁ := specializeCtxValue Γ b₁ (Arithmetic.numeral e) seed
  let d₂ := specializeCtxValue Γ b₂ (Arithmetic.numeral d) d₁
  let a₀ := instanceValue (familyAcceptance S M h k).val ![e]
  let a₁ : V := (⌜totality M k⌝ : V)
  let a₂ := instanceValue (transferClosure S M h k) ![d]
  let c₁ := imp ℒₒᵣ a₁ a₂
  let c₀ := imp ℒₒᵣ a₀ c₁
  have hd₁ : DerivationOf S d₁ (insert (^∀ b₂) Γ) := by
    have hd := derivationOf_specializeNumeral S (u := e)
      (by simpa only [closureSchema_quote] using hs)
    simpa only [b₁, b₂, d₁, closure_first] using hd
  have hd₂ : DerivationOf S d₂ (insert c₀ Γ) := by
    have hd := derivationOf_specializeNumeral S (u := d) hd₁
    simpa only [b₂, d₂, closure_second, closure_matrix_instance] using hd
  have hd₃ := derivationOf_applyCtxValue S hd₂ ha
  have hd₄ := derivationOf_applyCtxValue S hd₃ ht
  simpa only [closureValue, closureBody_quote, closure_first, allBodyValue_all,
    closure_second, closure_matrix_instance, consequentValue_imp,
    b₁, b₂, d₁, d₂, a₀, a₁, a₂, c₀, c₁] using hd₄

theorem closureGraph_preserves_derivationOf (S : ArithmeticTheory) [S.Δ₁]
    (M : 𝚺₁.Semisentence 1) (h k : ℕ) {o seed Γ a t e d : V}
    (ho : (closureGraph (closureBodyCode S M h k)).val.Evalb ![o, seed, Γ, a, t, e, d])
    (hs : DerivationOf S seed (insert (⌜closureSchema S M h k⌝ : V) Γ))
    (ha : DerivationOf S a (insert (instanceValue (familyAcceptance S M h k).val ![e]) Γ))
    (ht : DerivationOf S t (insert (⌜totality M k⌝ : V) Γ)) :
    DerivationOf S o (insert (instanceValue (transferClosure S M h k) ![d]) Γ) := by
  rw [(closureGraph_iff _ _ _ _ _ _ _ _).mp ho]
  exact derivationOf_closureValue S M h k hs ha ht

theorem proof_pointwiseValue (S : ArithmeticTheory) [S.Δ₁]
    (M : 𝚺₁.Semisentence 1) (h k : ℕ) {seed a t m p e u d : V}
    (hs : Proof S seed (⌜pointwiseSchema S M h k⌝ : V))
    (ha : Proof S a (instanceValue (familyAcceptance S M h k).val ![e]))
    (ht : Proof S t (⌜totality M k⌝ : V)) (hm : Proof S m (instanceValue M.val ![u]))
    (hp : Proof S p (instanceValue (membershipFormula S h).val ![u, d])) :
    Proof S (pointwiseValue (pointwiseBodyCode S M h k) seed 0 a t m p e u d)
      (instanceValue (membershipFormula S k).val ![u, d]) := by
  simpa only [Proof, singleton_eq_insert, emptyset_def] using
    derivationOf_pointwiseValue S M h k
      (by simpa only [Proof, singleton_eq_insert, emptyset_def] using hs)
      (by simpa only [Proof, singleton_eq_insert, emptyset_def] using ha)
      (by simpa only [Proof, singleton_eq_insert, emptyset_def] using ht)
      (by simpa only [Proof, singleton_eq_insert, emptyset_def] using hm)
      (by simpa only [Proof, singleton_eq_insert, emptyset_def] using hp)

theorem proof_closureValue (S : ArithmeticTheory) [S.Δ₁]
    (M : 𝚺₁.Semisentence 1) (h k : ℕ) {seed a t e d : V}
    (hs : Proof S seed (⌜closureSchema S M h k⌝ : V))
    (ha : Proof S a (instanceValue (familyAcceptance S M h k).val ![e]))
    (ht : Proof S t (⌜totality M k⌝ : V)) :
    Proof S (closureValue (closureBodyCode S M h k) seed 0 a t e d)
      (instanceValue (transferClosure S M h k) ![d]) := by
  simpa only [Proof, singleton_eq_insert, emptyset_def] using
    derivationOf_closureValue S M h k
      (by simpa only [Proof, singleton_eq_insert, emptyset_def] using hs)
      (by simpa only [Proof, singleton_eq_insert, emptyset_def] using ha)
      (by simpa only [Proof, singleton_eq_insert, emptyset_def] using ht)

end FailureOfComposition.NativeMembershipAssembly
