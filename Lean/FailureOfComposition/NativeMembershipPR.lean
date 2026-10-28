/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import FailureOfComposition.NativeMembershipConstructor

/-!
# Joint primitive recursiveness of closure assembly

The six varying arguments are packed as `((seed,Gamma),((a,t),(e,d)))`.
The explicit template code is fixed; no canonical theory graph is evaluated.
-/

set_option autoImplicit false

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic

namespace FailureOfComposition.NativeMembershipAssembly

open FailureOfComposition.NativeFamilyExtraction
open FailureOfComposition.NativeContextSpecialization
open FailureOfComposition.NativeContextMP
open FailureOfComposition.NativeSubstitution
open FailureOfComposition.NativeEqualityTransport

set_option backward.isDefEq.respectTransparency false in
private theorem primrec_specialize {X : Type*} [Primcodable X]
    {g b t d : X → ℕ} (hg : Primrec g) (hb : Primrec b)
    (ht : Primrec t) (hd : Primrec d) :
    Primrec (fun x => specializeCtx (g x) (b x) (t x) (d x)) := by
  apply (primrec_specializeCtxPacked.comp (((hg.pair hb).pair ht).pair hd)).of_eq
  intro x
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem primrec_apply {X : Type*} [Primcodable X]
    {g c e p : X → ℕ} (hg : Primrec g) (hc : Primrec c)
    (he : Primrec e) (hp : Primrec p) :
    Primrec (fun x => applyCtxCode (g x) (c x) (e x) (p x)) := by
  apply (primrec_mpCtxPacked.comp ((((hg.pair (primrec_antecedentCode.comp hc)).pair
    (primrec_consequentCode.comp hc)).pair he).pair hp)).of_eq
  intro x
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem primrec_closureCtxPacked (body : ℕ) : Primrec (closureCtxPacked body) := by
  let seed : ClosureArgs → ℕ := fun z => z.1.1
  let g : ClosureArgs → ℕ := fun z => z.1.2
  let a : ClosureArgs → ℕ := fun z => z.2.1.1
  let t : ClosureArgs → ℕ := fun z => z.2.1.2
  let e : ClosureArgs → ℕ := fun z => z.2.2.1
  let d : ClosureArgs → ℕ := fun z => z.2.2.2
  have hs : Primrec seed := Primrec.fst.comp Primrec.fst
  have hg : Primrec g := Primrec.snd.comp Primrec.fst
  have ha : Primrec a := Primrec.fst.comp (Primrec.fst.comp Primrec.snd)
  have ht : Primrec t := Primrec.snd.comp (Primrec.fst.comp Primrec.snd)
  have he : Primrec e := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hd : Primrec d := Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  let ne : ClosureArgs → ℕ := fun z => numeralTermCode (e z)
  let nd : ClosureArgs → ℕ := fun z => numeralTermCode (d z)
  have hne : Primrec ne := primrec_numeralTermCode.comp he
  have hnd : Primrec nd := primrec_numeralTermCode.comp hd
  let b₂ : ClosureArgs → ℕ := fun z => allBodyCode (subst1Code (ne z) body)
  let c₀ : ClosureArgs → ℕ := fun z => subst1Code (nd z) (b₂ z)
  let c₁ : ClosureArgs → ℕ := fun z => consequentCode (c₀ z)
  have hb₂ : Primrec b₂ := primrec_allBodyCode.comp
    (primrec₂_subst1Code.comp hne (Primrec.const body))
  have hc₀ : Primrec c₀ := primrec₂_subst1Code.comp hnd hb₂
  have hc₁ : Primrec c₁ := primrec_consequentCode.comp hc₀
  let d₁ : ClosureArgs → ℕ := fun z => specializeCtx (g z) body (ne z) (seed z)
  let d₂ : ClosureArgs → ℕ := fun z => specializeCtx (g z) (b₂ z) (nd z) (d₁ z)
  let d₃ : ClosureArgs → ℕ := fun z => applyCtxCode (g z) (c₀ z) (d₂ z) (a z)
  have hd₁ : Primrec d₁ := primrec_specialize hg (Primrec.const body) hne hs
  have hd₂ : Primrec d₂ := primrec_specialize hg hb₂ hnd hd₁
  have hd₃ : Primrec d₃ := primrec_apply hg hc₀ hd₂ ha
  apply (primrec_apply hg hc₁ hd₃ ht).of_eq
  intro z
  simp only [closureCtxPacked, closureCtx, seed, g, a, t, e, d,
    ne, nd, b₂, c₀, c₁, d₁, d₂, d₃]

end FailureOfComposition.NativeMembershipAssembly
