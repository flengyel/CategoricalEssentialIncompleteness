/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import FailureOfComposition.NativeFamilyConstructor

/-!
# Joint primitive recursiveness of the nine-input constructor

The template code is an explicit numerical parameter. No model-side or
choice-based definition is evaluated by this proof constructor.
-/

@[expose] public section

set_option autoImplicit false

open Encodable FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic

namespace FailureOfComposition.NativeFamilyExtraction

open FailureOfComposition.NativeContextMP
open FailureOfComposition.NativeContextSpecialization
open FailureOfComposition.NativeSubstitution
open FailureOfComposition.NativeEqualityTransport

theorem primrec_allBodyCode : Primrec allBodyCode := by
  exact Primrec.snd.comp (Primrec.unpair.comp (Primrec.nat_sub.comp Primrec.id (Primrec.const 1)))

theorem primrec_consequentCode : Primrec consequentCode :=
  Primrec.snd.comp (Primrec.unpair.comp primrec_allBodyCode)

theorem primrec_antecedentCode : Primrec antecedentCode :=
  primrec_formulaNegTotalCode.comp (Primrec.fst.comp (Primrec.unpair.comp primrec_allBodyCode))

-- Keep the already-verified numerical constructors opaque during composition.
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
theorem primrec_extractCtxPacked (body : ℕ) : Primrec (extractCtxPacked body) := by
  let seed : ExtractArgs → ℕ := fun z => z.1.1.1
  let g : ExtractArgs → ℕ := fun z => z.1.1.2
  let e : ExtractArgs → ℕ := fun z => z.1.2
  let m : ExtractArgs → ℕ := fun z => z.2.1.1.1
  let pH : ExtractArgs → ℕ := fun z => z.2.1.1.2
  let pK : ExtractArgs → ℕ := fun z => z.2.1.2
  let u : ExtractArgs → ℕ := fun z => z.2.2.1.1
  let y : ExtractArgs → ℕ := fun z => z.2.2.1.2
  let r : ExtractArgs → ℕ := fun z => z.2.2.2
  have hs : Primrec seed := Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
  have hg : Primrec g := Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
  have he : Primrec e := Primrec.snd.comp Primrec.fst
  have hm : Primrec m := Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.snd))
  have hh : Primrec pH := Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.snd))
  have hk : Primrec pK := Primrec.snd.comp (Primrec.fst.comp Primrec.snd)
  have hu : Primrec u := Primrec.fst.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
  have hy : Primrec y := Primrec.snd.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
  have hr : Primrec r := Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  let nu : ExtractArgs → ℕ := fun z => numeralTermCode (u z)
  let ny : ExtractArgs → ℕ := fun z => numeralTermCode (y z)
  let nr : ExtractArgs → ℕ := fun z => numeralTermCode (r z)
  have hnu : Primrec nu := primrec_numeralTermCode.comp hu
  have hny : Primrec ny := primrec_numeralTermCode.comp hy
  have hnr : Primrec nr := primrec_numeralTermCode.comp hr
  let b₂ : ExtractArgs → ℕ := fun z => allBodyCode (subst1Code (nu z) body)
  let b₃ : ExtractArgs → ℕ := fun z => allBodyCode (subst1Code (ny z) (b₂ z))
  let c₀ : ExtractArgs → ℕ := fun z => subst1Code (nr z) (b₃ z)
  let c₁ : ExtractArgs → ℕ := fun z => consequentCode (c₀ z)
  let c₂ : ExtractArgs → ℕ := fun z => consequentCode (c₁ z)
  let c₃ : ExtractArgs → ℕ := fun z => consequentCode (c₂ z)
  have hb₂ : Primrec b₂ := primrec_allBodyCode.comp
    (primrec₂_subst1Code.comp hnu (Primrec.const body))
  have hb₃ : Primrec b₃ := primrec_allBodyCode.comp (primrec₂_subst1Code.comp hny hb₂)
  have hc₀ : Primrec c₀ := primrec₂_subst1Code.comp hnr hb₃
  have hc₁ : Primrec c₁ := primrec_consequentCode.comp hc₀
  have hc₂ : Primrec c₂ := primrec_consequentCode.comp hc₁
  have hc₃ : Primrec c₃ := primrec_consequentCode.comp hc₂
  let d₁ : ExtractArgs → ℕ := fun z => specializeCtx (g z) body (nu z) (seed z)
  let d₂ : ExtractArgs → ℕ := fun z => specializeCtx (g z) (b₂ z) (ny z) (d₁ z)
  let d₃ : ExtractArgs → ℕ := fun z => specializeCtx (g z) (b₃ z) (nr z) (d₂ z)
  let d₄ : ExtractArgs → ℕ := fun z => applyCtxCode (g z) (c₀ z) (d₃ z) (e z)
  let d₅ : ExtractArgs → ℕ := fun z => applyCtxCode (g z) (c₁ z) (d₄ z) (m z)
  let d₆ : ExtractArgs → ℕ := fun z => applyCtxCode (g z) (c₂ z) (d₅ z) (pH z)
  have hd₁ : Primrec d₁ := primrec_specialize hg (Primrec.const body) hnu hs
  have hd₂ : Primrec d₂ := primrec_specialize hg hb₂ hny hd₁
  have hd₃ : Primrec d₃ := primrec_specialize hg hb₃ hnr hd₂
  have hd₄ : Primrec d₄ := primrec_apply hg hc₀ hd₃ he
  have hd₅ : Primrec d₅ := primrec_apply hg hc₁ hd₄ hm
  have hd₆ : Primrec d₆ := primrec_apply hg hc₂ hd₅ hh
  apply (primrec_apply hg hc₃ hd₆ hk).of_eq
  intro z
  simp only [extractCtxPacked, extractCtx, seed, g, e, m, pH, pK, u, y, r,
    nu, ny, nr, b₂, b₃, c₀, c₁, c₂, c₃, d₁, d₂, d₃, d₄, d₅, d₆]

end FailureOfComposition.NativeFamilyExtraction
