/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import FailureOfComposition.NativeFamilyPR
public import FailureOfComposition.NativeFamilyNat

/-!
# Numerical pointwise and universal-closure assembly

Pointwise assembly reuses the nine-input extractor, mapping its arguments
to `(seed,Gamma,a,t,m,p,e,u,d)`. Closure assembly uses two specializations
and two same-context MP steps. Both functions take an explicit natural
template code; neither computes a theory graph or selects proof witnesses.
-/

@[expose] public section

set_option autoImplicit false

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic

namespace FailureOfComposition.NativeMembershipAssembly

open FailureOfComposition.NativeFamilyExtraction
open FailureOfComposition.NativeContextSpecialization
open FailureOfComposition.NativeSubstitution
open FailureOfComposition.NativeEqualityTransport
open FFL.FirstOrder.Arithmetic.Bootstrapping

def pointwiseCtx (body seed Γ a t m p e u d : ℕ) : ℕ :=
  extractCtx body seed Γ a t m p e u d

abbrev PointwiseArgs := ExtractArgs

/-- Packed as `(((seed,Gamma),a),(((t,m),p),((e,u),d)))`. -/
def pointwiseCtxPacked (body : ℕ) (z : PointwiseArgs) : ℕ := extractCtxPacked body z

theorem primrec_pointwiseCtxPacked (body : ℕ) : Primrec (pointwiseCtxPacked body) :=
  primrec_extractCtxPacked body

def closureCtx (body seed Γ a t e d : ℕ) : ℕ :=
  let ne := numeralTermCode e
  let nd := numeralTermCode d
  let b₂ := allBodyCode (subst1Code ne body)
  let c₀ := subst1Code nd b₂
  let c₁ := consequentCode c₀
  let d₁ := specializeCtx Γ body ne seed
  let d₂ := specializeCtx Γ b₂ nd d₁
  let d₃ := applyCtxCode Γ c₀ d₂ a
  applyCtxCode Γ c₁ d₃ t

abbrev ClosureArgs := (ℕ × ℕ) × ((ℕ × ℕ) × (ℕ × ℕ))

/-- Packed as `((seed,Gamma),((a,t),(e,d)))`. -/
def closureCtxPacked (body : ℕ) (z : ClosureArgs) : ℕ :=
  closureCtx body z.1.1 z.1.2 z.2.1.1 z.2.1.2 z.2.2.1 z.2.2.2

section Internal

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]

noncomputable def pointwiseValue (body : ℕ) (seed Γ a t m p e u d : V) : V :=
  extractValue body seed Γ a t m p e u d

noncomputable def pointwiseGraph (body : ℕ) : 𝚺₁.Semisentence 10 := extractGraph body

theorem pointwiseGraph_iff (body : ℕ) (o seed Γ a t m p e u d : V) :
    (pointwiseGraph body).val.Evalb ![o, seed, Γ, a, t, m, p, e, u, d] ↔
      o = pointwiseValue body seed Γ a t m p e u d :=
  extractGraph_iff body o seed Γ a t m p e u d

theorem pointwiseGraph_total (body : ℕ) (seed Γ a t m p e u d : V) :
    ∃ o : V, (pointwiseGraph body).val.Evalb ![o, seed, Γ, a, t, m, p, e, u, d] :=
  extractGraph_total body seed Γ a t m p e u d

theorem pointwiseGraph_functional (body : ℕ) {o o' seed Γ a t m p e u d : V}
    (ho : (pointwiseGraph body).val.Evalb ![o, seed, Γ, a, t, m, p, e, u, d])
    (ho' : (pointwiseGraph body).val.Evalb ![o', seed, Γ, a, t, m, p, e, u, d]) : o = o' :=
  extractGraph_functional body ho ho'

noncomputable def closureValue (body : ℕ) (seed Γ a t e d : V) : V :=
  let b₁ := ORingStructure.numeral body
  let ne := Arithmetic.numeral e
  let nd := Arithmetic.numeral d
  let b₂ := sndIdx (subst1Value ne b₁)
  let c₀ := subst1Value nd b₂
  let c₁ := consequentValue c₀
  let d₁ := specializeCtxValue Γ b₁ ne seed
  let d₂ := specializeCtxValue Γ b₂ nd d₁
  let d₃ := applyCtxValue Γ c₀ d₂ a
  applyCtxValue Γ c₁ d₃ t

noncomputable def closureGraph (body : ℕ) : 𝚺₁.Semisentence 7 := .mkSigma
  “o seed Γ a t e d.
    ∃ ne, !numeralTermCodeGraph ne e ∧
    ∃ nd, !numeralTermCodeGraph nd d ∧
    ∃ s₁, !subst1Graph s₁ ne ↑body ∧ ∃ b₂, !sndIdxDef b₂ s₁ ∧
    ∃ c₀, !subst1Graph c₀ nd b₂ ∧ ∃ c₁, !consequentGraph c₁ c₀ ∧
    ∃ d₁, !specializeCtxGraph d₁ Γ ↑body ne seed ∧
    ∃ d₂, !specializeCtxGraph d₂ Γ b₂ nd d₁ ∧
    ∃ d₃, !applyCtxGraph d₃ Γ c₀ d₂ a ∧ !applyCtxGraph o Γ c₁ d₃ t”

private theorem specialize_eval (v : Fin 5 → V) :
    specializeCtxGraph.val.Evalb v ↔ v 0 = specializeCtxValue (v 1) (v 2) (v 3) (v 4) := by
  have hv : ![v 0, v 1, v 2, v 3, v 4] = v := by
    funext i
    fin_cases i <;> simp
  rw [← hv]
  exact specializeCtxGraph_iff _ _ _ _ _

private theorem apply_eval (v : Fin 5 → V) :
    applyCtxGraph.val.Evalb v ↔ v 0 = applyCtxValue (v 1) (v 2) (v 3) (v 4) := by
  have hv : ![v 0, v 1, v 2, v 3, v 4] = v := by
    funext i
    fin_cases i <;> simp
  rw [← hv]
  exact applyCtxGraph_iff _ _ _ _ _

theorem closureGraph_iff (body : ℕ) (o seed Γ a t e d : V) :
    (closureGraph body).val.Evalb ![o, seed, Γ, a, t, e, d] ↔
      o = closureValue body seed Γ a t e d := by
  simp [closureGraph, closureValue, numeralTermCodeGraph_iff, subst1Graph_iff,
    consequentGraph_iff, specialize_eval, apply_eval, Tarski.Structure.numeral_eq_numeral]

theorem closureGraph_total (body : ℕ) (seed Γ a t e d : V) :
    ∃ o : V, (closureGraph body).val.Evalb ![o, seed, Γ, a, t, e, d] :=
  ⟨closureValue body seed Γ a t e d, (closureGraph_iff body _ _ _ _ _ _ _).mpr rfl⟩

theorem closureGraph_functional (body : ℕ) {o o' seed Γ a t e d : V}
    (ho : (closureGraph body).val.Evalb ![o, seed, Γ, a, t, e, d])
    (ho' : (closureGraph body).val.Evalb ![o', seed, Γ, a, t, e, d]) : o = o' :=
  ((closureGraph_iff body _ _ _ _ _ _ _).mp ho).trans
    ((closureGraph_iff body _ _ _ _ _ _ _).mp ho').symm

end Internal

theorem pointwiseValue_nat (body seed Γ a t m p e u d : ℕ) :
    pointwiseValue body seed Γ a t m p e u d = pointwiseCtx body seed Γ a t m p e u d :=
  extractValue_nat body seed Γ a t m p e u d

theorem pointwiseGraph_nat_iff (body o seed Γ a t m p e u d : ℕ) :
    (pointwiseGraph body).val.Evalb ![o, seed, Γ, a, t, m, p, e, u, d] ↔
      o = pointwiseCtx body seed Γ a t m p e u d :=
  extractGraph_nat_iff body o seed Γ a t m p e u d

theorem closureValue_nat (body seed Γ a t e d : ℕ) :
    closureValue body seed Γ a t e d = closureCtx body seed Γ a t e d := by
  simp only [closureValue, numeral_eq_natCast_app, natCast_nat,
    numeralTermCodeValue_nat, subst1Value_nat, allBodyValue_nat,
    consequentValue_nat, specializeCtxValue_nat, applyCtxValue_nat]
  rfl

theorem closureGraph_nat_iff (body o seed Γ a t e d : ℕ) :
    (closureGraph body).val.Evalb ![o, seed, Γ, a, t, e, d] ↔
      o = closureCtx body seed Γ a t e d := by
  rw [closureGraph_iff, closureValue_nat]

end FailureOfComposition.NativeMembershipAssembly
