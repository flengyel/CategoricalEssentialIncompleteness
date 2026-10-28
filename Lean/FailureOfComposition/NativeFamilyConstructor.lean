/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import FailureOfComposition.NativeEqualityTransport

/-!
# An executable family-proof constructor

The numerical parameter `body` is supplied syntax: the body of the outer
universal quantifier in the extraction seed. It is not computed from a coded
object or a chosen representative. The nine arguments are packed in three
triples `(((seed,Gamma),e),(((m,pH),pK),((u,y),y')))`. Three specializations are followed
by four context-preserving applications of modus ponens. Syntax projections
are total even on malformed inputs; correctness requires the supplied proofs.
-/

set_option autoImplicit false

open Encodable FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic

namespace FailureOfComposition.NativeFamilyExtraction

open FFL.FirstOrder.Arithmetic.Bootstrapping
open FailureOfComposition.NativeContextMP
open FailureOfComposition.NativeContextSpecialization
open FailureOfComposition.NativeSubstitution
open FailureOfComposition.NativeEqualityTransport

def allBodyCode (a : ℕ) : ℕ := (a - 1).unpair.2

def consequentCode (a : ℕ) : ℕ := ((a - 1).unpair.2).unpair.2

def antecedentCode (a : ℕ) : ℕ := formulaNegTotalCode (((a - 1).unpair.2).unpair.1)

def applyCtxCode (Γ c e p : ℕ) : ℕ :=
  mpCtx Γ (antecedentCode c) (consequentCode c) e p

def extractCtx (body seed Γ e m pH pK u y r : ℕ) : ℕ :=
  let nu := numeralTermCode u
  let ny := numeralTermCode y
  let nr := numeralTermCode r
  let b₂ := allBodyCode (subst1Code nu body)
  let b₃ := allBodyCode (subst1Code ny b₂)
  let c₀ := subst1Code nr b₃
  let c₁ := consequentCode c₀
  let c₂ := consequentCode c₁
  let c₃ := consequentCode c₂
  let d₁ := specializeCtx Γ body nu seed
  let d₂ := specializeCtx Γ b₂ ny d₁
  let d₃ := specializeCtx Γ b₃ nr d₂
  let d₄ := applyCtxCode Γ c₀ d₃ e
  let d₅ := applyCtxCode Γ c₁ d₄ m
  let d₆ := applyCtxCode Γ c₂ d₅ pH
  applyCtxCode Γ c₃ d₆ pK

abbrev ExtractArgs := ((ℕ × ℕ) × ℕ) × (((ℕ × ℕ) × ℕ) × ((ℕ × ℕ) × ℕ))

def extractCtxPacked (body : ℕ) (z : ExtractArgs) : ℕ :=
  extractCtx body z.1.1.1 z.1.1.2 z.1.2
    z.2.1.1.1 z.2.1.1.2 z.2.1.2 z.2.2.1.1 z.2.2.1.2 z.2.2.2


section Internal

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]

noncomputable def consequentValue (c : V) : V := π₂ (sndIdx c)

noncomputable def antecedentValue (c : V) : V := guardedNegValue (π₁ (sndIdx c))

noncomputable def consequentGraph : 𝚺₁.Semisentence 2 := .mkSigma
  “a c. ∃ t, !sndIdxDef t c ∧ !pi₂Def a t”

noncomputable def antecedentGraph : 𝚺₁.Semisentence 2 := .mkSigma
  “a c. ∃ t, !sndIdxDef t c ∧ ∃ n, !pi₁Def n t ∧ !guardedNegGraph a n”

theorem consequentGraph_iff (a c : V) :
    consequentGraph.val.Evalb ![a, c] ↔ a = consequentValue c := by
  simp [consequentGraph, consequentValue]

theorem antecedentGraph_iff (a c : V) :
    antecedentGraph.val.Evalb ![a, c] ↔ a = antecedentValue c := by
  simp [antecedentGraph, antecedentValue, guardedNegGraph_iff]

noncomputable def applyCtxValue (Γ c e p : V) : V :=
  mpCtxValue Γ (antecedentValue c) (consequentValue c) e p

noncomputable def applyCtxGraph : 𝚺₁.Semisentence 5 := .mkSigma
  “o Γ c e p. ∃ a, !antecedentGraph a c ∧
    ∃ b, !consequentGraph b c ∧ !mpCtxGraph o Γ a b e p”

private theorem mpCtxGraph_eval (v : Fin 6 → V) :
    mpCtxGraph.val.Evalb v ↔ v 0 = mpCtxValue (v 1) (v 2) (v 3) (v 4) (v 5) := by
  have hv : ![v 0, v 1, v 2, v 3, v 4, v 5] = v := by
    funext i
    fin_cases i <;> simp
  rw [← hv]
  exact mpCtxGraph_iff _ _ _ _ _ _

theorem applyCtxGraph_iff (o Γ c e p : V) :
    applyCtxGraph.val.Evalb ![o, Γ, c, e, p] ↔ o = applyCtxValue Γ c e p := by
  simp [applyCtxGraph, applyCtxValue, antecedentGraph_iff, consequentGraph_iff, mpCtxGraph_eval]

private theorem specializeCtxGraph_eval (v : Fin 5 → V) :
    specializeCtxGraph.val.Evalb v ↔ v 0 = specializeCtxValue (v 1) (v 2) (v 3) (v 4) := by
  have hv : ![v 0, v 1, v 2, v 3, v 4] = v := by
    funext i
    fin_cases i <;> simp
  rw [← hv]
  exact specializeCtxGraph_iff _ _ _ _ _

private theorem applyCtxGraph_eval (v : Fin 5 → V) :
    applyCtxGraph.val.Evalb v ↔ v 0 = applyCtxValue (v 1) (v 2) (v 3) (v 4) := by
  have hv : ![v 0, v 1, v 2, v 3, v 4] = v := by
    funext i
    fin_cases i <;> simp
  rw [← hv]
  exact applyCtxGraph_iff _ _ _ _ _

noncomputable def extractValue (body : ℕ) (seed Γ e m pH pK u y r : V) : V :=
  let b₁ := ORingStructure.numeral body
  let nu := Arithmetic.numeral u
  let ny := Arithmetic.numeral y
  let nr := Arithmetic.numeral r
  let b₂ := sndIdx (subst1Value nu b₁)
  let b₃ := sndIdx (subst1Value ny b₂)
  let c₀ := subst1Value nr b₃
  let c₁ := consequentValue c₀
  let c₂ := consequentValue c₁
  let c₃ := consequentValue c₂
  let d₁ := specializeCtxValue Γ b₁ nu seed
  let d₂ := specializeCtxValue Γ b₂ ny d₁
  let d₃ := specializeCtxValue Γ b₃ nr d₂
  let d₄ := applyCtxValue Γ c₀ d₃ e
  let d₅ := applyCtxValue Γ c₁ d₄ m
  let d₆ := applyCtxValue Γ c₂ d₅ pH
  applyCtxValue Γ c₃ d₆ pK

/-- Output first, followed by the nine numerical arguments in packed order. -/
noncomputable def extractGraph (body : ℕ) : 𝚺₁.Semisentence 10 := .mkSigma
  “o seed Γ e m pH pK u y r.
    ∃ nu, !numeralTermCodeGraph nu u ∧
    ∃ ny, !numeralTermCodeGraph ny y ∧
    ∃ nr, !numeralTermCodeGraph nr r ∧
    ∃ s₁, !subst1Graph s₁ nu ↑body ∧ ∃ b₂, !sndIdxDef b₂ s₁ ∧
    ∃ s₂, !subst1Graph s₂ ny b₂ ∧ ∃ b₃, !sndIdxDef b₃ s₂ ∧
    ∃ c₀, !subst1Graph c₀ nr b₃ ∧
    ∃ c₁, !consequentGraph c₁ c₀ ∧
    ∃ c₂, !consequentGraph c₂ c₁ ∧
    ∃ c₃, !consequentGraph c₃ c₂ ∧
    ∃ d₁, !specializeCtxGraph d₁ Γ ↑body nu seed ∧
    ∃ d₂, !specializeCtxGraph d₂ Γ b₂ ny d₁ ∧
    ∃ d₃, !specializeCtxGraph d₃ Γ b₃ nr d₂ ∧
    ∃ d₄, !applyCtxGraph d₄ Γ c₀ d₃ e ∧
    ∃ d₅, !applyCtxGraph d₅ Γ c₁ d₄ m ∧
    ∃ d₆, !applyCtxGraph d₆ Γ c₂ d₅ pH ∧
      !applyCtxGraph o Γ c₃ d₆ pK”

theorem extractGraph_iff (body : ℕ) (o seed Γ e m pH pK u y r : V) :
    (extractGraph body).val.Evalb ![o, seed, Γ, e, m, pH, pK, u, y, r] ↔
      o = extractValue body seed Γ e m pH pK u y r := by
  simp [extractGraph, extractValue, numeralTermCodeGraph_iff, subst1Graph_iff,
    consequentGraph_iff, specializeCtxGraph_eval, applyCtxGraph_eval,
    Tarski.Structure.numeral_eq_numeral]

theorem extractGraph_total (body : ℕ) (seed Γ e m pH pK u y r : V) :
    ∃ o : V, (extractGraph body).val.Evalb ![o, seed, Γ, e, m, pH, pK, u, y, r] :=
  ⟨extractValue body seed Γ e m pH pK u y r, (extractGraph_iff body _ _ _ _ _ _ _ _ _ _).mpr rfl⟩

theorem extractGraph_functional (body : ℕ) {o o' seed Γ e m pH pK u y r : V}
    (ho : (extractGraph body).val.Evalb ![o, seed, Γ, e, m, pH, pK, u, y, r])
    (ho' : (extractGraph body).val.Evalb ![o', seed, Γ, e, m, pH, pK, u, y, r]) : o = o' :=
  ((extractGraph_iff body _ _ _ _ _ _ _ _ _ _).mp ho).trans
    ((extractGraph_iff body _ _ _ _ _ _ _ _ _ _).mp ho').symm

theorem allBodyValue_all (a : V) : sndIdx (^∀ a) = a := by
  simp [sndIdx, qqAll]

theorem consequentValue_imp (a b : V) : consequentValue (imp ℒₒᵣ a b) = b := by
  simp [consequentValue, sndIdx, imp, qqOr]

theorem antecedentValue_imp {a : V} (ha : IsFormula ℒₒᵣ a) (b : V) :
    antecedentValue (imp ℒₒᵣ a b) = a := by
  simp [antecedentValue, sndIdx, imp, qqOr, guardedNegValue_eq_neg ha.neg,
    ha.isUFormula.neg_neg]

end Internal

end FailureOfComposition.NativeFamilyExtraction
