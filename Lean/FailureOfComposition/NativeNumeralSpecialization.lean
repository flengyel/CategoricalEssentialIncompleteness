/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import FailureOfComposition.NativeNumeralSeeds

/-!
# Three and four operational numeral specializations

The step seeds require three or four successive specializations. Each
operation uses the accepted context-preserving constructor and obtains the
next body by the total body projection. The formulas and proofs are kept
separate: the instance functions compute the final sentence, while the
specialization functions compute its derivation tree. All supplied numerical
codes, including malformed codes, have a specified output.
-/

@[expose] public section

set_option autoImplicit false

open Encodable FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic

namespace FailureOfComposition.NativeNumeralArithmetic

open FFL.FirstOrder.Arithmetic.Bootstrapping
open FailureOfComposition.NativeContextMP
open FailureOfComposition.NativeContextSpecialization
open FailureOfComposition.NativeSubstitution
open FailureOfComposition.NativeEqualityTransport
open FailureOfComposition.NativeFamilyExtraction

def nextBodyCode (body x : ℕ) : ℕ := allBodyCode (subst1Code (numeralTermCode x) body)

def instance3Code (body x y z : ℕ) : ℕ :=
  subst1Code (numeralTermCode z) (nextBodyCode (nextBodyCode body x) y)

def specialize3Code (body Γ seed x y z : ℕ) : ℕ :=
  let b₂ := nextBodyCode body x
  let b₃ := nextBodyCode b₂ y
  let d₁ := specializeCtx Γ body (numeralTermCode x) seed
  let d₂ := specializeCtx Γ b₂ (numeralTermCode y) d₁
  specializeCtx Γ b₃ (numeralTermCode z) d₂

def instance4Code (body x y z w : ℕ) : ℕ :=
  instance3Code (nextBodyCode body x) y z w

def specialize4Code (body Γ seed x y z w : ℕ) : ℕ :=
  specialize3Code (nextBodyCode body x) Γ
    (specializeCtx Γ body (numeralTermCode x) seed) y z w

set_option backward.isDefEq.respectTransparency false in
theorem primrec_specialize {X : Type*} [Primcodable X]
    {g b t d : X → ℕ} (hg : Primrec g) (hb : Primrec b)
    (ht : Primrec t) (hd : Primrec d) :
    Primrec (fun x => specializeCtx (g x) (b x) (t x) (d x)) := by
  exact (primrec_specializeCtxPacked.comp (((hg.pair hb).pair ht).pair hd)).of_eq fun _ => rfl

set_option backward.isDefEq.respectTransparency false in
theorem primrec_apply {X : Type*} [Primcodable X]
    {g c e p : X → ℕ} (hg : Primrec g) (hc : Primrec c)
    (he : Primrec e) (hp : Primrec p) :
    Primrec (fun x => applyCtxCode (g x) (c x) (e x) (p x)) := by
  exact (primrec_mpCtxPacked.comp ((((hg.pair (primrec_antecedentCode.comp hc)).pair
    (primrec_consequentCode.comp hc)).pair he).pair hp)).of_eq fun _ => rfl

theorem primrec_nextBody {X : Type*} [Primcodable X] {b x : X → ℕ}
    (hb : Primrec b) (hx : Primrec x) : Primrec (fun u => nextBodyCode (b u) (x u)) :=
  primrec_allBodyCode.comp (primrec₂_subst1Code.comp (primrec_numeralTermCode.comp hx) hb)

theorem primrec_instance3 {X : Type*} [Primcodable X] {b x y z : X → ℕ}
    (hb : Primrec b) (hx : Primrec x) (hy : Primrec y) (hz : Primrec z) :
    Primrec (fun u => instance3Code (b u) (x u) (y u) (z u)) :=
  primrec₂_subst1Code.comp (primrec_numeralTermCode.comp hz)
    (primrec_nextBody (primrec_nextBody hb hx) hy)

theorem primrec_specialize3 {X : Type*} [Primcodable X] {b g s x y z : X → ℕ}
    (hb : Primrec b) (hg : Primrec g) (hs : Primrec s)
    (hx : Primrec x) (hy : Primrec y) (hz : Primrec z) :
    Primrec (fun u => specialize3Code (b u) (g u) (s u) (x u) (y u) (z u)) := by
  have hb₂ := primrec_nextBody hb hx
  have hd₁ := primrec_specialize hg hb (primrec_numeralTermCode.comp hx) hs
  have hd₂ := primrec_specialize hg hb₂ (primrec_numeralTermCode.comp hy) hd₁
  exact primrec_specialize hg (primrec_nextBody hb₂ hy) (primrec_numeralTermCode.comp hz) hd₂

theorem primrec_instance4 {X : Type*} [Primcodable X] {b x y z w : X → ℕ}
    (hb : Primrec b) (hx : Primrec x) (hy : Primrec y) (hz : Primrec z) (hw : Primrec w) :
    Primrec (fun u => instance4Code (b u) (x u) (y u) (z u) (w u)) :=
  primrec_instance3 (primrec_nextBody hb hx) hy hz hw

theorem primrec_specialize4 {X : Type*} [Primcodable X] {b g s x y z w : X → ℕ}
    (hb : Primrec b) (hg : Primrec g) (hs : Primrec s)
    (hx : Primrec x) (hy : Primrec y) (hz : Primrec z) (hw : Primrec w) :
    Primrec (fun u => specialize4Code (b u) (g u) (s u) (x u) (y u) (z u) (w u)) :=
  primrec_specialize3 (primrec_nextBody hb hx) hg
    (primrec_specialize hg hb (primrec_numeralTermCode.comp hx) hs) hy hz hw

section Internal

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]

noncomputable def nextBodyValue (body x : V) : V :=
  sndIdx (subst1Value (Arithmetic.numeral x) body)

noncomputable def instance3Value (body x y z : V) : V :=
  subst1Value (Arithmetic.numeral z) (nextBodyValue (nextBodyValue body x) y)

noncomputable def specialize3Value (body Γ seed x y z : V) : V :=
  let b₂ := nextBodyValue body x
  let b₃ := nextBodyValue b₂ y
  let d₁ := specializeCtxValue Γ body (Arithmetic.numeral x) seed
  let d₂ := specializeCtxValue Γ b₂ (Arithmetic.numeral y) d₁
  specializeCtxValue Γ b₃ (Arithmetic.numeral z) d₂

noncomputable def instance4Value (body x y z w : V) : V :=
  instance3Value (nextBodyValue body x) y z w

noncomputable def specialize4Value (body Γ seed x y z w : V) : V :=
  specialize3Value (nextBodyValue body x) Γ
    (specializeCtxValue Γ body (Arithmetic.numeral x) seed) y z w

noncomputable def nextBodyGraph : 𝚺₁.Semisentence 3 := .mkSigma
  “b body x. ∃ nx, !numeralTermCodeGraph nx x ∧ ∃ s, !subst1Graph s nx body ∧ !sndIdxDef b s”

noncomputable def instance3Graph : 𝚺₁.Semisentence 5 := .mkSigma
  “c body x y z. ∃ b₂, !nextBodyGraph b₂ body x ∧
    ∃ b₃, !nextBodyGraph b₃ b₂ y ∧
    ∃ nz, !numeralTermCodeGraph nz z ∧ !subst1Graph c nz b₃”

noncomputable def specialize3Graph : 𝚺₁.Semisentence 7 := .mkSigma
  “o body Γ seed x y z. ∃ b₂, !nextBodyGraph b₂ body x ∧
    ∃ b₃, !nextBodyGraph b₃ b₂ y ∧
    ∃ nx, !numeralTermCodeGraph nx x ∧
    ∃ ny, !numeralTermCodeGraph ny y ∧
    ∃ nz, !numeralTermCodeGraph nz z ∧
    ∃ d₁, !specializeCtxGraph d₁ Γ body nx seed ∧
    ∃ d₂, !specializeCtxGraph d₂ Γ b₂ ny d₁ ∧ !specializeCtxGraph o Γ b₃ nz d₂”

noncomputable def instance4Graph : 𝚺₁.Semisentence 6 := .mkSigma
  “c body x y z w. ∃ b, !nextBodyGraph b body x ∧ !instance3Graph c b y z w”

noncomputable def specialize4Graph : 𝚺₁.Semisentence 8 := .mkSigma
  “o body Γ seed x y z w. ∃ b, !nextBodyGraph b body x ∧
    ∃ nx, !numeralTermCodeGraph nx x ∧
    ∃ d, !specializeCtxGraph d Γ body nx seed ∧ !specialize3Graph o b Γ d y z w”

@[simp] theorem specializeCtxGraph_eval (v : Fin 5 → V) :
    specializeCtxGraph.val.Evalb v ↔ v 0 = specializeCtxValue (v 1) (v 2) (v 3) (v 4) := by
  have hv : v = ![v 0, v 1, v 2, v 3, v 4] := by ext i; fin_cases i <;> rfl
  rw [hv]
  exact specializeCtxGraph_iff _ _ _ _ _

@[simp] theorem applyCtxGraph_eval (v : Fin 5 → V) :
    applyCtxGraph.val.Evalb v ↔ v 0 = applyCtxValue (v 1) (v 2) (v 3) (v 4) := by
  have hv : v = ![v 0, v 1, v 2, v 3, v 4] := by ext i; fin_cases i <;> rfl
  rw [hv]
  exact applyCtxGraph_iff _ _ _ _ _

@[simp] theorem nextBodyGraph_eval (v : Fin 3 → V) :
    nextBodyGraph.val.Evalb v ↔ v 0 = nextBodyValue (v 1) (v 2) := by
  simp [nextBodyGraph, nextBodyValue, numeralTermCodeGraph_iff, subst1Graph_iff]

@[simp] theorem instance3Graph_eval (v : Fin 5 → V) :
    instance3Graph.val.Evalb v ↔ v 0 = instance3Value (v 1) (v 2) (v 3) (v 4) := by
  simp [instance3Graph, instance3Value, numeralTermCodeGraph_iff, subst1Graph_iff]

@[simp] theorem specialize3Graph_eval (v : Fin 7 → V) :
    specialize3Graph.val.Evalb v ↔
      v 0 = specialize3Value (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) := by
  simp [specialize3Graph, specialize3Value, numeralTermCodeGraph_iff]

@[simp] theorem instance4Graph_eval (v : Fin 6 → V) :
    instance4Graph.val.Evalb v ↔ v 0 = instance4Value (v 1) (v 2) (v 3) (v 4) (v 5) := by
  simp [instance4Graph, instance4Value]

@[simp] theorem specialize4Graph_eval (v : Fin 8 → V) :
    specialize4Graph.val.Evalb v ↔
      v 0 = specialize4Value (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7) := by
  simp [specialize4Graph, specialize4Value, numeralTermCodeGraph_iff]

end Internal

theorem nextBodyValue_nat (body x : ℕ) : nextBodyValue body x = nextBodyCode body x := by
  simp only [nextBodyValue, nextBodyCode, numeralTermCodeValue_nat,
    subst1Value_nat, allBodyValue_nat]

theorem instance3Value_nat (body x y z : ℕ) :
    instance3Value body x y z = instance3Code body x y z := by
  simp only [instance3Value, instance3Code, numeralTermCodeValue_nat,
    subst1Value_nat, nextBodyValue_nat]

theorem specialize3Value_nat (body Γ seed x y z : ℕ) :
    specialize3Value body Γ seed x y z = specialize3Code body Γ seed x y z := by
  simp only [specialize3Value, specialize3Code, nextBodyValue_nat,
    numeralTermCodeValue_nat, specializeCtxValue_nat]

theorem instance4Value_nat (body x y z w : ℕ) :
    instance4Value body x y z w = instance4Code body x y z w := by
  simp only [instance4Value, instance4Code, nextBodyValue_nat, instance3Value_nat]

theorem specialize4Value_nat (body Γ seed x y z w : ℕ) :
    specialize4Value body Γ seed x y z w = specialize4Code body Γ seed x y z w := by
  simp only [specialize4Value, specialize4Code, nextBodyValue_nat, numeralTermCodeValue_nat,
    specializeCtxValue_nat, specialize3Value_nat]

end FailureOfComposition.NativeNumeralArithmetic
