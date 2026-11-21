/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ArithmeticIndexedPAEnumerationSimple
public import CategoricalEssentialIncompleteness.V46ArithmeticIndexedPAEnumerationClosure

/-! # Literal induction-matrix enumeration through substitution graphs -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates

namespace CategoricalEssentialIncompleteness.V46.ArithmeticIndexedPAEnumeration
open NamedArithmeticSignature ArithmeticNamedAxiomComparison ConcreteNamedSubstitution

def successorExpression : Words.Expr := Words.add (Words.varWord (.slot 0)) Words.one
def inductionExpression : Words.Expr := Words.inductionMatrix (.slot 0) (.slot 1) (.slot 2) (.slot 3)

def inductionCarrier : Carrier :=
  let Z := Words.graph Words.zero
  let S := Words.graph successorExpression
  let I := Words.graph inductionExpression
  let F := formulaCarrier
  let R := substitutionResultGraph variableSymbols functionSymbols relationSymbols bound
  let X := Words.slotGraph 0
  let B := Words.slotGraph 1
  let Z0 := Words.slotGraph 2
  let ZS := Words.slotGraph 3
  .mkSigma “out. ∃ env x body base step zero succ rb rs,
    !X.val x env ∧ !B.val body env ∧ !Z0.val base env ∧ !ZS.val step env ∧
    !F.val body ∧ !Z.val zero env ∧ !S.val succ env ∧
    !pairDef.val rb base 1 ∧ !R.val rb x zero body ∧
    !pairDef.val rs step 1 ∧ !R.val rs x succ body ∧ !I.val out env”

section Models
variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝚺 1 :=
  models_of_subtheory (U := 𝗣𝗔) inferInstance
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 :=
  models_of_subtheory (U := 𝗜𝚺 1) inferInstance

@[simp] theorem inductionCarrier_eval (out : M) :
    inductionCarrier.val.Evalb ![out] ↔ ∃ env : M,
      formulaCarrier.val.Evalb ![Words.value (.slot 1) env] ∧
      ok (Words.value (.slot 2) env) = substitutionResult variableSymbols functionSymbols relationSymbols bound
        (Words.value (.slot 0) env) (Words.value Words.zero env) (Words.value (.slot 1) env) ∧
      ok (Words.value (.slot 3) env) = substitutionResult variableSymbols functionSymbols relationSymbols bound
        (Words.value (.slot 0) env) (Words.value successorExpression env) (Words.value (.slot 1) env) ∧
      out = Words.value inductionExpression env := by
  simp [inductionCarrier,ok]

end Models

theorem successor_value (env : ℕ) :
    Words.value successorExpression env =
      termCode (NamedArithmeticSignature.add (.var (Words.value (.slot 0) env)) NamedArithmeticSignature.one) :=
  Words.add_value _ _ env _ _ (Words.variable_value (.slot 0) env) (Words.one_value env)

theorem optionCode_success {φ : Formula} {x word : ℕ} {t : Term}
    (h : NamedPostfixEncoding.optionCode (φ.substitute x t) = ok word) :
    ∃ ψ : Formula, φ.substitute x t = some ψ ∧ formulaCode ψ = word := by
  cases hs : φ.substitute x t with
  | none =>
      have hp := congrArg (fun n : ℕ => π₂ n) h
      simp [hs,NamedPostfixEncoding.optionCode,ok,pi₂_zero] at hp
  | some ψ =>
      refine ⟨ψ,rfl,?_⟩
      have hp := congrArg (fun n : ℕ => π₁ n) h
      simpa [hs,NamedPostfixEncoding.optionCode,ok] using hp

theorem inductionCarrier_seed (out : ℕ) (h : inductionCarrier.val.Evalb ![out]) :
    ∃ ψ : Formula, PASeed ψ ∧ formulaCode ψ = out := by
  obtain ⟨env,hbody,h0,hs,hout⟩ := (inductionCarrier_eval _).mp h
  obtain ⟨φ,hφ⟩ := (NamedPostfixEncoding.standard_codes_surjective
    functionSymbols relationSymbols bound).2 _ hbody
  let x := Words.value (.slot 0) env
  have hz : NamedPostfixEncoding.optionCode (φ.substitute x NamedArithmeticSignature.zero) =
      ok (Words.value (.slot 2) env) := by
    rw [← NamedPostfixEncoding.substitutionResult_formulaCode φ NamedArithmeticSignature.zero x]
    have hw : NamedPostfixEncoding.termCode NamedArithmeticSignature.zero = Words.value Words.zero env :=
      (Words.zero_value env).symm
    rw [hφ,hw]
    exact h0.symm
  have hsuc : NamedPostfixEncoding.optionCode
      (φ.substitute x (NamedArithmeticSignature.add (.var x) NamedArithmeticSignature.one)) =
        ok (Words.value (.slot 3) env) := by
    rw [← NamedPostfixEncoding.substitutionResult_formulaCode φ
      (NamedArithmeticSignature.add (.var x) NamedArithmeticSignature.one) x]
    have hw : NamedPostfixEncoding.termCode
        (NamedArithmeticSignature.add (.var x) NamedArithmeticSignature.one) =
          Words.value successorExpression env := (successor_value env).symm
    rw [hφ,hw]
    exact hs.symm
  obtain ⟨φ0,s0,c0⟩ := optionCode_success hz
  obtain ⟨φs,ss,cs⟩ := optionCode_success hsuc
  have hf0 : φ.FreeFor x NamedArithmeticSignature.zero :=
    (NamedFiniteSyntax.Formula.substitute_isSome_iff _ _ _).mp (by simp [s0])
  have hfs : φ.FreeFor x (NamedArithmeticSignature.add (.var x) NamedArithmeticSignature.one) :=
    (NamedFiniteSyntax.Formula.substitute_isSome_iff _ _ _).mp (by simp [ss])
  have hc := Words.inductionMatrix_value (.slot 0) (.slot 1) (.slot 2) (.slot 3)
    env x φ φ0 φs rfl hφ.symm c0.symm cs.symm
  exact ⟨inductionMatrix x φ φ0 φs,PASeed.«induction» x φ φ0 φs hf0 hfs s0 ss,
    hc.symm.trans hout.symm⟩

def inductionEnvironment (x body base step : ℕ) : ℕ :=
  Arithmetic.pair x (Arithmetic.pair body (Arithmetic.pair base (Arithmetic.pair step 0)))

@[simp] theorem inductionEnvironment_slot_zero (x body base step : ℕ) :
    Words.slotValue 0 (inductionEnvironment x body base step) = x := by
  simp [Words.slotValue,inductionEnvironment]

@[simp] theorem inductionEnvironment_slot_one (x body base step : ℕ) :
    Words.slotValue 1 (inductionEnvironment x body base step) = body := by
  simp [Words.slotValue,inductionEnvironment]

@[simp] theorem inductionEnvironment_slot_two (x body base step : ℕ) :
    Words.slotValue 2 (inductionEnvironment x body base step) = base := by
  simp [Words.slotValue,inductionEnvironment]

@[simp] theorem inductionEnvironment_slot_three (x body base step : ℕ) :
    Words.slotValue 3 (inductionEnvironment x body base step) = step := by
  simp [Words.slotValue,inductionEnvironment]

@[simp] theorem inductionEnvironment_zero (x body base step : ℕ) :
    Words.value (.slot 0) (inductionEnvironment x body base step) = x := by
  exact inductionEnvironment_slot_zero x body base step
@[simp] theorem inductionEnvironment_one (x body base step : ℕ) :
    Words.value (.slot 1) (inductionEnvironment x body base step) = body := by
  exact inductionEnvironment_slot_one x body base step
@[simp] theorem inductionEnvironment_two (x body base step : ℕ) :
    Words.value (.slot 2) (inductionEnvironment x body base step) = base := by
  exact inductionEnvironment_slot_two x body base step
@[simp] theorem inductionEnvironment_three (x body base step : ℕ) :
    Words.value (.slot 3) (inductionEnvironment x body base step) = step := by
  exact inductionEnvironment_slot_three x body base step

theorem inductionCarrier_of_native {ψ : Formula} (h : NativeInduction ψ) :
    inductionCarrier.val.Evalb ![formulaCode ψ] := by
  obtain ⟨x,body,base,step,rfl,_,_,s0,ss⟩ := h
  let env := inductionEnvironment x (formulaCode body) (formulaCode base) (formulaCode step)
  have hc := Words.inductionMatrix_value (.slot 0) (.slot 1) (.slot 2) (.slot 3)
    env x body base step (by simp [env]) (by simp [env]) (by simp [env]) (by simp [env])
  have hz := NamedPostfixEncoding.substitutionResult_formulaCode body NamedArithmeticSignature.zero x
  have hs := NamedPostfixEncoding.substitutionResult_formulaCode body
    (NamedArithmeticSignature.add (.var x) NamedArithmeticSignature.one) x
  simp only [s0,NamedPostfixEncoding.optionCode_some] at hz
  simp only [ss,NamedPostfixEncoding.optionCode_some] at hs
  apply (inductionCarrier_eval _).mpr
  refine ⟨env,?_,?_,?_,hc.symm⟩
  · simpa only [env,inductionEnvironment_one] using NamedPostfixEncoding.formulaCode_member body
  · simpa only [env,inductionEnvironment_zero,inductionEnvironment_one,inductionEnvironment_two,
      Words.zero_value,ok] using hz.symm
  · simpa only [successor_value,env,inductionEnvironment_zero,inductionEnvironment_one,
      inductionEnvironment_three,ok] using hs.symm

def seedCarrier : Carrier := .mkSigma “out. !simpleCarrier.val out ∨ !inductionCarrier.val out”

theorem seedCarrier_standard (out : ℕ) :
    seedCarrier.val.Evalb ![out] ↔ ∃ ψ : Formula, PASeed ψ ∧ formulaCode ψ = out := by
  constructor
  · intro h
    have hor : simpleCarrier.val.Evalb ![out] ∨ inductionCarrier.val.Evalb ![out] := by
      simpa [seedCarrier] using h
    exact hor.elim (simpleCarrier_seed out) (inductionCarrier_seed out)
  · rintro ⟨ψ,hψ,rfl⟩
    rcases seed_cases hψ with ⟨k,env,hfresh,he⟩ | hi
    · have hc : simpleCarrier.val.Evalb ![formulaCode ψ] :=
        (simpleCarrier_standard _).mpr ⟨k,env,hfresh,congrArg formulaCode he.symm⟩
      simpa [seedCarrier] using (Or.inl hc :
        simpleCarrier.val.Evalb ![formulaCode ψ] ∨ inductionCarrier.val.Evalb ![formulaCode ψ])
    · have hc := inductionCarrier_of_native hi
      simpa [seedCarrier] using (Or.inr hc :
        simpleCarrier.val.Evalb ![formulaCode ψ] ∨ inductionCarrier.val.Evalb ![formulaCode ψ])

end CategoricalEssentialIncompleteness.V46.ArithmeticIndexedPAEnumeration
