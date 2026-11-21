/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ArithmeticIndexedPAEnumerationTemplates

/-! # The Σ₁ enumeration of the finite arithmetic/order schemes -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates

namespace CategoricalEssentialIncompleteness.V46.ArithmeticIndexedPAEnumeration
open NamedArithmeticSignature ArithmeticNamedAxiomComparison

def guardGraph (k : Fin 17) : Carrier :=
  if k.val = 3 then
    let X := Words.slotGraph 0
    let Y := Words.slotGraph 1
    let Z := Words.slotGraph 2
    .mkSigma “env. ∃ x y z, !X.val x env ∧ !Y.val y env ∧
      !Z.val z env ∧ z ≠ x ∧ z ≠ y”
  else .mkSigma “env. env = env”

def simpleBranch (k : Fin 17) : Carrier :=
  let H := guardGraph k
  let G := Words.graph (simpleTemplate k).expression
  .mkSigma “out. ∃ env, !H.val env ∧ !G.val out env”

def carrierUnion : List Carrier → Carrier
  | [] => .mkSigma “out. 0 = 1”
  | C :: cs =>
      let U := carrierUnion cs
      .mkSigma “out. !C.val out ∨ !U.val out”

def simpleCarrier : Carrier := carrierUnion (List.ofFn simpleBranch)

section Models
variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝚺 1 :=
  models_of_subtheory (U := 𝗣𝗔) inferInstance
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 :=
  models_of_subtheory (U := 𝗜𝚺 1) inferInstance

@[simp] theorem guardGraph_eval (k : Fin 17) (env : M) :
    (guardGraph k).val.Evalb ![env] ↔
      (k.val = 3 → Words.slotValue 2 env ≠ Words.slotValue 0 env ∧ Words.slotValue 2 env ≠ Words.slotValue 1 env) := by
  by_cases hk : k.val = 3 <;> simp [guardGraph,hk]

@[simp] theorem simpleBranch_eval (k : Fin 17) (out : M) :
    (simpleBranch k).val.Evalb ![out] ↔ ∃ env : M,
      (guardGraph k).val.Evalb ![env] ∧
        out = Words.value (simpleTemplate k).expression env := by
  simp [simpleBranch]

@[simp] theorem carrierUnion_eval (cs : List Carrier) (out : M) :
    (carrierUnion cs).val.Evalb ![out] ↔ ∃ C ∈ cs, C.val.Evalb ![out] := by
  induction cs with
  | nil => simp [carrierUnion]
  | cons C cs ih => simp [carrierUnion,ih]

end Models

theorem guardGraph_standard (k : Fin 17) (env : ℕ) :
    (guardGraph k).val.Evalb ![env] ↔ fresh k env := by
  rw [guardGraph_eval]
  rfl

theorem simpleBranch_standard (k : Fin 17) (out : ℕ) :
    (simpleBranch k).val.Evalb ![out] ↔
      ∃ env : ℕ, fresh k env ∧ out = formulaCode ((simpleTemplate k).instantiate env) := by
  rw [simpleBranch_eval]
  simp only [guardGraph_standard,FormulaSchema.expression_code]

theorem simpleCarrier_standard (out : ℕ) :
    simpleCarrier.val.Evalb ![out] ↔ ∃ k : Fin 17, ∃ env : ℕ,
      fresh k env ∧ out = formulaCode ((simpleTemplate k).instantiate env) := by
  rw [simpleCarrier,carrierUnion_eval]
  constructor
  · rintro ⟨C,hC,hout⟩
    obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hC
    obtain ⟨env,hfresh,he⟩ := (simpleBranch_standard k out).mp hout
    exact ⟨k,env,hfresh,he⟩
  · rintro ⟨k,env,hfresh,he⟩
    exact ⟨simpleBranch k,List.mem_ofFn.mpr ⟨k,rfl⟩,
      (simpleBranch_standard k out).mpr ⟨env,hfresh,he⟩⟩

theorem simpleCarrier_seed (out : ℕ) (h : simpleCarrier.val.Evalb ![out]) :
    ∃ φ : Formula, PASeed φ ∧ formulaCode φ = out := by
  obtain ⟨k,env,hfresh,he⟩ := (simpleCarrier_standard out).mp h
  exact ⟨_,simpleTemplate_seed k env hfresh,he.symm⟩

def environment (a b c : ℕ) : ℕ := Arithmetic.pair a (Arithmetic.pair b (Arithmetic.pair c 0))

@[simp] theorem environment_zero (a b c : ℕ) : Words.slotValue 0 (environment a b c) = a := by
  simp [Words.slotValue,environment]
@[simp] theorem environment_one (a b c : ℕ) : Words.slotValue 1 (environment a b c) = b := by
  simp [Words.slotValue,environment]
@[simp] theorem environment_two (a b c : ℕ) : Words.slotValue 2 (environment a b c) = c := by
  simp [Words.slotValue,environment]

def NativeInduction (φ : Formula) : Prop :=
  ∃ x body base step, φ = inductionMatrix x body base step ∧
    body.FreeFor x NamedArithmeticSignature.zero ∧
    body.FreeFor x (NamedArithmeticSignature.add (.var x) NamedArithmeticSignature.one) ∧
    body.substitute x NamedArithmeticSignature.zero = some base ∧
    body.substitute x (NamedArithmeticSignature.add (.var x) NamedArithmeticSignature.one) = some step

/-- This is a constructor-by-constructor classification of the named PASeed inductive
family, not a representation assumption. -/
theorem seed_cases {φ : Formula} (h : PASeed φ) :
    (∃ k : Fin 17, ∃ env : ℕ, fresh k env ∧ (simpleTemplate k).instantiate env = φ) ∨
      NativeInduction φ := by
  cases h with
  | addZero a =>
      left; exact ⟨0,environment a 0 0,by simp [fresh],by simp [simpleTemplate,FormulaSchema.instantiate,TermSchema.instantiate]⟩
  | addAssoc a b c =>
      left; exact ⟨1,environment a b c,by simp [fresh],by simp [simpleTemplate,FormulaSchema.instantiate,TermSchema.instantiate]⟩
  | addComm a b =>
      left; exact ⟨2,environment a b 0,by simp [fresh],by simp [simpleTemplate,FormulaSchema.instantiate,TermSchema.instantiate]⟩
  | addEqOfLt a b c hca hcb =>
      left
      refine ⟨3,environment a b c,by simpa [fresh] using And.intro hca hcb,?_⟩
      simp [simpleTemplate,FormulaSchema.instantiate,FormulaSchema.existential,TermSchema.instantiate,
        ArithmeticNamedTranslation.existential]
  | zeroLe a =>
      left; refine ⟨4,environment a 0 0,by simp [fresh],?_⟩
      simp [simpleTemplate,FormulaSchema.instantiate,FormulaSchema.le,FormulaSchema.disjunction,
        TermSchema.instantiate,ArithmeticNamedAxiomComparison.le,ArithmeticNamedTranslation.disjunction]
  | zeroLtOne =>
      left; exact ⟨5,environment 0 0 0,by simp [fresh],by simp [simpleTemplate,FormulaSchema.instantiate,TermSchema.instantiate]⟩
  | oneLeOfZeroLt a =>
      left; refine ⟨6,environment a 0 0,by simp [fresh],?_⟩
      simp [simpleTemplate,FormulaSchema.instantiate,FormulaSchema.le,FormulaSchema.disjunction,
        TermSchema.instantiate,ArithmeticNamedAxiomComparison.le,ArithmeticNamedTranslation.disjunction]
  | addLtAdd a b c =>
      left; exact ⟨7,environment a b c,by simp [fresh],by simp [simpleTemplate,FormulaSchema.instantiate,TermSchema.instantiate]⟩
  | mulZero a =>
      left; exact ⟨8,environment a 0 0,by simp [fresh],by simp [simpleTemplate,FormulaSchema.instantiate,TermSchema.instantiate]⟩
  | mulOne a =>
      left; exact ⟨9,environment a 0 0,by simp [fresh],by simp [simpleTemplate,FormulaSchema.instantiate,TermSchema.instantiate]⟩
  | mulAssoc a b c =>
      left; exact ⟨10,environment a b c,by simp [fresh],by simp [simpleTemplate,FormulaSchema.instantiate,TermSchema.instantiate]⟩
  | mulComm a b =>
      left; exact ⟨11,environment a b 0,by simp [fresh],by simp [simpleTemplate,FormulaSchema.instantiate,TermSchema.instantiate]⟩
  | mulLtMul a b c =>
      left; refine ⟨12,environment a b c,by simp [fresh],?_⟩
      simp [simpleTemplate,FormulaSchema.instantiate,FormulaSchema.conjunction,
        TermSchema.instantiate,ArithmeticNamedTranslation.conjunction]
  | distr a b c =>
      left; exact ⟨13,environment a b c,by simp [fresh],by simp [simpleTemplate,FormulaSchema.instantiate,TermSchema.instantiate]⟩
  | ltIrrefl a =>
      left; exact ⟨14,environment a 0 0,by simp [fresh],by simp [simpleTemplate,FormulaSchema.instantiate,TermSchema.instantiate]⟩
  | ltTrans a b c =>
      left; refine ⟨15,environment a b c,by simp [fresh],?_⟩
      simp [simpleTemplate,FormulaSchema.instantiate,FormulaSchema.conjunction,
        TermSchema.instantiate,ArithmeticNamedTranslation.conjunction]
  | ltTri a b =>
      left; refine ⟨16,environment a b 0,by simp [fresh],?_⟩
      simp [simpleTemplate,FormulaSchema.instantiate,FormulaSchema.disjunction,
        TermSchema.instantiate,ArithmeticNamedTranslation.disjunction]
  | «induction» x body base step h0 hs s0 ss =>
      exact Or.inr ⟨x,body,base,step,rfl,h0,hs,s0,ss⟩

end CategoricalEssentialIncompleteness.V46.ArithmeticIndexedPAEnumeration
