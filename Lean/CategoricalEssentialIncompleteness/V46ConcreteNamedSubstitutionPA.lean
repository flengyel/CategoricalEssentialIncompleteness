/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ConcreteNamedSubstitutionAlgorithmTyped

/-! Explicit PA-proof statements for the numerical realization. These
proofs use all-PA-model numerical lemmas, rather than the totality of any
arbitrary operation graph in a stronger theory T. -/

@[expose] public section
noncomputable section
local instance primitiveNamedPADecidableEqNat : DecidableEq ℕ := Classical.decEq ℕ
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates

namespace CategoricalEssentialIncompleteness.V46.ConcreteNamedSubstitution
open SyntacticSyntax SyntacticSyntax.Coding
variable (V : Carrier) (σ π : ℕ → Carrier) (d : ℕ)

def freeVariablesPreservationSentence (formula : Bool) : ArithmeticSentence :=
  let C := Postfix.carrier formula (SyntaxPolynomial.termExpression V σ d) (SyntaxPolynomial.formulaExpression V π d)
  let L := SyntacticLists.listCarrier V
  let F := freeVariablesGraph V σ π d
  “∀ word out, !C.val word → !F.val out word → !L.val out”

def substitutionTotalSentence : ArithmeticSentence :=
  let G := substitutionPayloadGraph V σ π d
  “∀ x replacement word, ∃! out, !G.val out x replacement word”

def substitutionPreservationSentence (formula : Bool) : ArithmeticSentence :=
  let Tm := Postfix.carrier false (SyntaxPolynomial.termExpression V σ d) (SyntaxPolynomial.formulaExpression V π d)
  let C := Postfix.carrier formula (SyntaxPolynomial.termExpression V σ d) (SyntaxPolynomial.formulaExpression V π d)
  let Q := if formula then formulaPayloadCarrier V σ π d else termPayloadCarrier V σ π d
  let G := substitutionPayloadGraph V σ π d
  “∀ x replacement word out, !V.val x → !Tm.val replacement → !C.val word →
    !G.val out x replacement word → !Q.val out”

def freeForSuccessSentence : ArithmeticSentence :=
  let Tm := Postfix.carrier false (SyntaxPolynomial.termExpression V σ d) (SyntaxPolynomial.formulaExpression V π d)
  let Fm := Postfix.carrier true (SyntaxPolynomial.termExpression V σ d) (SyntaxPolynomial.formulaExpression V π d)
  let R := substitutionResultGraph V σ π d
  let A := substitutionFreeForGraph V σ π d
  “∀ x replacement word res ff, !V.val x → !Tm.val replacement → !Fm.val word →
    !R.val res x replacement word → !A.val ff x replacement word →
    (ff = 1 ↔ ∃ new, !Fm.val new ∧ !pairDef.val res new 1)”

section Models
variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

@[simp] theorem freeVariablesPreservationSentence_eval (formula : Bool) :
    (freeVariablesPreservationSentence V σ π d formula).Evalb (M := M) ![] ↔
      ∀ word out : M,
        (Postfix.carrier formula (SyntaxPolynomial.termExpression V σ d) (SyntaxPolynomial.formulaExpression V π d)).val.Evalb ![word] →
        (freeVariablesGraph V σ π d).val.Evalb ![out,word] →
        (SyntacticLists.listCarrier V).val.Evalb ![out] := by
  simp [freeVariablesPreservationSentence]

@[simp] theorem substitutionTotalSentence_eval :
    (substitutionTotalSentence V σ π d).Evalb (M := M) ![] ↔
      ∀ x replacement word : M,∃! out : M,
        (substitutionPayloadGraph V σ π d).val.Evalb ![out,x,replacement,word] := by
  simp [substitutionTotalSentence]

@[simp] theorem substitutionPreservationSentence_eval (formula : Bool) :
    (substitutionPreservationSentence V σ π d formula).Evalb (M := M) ![] ↔
      ∀ x replacement word out : M,V.val.Evalb ![x] →
        (Postfix.carrier false (SyntaxPolynomial.termExpression V σ d) (SyntaxPolynomial.formulaExpression V π d)).val.Evalb ![replacement] →
        (Postfix.carrier formula (SyntaxPolynomial.termExpression V σ d) (SyntaxPolynomial.formulaExpression V π d)).val.Evalb ![word] →
        (substitutionPayloadGraph V σ π d).val.Evalb ![out,x,replacement,word] →
        (if formula then formulaPayloadCarrier V σ π d else termPayloadCarrier V σ π d).val.Evalb ![out] := by
  simp [substitutionPreservationSentence]

@[simp] theorem freeForSuccessSentence_eval :
    (freeForSuccessSentence V σ π d).Evalb (M := M) ![] ↔
      ∀ x replacement word res ff : M,V.val.Evalb ![x] →
        (Postfix.carrier false (SyntaxPolynomial.termExpression V σ d) (SyntaxPolynomial.formulaExpression V π d)).val.Evalb ![replacement] →
        (Postfix.carrier true (SyntaxPolynomial.termExpression V σ d) (SyntaxPolynomial.formulaExpression V π d)).val.Evalb ![word] →
        (substitutionResultGraph V σ π d).val.Evalb ![res,x,replacement,word] →
        (substitutionFreeForGraph V σ π d).val.Evalb ![ff,x,replacement,word] →
        (ff = 1 ↔ ∃ new : M,
          (Postfix.carrier true (SyntaxPolynomial.termExpression V σ d) (SyntaxPolynomial.formulaExpression V π d)).val.Evalb ![new] ∧
            res = ok new) := by
  simp [freeForSuccessSentence,ok]

end Models

/-- The preservation proof has PA strength for every fixed coefficient
predicate, not merely T strength after a graph restriction. -/
theorem freeVariables_preservation_PA (formula : Bool) :
    𝗣𝗔 ⊢ freeVariablesPreservationSentence V σ π d formula := by
  apply complete.{0} 𝗣𝗔
  intro M _ _
  rw [models_iff,freeVariablesPreservationSentence_eval]
  intro word out hw hout
  obtain rfl := (freeVariablesGraph_eval V σ π d out word).mp hout
  exact freeVariables_carrier V σ π d formula word hw

theorem substitution_total_PA : 𝗣𝗔 ⊢ substitutionTotalSentence V σ π d := by
  apply complete.{0} 𝗣𝗔
  intro M _ _
  rw [models_iff,substitutionTotalSentence_eval]
  intro x replacement word
  refine ⟨substitutionPayload V σ π d x replacement word,by simp,?_⟩
  intro out hout
  exact (substitutionPayloadGraph_eval V σ π d out x replacement word).mp hout

theorem substitution_preservation_PA (formula : Bool) :
    𝗣𝗔 ⊢ substitutionPreservationSentence V σ π d formula := by
  apply complete.{0} 𝗣𝗔
  intro M _ _
  rw [models_iff,substitutionPreservationSentence_eval]
  intro x replacement word out _ hrep hw hout
  obtain rfl := (substitutionPayloadGraph_eval V σ π d out x replacement word).mp hout
  exact substitutionPayload_carrier V σ π d formula x replacement word hrep hw

/-- This PA theorem identifies the independently computed free-for flag
with the successful formula-value fiber, retaining its actual typed output. -/
theorem freeFor_success_PA : 𝗣𝗔 ⊢ freeForSuccessSentence V σ π d := by
  apply complete.{0} 𝗣𝗔
  intro M _ _
  rw [models_iff,freeForSuccessSentence_eval]
  intro x replacement word res ff _ hrep hw hres hff
  obtain rfl := (substitutionResultGraph_eval V σ π d res x replacement word).mp hres
  obtain rfl := (substitutionFreeForGraph_eval V σ π d ff x replacement word).mp hff
  rw [substitutionFreeFor_iff_success V σ π d x replacement word hrep hw]
  constructor
  · intro hs
    rcases substitutionResult_formula V σ π d x replacement word hrep hw with hz | ⟨new,hn,he⟩
    · simp [hz,pi₂_zero] at hs
    · exact ⟨new,hn,he⟩
  · rintro ⟨new,_,he⟩
    simp [he,ok]

end CategoricalEssentialIncompleteness.V46.ConcreteNamedSubstitution
