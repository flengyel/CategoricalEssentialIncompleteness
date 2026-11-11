/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SyntacticGeneratedAxioms


/-! # Statement checks in `V46SyntacticGeneratedAxiomsChecks` -/

@[expose] public section
noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticLists
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax
open CategoricalEssentialIncompleteness.V46.SyntacticGeneratedAxioms
namespace CategoricalEssentialIncompleteness.V46.SyntacticGeneratedAxioms.Checks
variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
variable (V : PredicateCategory T) (σ π : ℕ → PredicateCategory T) (d : ℕ) (Γ : Carrier)
variable (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T]
example (word : M) :
    (theoremCarrier T V σ π d Γ).val.Evalb ![word] ↔
      (ConcreteNamedComparison.literalSentenceCarrier T V σ π d).val.Evalb ![word] ∧
        ∃ p : Obj T M (proofs T V σ π d Γ).a.left,
          ((F T M).map (conclusion T V σ π d Γ) p).val = word :=
  theoremCarrier_model T V σ π d M Γ word
example : T ⊢ theoremProgramSentence T V σ π d Γ := theoremProgram_theory T V σ π d Γ
end CategoricalEssentialIncompleteness.V46.SyntacticGeneratedAxioms.Checks
