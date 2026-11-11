/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SyntacticGenerationAdjunction

/-! # Statement checks for generation in the total restriction splitting -/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.LocalConnectedness
open CategoricalEssentialIncompleteness.V46
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticGenerationAdjunction

variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
variable (V : TotalSplit T) (σ π : ℕ → TotalSplit T) (d : ℕ)
local notation "S" => SyntacticSyntax.plainTotalCategoricalSyntax T V σ π d

example : generation T V σ π d ⊣ inclusion T V σ π d := adjunction T V σ π d

example : subobjectGeneration T V σ π d ⊣ subobjectInclusion T V σ π d :=
  subobjectAdjunction T V σ π d

example : (inclusion T V σ π d).Full := inferInstance

example : (inclusion T V σ π d).Faithful := inferInstance

example (A : Over (S).sentenceObject) (B : ClosedTheories T V σ π d) :
    ((generation T V σ π d).obj A ⟶ B) ≃ (A ⟶ (inclusion T V σ π d).obj B) :=
  (adjunction T V σ π d).homEquiv A B

example (A : Subobject (S).sentenceObject) :
    ((subobjectGeneration T V σ π d).obj A).val =
      SyntacticGeneratedTheoryTotal.sentenceTheory T V σ π d A.arrow :=
  generated_sentence_subobject T V σ π d A

example (B : Over (S).sentenceObject) :
    FirstOrderPresentations.Closed (SyntacticGeneratedTheoryTotal.proofAlgebra T V σ π d) B ↔
      Mono B.hom ∧ SyntacticGeneratedTheoryTotal.IsSentenceTheory T V σ π d B.hom :=
  closed_iff T V σ π d B

#print axioms CategoricalEssentialIncompleteness.V46.SyntacticGenerationAdjunction.adjunction
#print axioms CategoricalEssentialIncompleteness.V46.SyntacticGenerationAdjunction.subobjectAdjunction
#print axioms CategoricalEssentialIncompleteness.V46.SyntacticGenerationAdjunction.closed_iff
