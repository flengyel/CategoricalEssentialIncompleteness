/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NamedGammaModelSource


/-! # Statement checks in `V46NamedGammaModelSourceChecks` -/

@[expose] public section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
namespace CategoricalEssentialIncompleteness.V46.NamedGammaModel
open NamedArithmeticSignature SyntacticPredicates
example (A : Carrier) :
    Consistent (ArithmeticNamedProofConnectives.system A) ↔
      ¬ SyntacticNamedHilbert.Derives functionSymbols relationSymbols bound A
        ArithmeticNamedTranslation.falsity := consistent_iff_no_falsity A
example (A : Carrier) (hPA : ∀ p ∈ (𝗣𝗔 : ArithmeticTheory),
    SyntacticNamedHilbert.Derives functionSymbols relationSymbols bound A
      (ArithmeticNamedTranslation.translateFormula 0 ![] p)) :
    ∀ p ∈ sourceTheory A, SyntacticNamedHilbert.Derives functionSymbols relationSymbols bound A
      (ArithmeticNamedTranslation.translateFormula 0 ![] p) := source_axioms_admissible A hPA
example (A : Carrier) (hPA : ArithmeticNamedProofTranslation.AxiomsAdmissible A 𝗣𝗔)
    (hc : Consistent (ArithmeticNamedProofConnectives.system A)) :
    Consistent (sourceTheory A) := source_consistent A hPA hc
example (A : Carrier) (hc : Consistent (sourceTheory A)) :
    ∃ (K : Type) (s : ORingStructure K), letI := s; K↓[ℒₒᵣ] ⊧* sourceTheory A :=
  exists_source_model A hc
example (A : Carrier) {K : Type} [ORingStructure K] [K↓[ℒₒᵣ] ⊧* sourceTheory A] (ρ : ℕ → K) :
    ∀ φ : Formula, A.val.Evalb ![formulaCode φ] → φ.freeVariables = [] →
      φ.Holds ArithmeticNamedTranslation.functions ArithmeticNamedTranslation.relations ρ :=
  source_model_models A ρ
end CategoricalEssentialIncompleteness.V46.NamedGammaModel
