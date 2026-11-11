/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NumericalArithmeticIncompleteness


/-! # Statement checks in `V46NumericalArithmeticIncompletenessChecks` -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.RestrictionCategory
open CategoricalEssentialIncompleteness.LocalConnectedness
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
namespace CategoricalEssentialIncompleteness.V46.NumericalArithmetic.Incompleteness.Checks
example (Γ : Carrier) (hPA : ContainsPA Γ) :
    includedA ≤ Idem.pull theta (theoremIdem paAxioms) ∧
      includedB ≤ Idem.pull theta (Idem.pull nu (theoremIdem paAxioms)) ∧
        theoremIdem paAxioms ≤ theoremIdem Γ :=
  domain_inclusions Γ hPA
example (Γ : Carrier) :
    theoremIdem Γ = Ranges.range (NumericalTuples.splitComparison.map (ProofComparison.conclusion Γ)) := rfl
example (Γ : Carrier) : ClassicalPrograms.splitSupport (theoremIdem Γ) =
    {word : ℕ | (ArithmeticLiteralModel.theoremPredicate Γ).val.Evalb (M := ℕ) ![word]} :=
  theorem_support Γ
example (Γ : Carrier) (hPA : ContainsPA Γ)
    (hc : Consistent (ArithmeticNamedProofConnectives.system Γ)) :
    theoremIdem Γ ⊓ Idem.pull nu (theoremIdem Γ) = ⊥ :=
  theorem_refutation_disjoint Γ hPA hc
example (Γ : Carrier) (hPA : ContainsPA Γ)
    (hc : Consistent (ArithmeticNamedProofConnectives.system Γ)) :
    Inseparable (theoremIdem Γ) (Idem.pull nu (theoremIdem Γ)) ∧
      theoremIdem Γ ⊔ Idem.pull nu (theoremIdem Γ) ≠ ⊤ := categorical_incompleteness Γ hPA hc
example (Γ : Carrier) :
    Idem.pull syntaxSentenceIso.hom (theoremIdem Γ) =
      Ranges.range (numericalQ.map (SentenceProofCodes.conclusion Γ)) := syntax_theorem_range Γ
example (Γ : Carrier) (hPA : ContainsPA Γ)
    (hc : Consistent (ArithmeticNamedProofConnectives.system Γ)) :
    Inseparable (syntaxTheoremIdem Γ)
      (Idem.pull (numericalQ.map Coordinates.numericalSyntax.sentenceNegation) (syntaxTheoremIdem Γ)) ∧
      syntaxTheoremIdem Γ ⊔
        Idem.pull (numericalQ.map Coordinates.numericalSyntax.sentenceNegation) (syntaxTheoremIdem Γ) ≠ ⊤ :=
  syntax_categorical_incompleteness Γ hPA hc
end CategoricalEssentialIncompleteness.V46.NumericalArithmetic.Incompleteness.Checks
