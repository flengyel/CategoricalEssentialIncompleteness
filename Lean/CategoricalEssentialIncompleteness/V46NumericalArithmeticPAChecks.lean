/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NumericalArithmeticPA


/-! # The arithmetic PA-axiom inclusion supplies source admissibility -/

@[expose] public section
noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
namespace CategoricalEssentialIncompleteness.V46.NumericalArithmetic.PAChecks
open NamedArithmeticSignature ArithmeticNamedAxiomComparison

example (Γ : Carrier)
    (hΓ : ∀ word : ℕ, ArithmeticIndexedPAEnumeration.axiomCodes.val.Evalb ![word] → Γ.val.Evalb ![word]) :
    ∀ ψ : Formula, PAAxiom ψ →
      SyntacticNamedHilbert.Derives functionSymbols relationSymbols bound Γ ψ := extendsPA Γ hΓ

example (Γ : Carrier)
    (hΓ : ∀ word : ℕ, ArithmeticIndexedPAEnumeration.axiomCodes.val.Evalb ![word] → Γ.val.Evalb ![word]) :
    ArithmeticNamedProofTranslation.AxiomsAdmissible Γ 𝗣𝗔 := axiomsAdmissible Γ hΓ

end CategoricalEssentialIncompleteness.V46.NumericalArithmetic.PAChecks
