/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NamedArithmeticProofSearchSource

/-! # Source-category Γ inverse-image statement checks -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.RestrictionCategory
open CategoricalEssentialIncompleteness.LocalConnectedness
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.NamedArithmeticSignature
open CategoricalEssentialIncompleteness.V46.NamedArithmeticProofSearch

namespace CategoricalEssentialIncompleteness.V46.NamedArithmeticProofSearch.SourceChecks

example (φ : Formula) (hφ : ∀ y, y ∈ φ.freeVariables → y = 0) :
    isTotal (sourceTheta φ hφ) := sourceTheta_total φ hφ

example (Γ : Carrier) (φ : Formula) (hφ : ∀ y, y ∈ φ.freeVariables → y = 0) :
    Idem.pull (sourceTheta φ hφ)
      (predicateIdem 𝗣𝗔 (SyntacticGeneratedAxioms.literalTheoremCarrier 𝗣𝗔
        variableSymbols functionSymbols relationSymbols bound Γ)) =
      predicateIdem 𝗣𝗔 (positive Γ φ) :=
  positive_source_pull Γ φ hφ

example (Γ : Carrier) (φ : Formula) (hφ : ∀ y, y ∈ φ.freeVariables → y = 0) :
    Idem.pull (sourceTheta φ hφ)
      (predicateIdem 𝗣𝗔 (SyntacticGeneratedAxioms.literalRefutationCarrier 𝗣𝗔
        variableSymbols functionSymbols relationSymbols bound Γ)) =
      predicateIdem 𝗣𝗔 (negative Γ φ) :=
  negative_source_pull Γ φ hφ

end CategoricalEssentialIncompleteness.V46.NamedArithmeticProofSearch.SourceChecks
