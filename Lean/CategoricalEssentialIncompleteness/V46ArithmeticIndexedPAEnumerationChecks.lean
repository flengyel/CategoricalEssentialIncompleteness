/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ArithmeticIndexedPAEnumeration

/-! # Actual native PA axioms, actual literal codes and the indexed extension condition -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.NamedArithmeticSignature

namespace CategoricalEssentialIncompleteness.V46.ArithmeticIndexedPAEnumerationChecks
open ArithmeticIndexedPAEnumeration ArithmeticNamedAxiomComparison

example (out : ℕ) :
    axiomCodes.val.Evalb ![out] ↔ ∃ ψ : Formula,
      (ψ.freeVariables = [] ∧ ∃ φ, PASeed φ ∧ UniversalClosure φ ψ) ∧
      formulaCode ψ = out :=
  axiomCodes_standard out

example (e : ℕ) :
    ∀ ψ : Formula,
      (ψ.freeVariables = [] ∧ ∃ φ, PASeed φ ∧ UniversalClosure φ ψ) →
      SyntacticNamedHilbert.Derives functionSymbols relationSymbols bound
        (ArithmeticIndexedAxioms.fiberAxioms axiomCodes e) ψ :=
  fiber_extendsPA e

example (e : ℕ) :
    ArithmeticNamedProofTranslation.AxiomsAdmissible
      (ArithmeticIndexedAxioms.fiberAxioms axiomCodes e) 𝗣𝗔 :=
  ArithmeticNamedAxiomComparison.axiomsAdmissible_PA _ (fiber_extendsPA e)

example (φ ψ : Formula) :
    closureRelation.val.Evalb ![formulaCode ψ,formulaCode φ] ↔ UniversalClosure φ ψ :=
  closureRelation_codes φ ψ

end CategoricalEssentialIncompleteness.V46.ArithmeticIndexedPAEnumerationChecks
