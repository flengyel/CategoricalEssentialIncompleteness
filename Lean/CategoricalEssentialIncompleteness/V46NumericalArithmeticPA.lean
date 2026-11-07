/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46ArithmeticIndexedPAEnumeration

/-! # The printed arithmetic PA-axiom inclusion supplies source admissibility -/
noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates

namespace CategoricalEssentialIncompleteness.V46.NumericalArithmetic
open NamedArithmeticSignature ArithmeticNamedAxiomComparison

/-- Inclusion of the chosen, already compared native PA sentence axioms. -/
def ContainsPA (Γ : Carrier) : Prop :=
  ∀ word : ℕ, ArithmeticIndexedPAEnumeration.axiomCodes.val.Evalb ![word] → Γ.val.Evalb ![word]

theorem containsPA_iff (Γ : Carrier) : ContainsPA Γ ↔
    ∀ ψ : Formula, PAAxiom ψ → Γ.val.Evalb ![formulaCode ψ] := by
  constructor
  · intro h ψ hψ
    exact h (formulaCode ψ) ((ArithmeticIndexedPAEnumeration.axiomCodes_standard _).mpr ⟨ψ,hψ,rfl⟩)
  · intro h word hw
    obtain ⟨ψ,hψ,rfl⟩ := (ArithmeticIndexedPAEnumeration.axiomCodes_standard word).mp hw
    exact h ψ hψ

theorem extendsPA (Γ : Carrier) (hΓ : ContainsPA Γ) : ExtendsPA Γ := by
  intro ψ hψ
  exact SyntacticNamedHilbert.Derives.axiom ψ ((containsPA_iff Γ).mp hΓ ψ hψ) hψ.1

/-- Admissibility is derived from the concrete inclusion of axiom codes. -/
theorem axiomsAdmissible (Γ : Carrier) (hΓ : ContainsPA Γ) :
    ArithmeticNamedProofTranslation.AxiomsAdmissible Γ 𝗣𝗔 :=
  ArithmeticNamedAxiomComparison.axiomsAdmissible_PA Γ (extendsPA Γ hΓ)

end CategoricalEssentialIncompleteness.V46.NumericalArithmetic
