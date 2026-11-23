/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46RelationalSignatureAdjunction

/-! # The sorts, morphisms, unit and counit of the relational signature adjunction -/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace CategoricalEssentialIncompleteness.V46.Voutsadakis.Checks

theorem hom_equivalence (A : HSet.{u}) (X : Signature.{u}) :
    Nonempty ((freeSignature.obj A ⟶ X) ≃ A.Components (Formula.hierarchy X.symbols)) :=
  ⟨(signatureAdjunction.homEquiv A X).trans (HSet.homEquivComponents A _)⟩

theorem substitution_under_quantifier {X Y : Signature.{u}} (f : X ⟶ Y)
    (N : Finset ℕ) (k : ℕ) (p : Formula X.symbols.carrier)
    (hp : Formula.Supported X.symbols p (insert k N)) :
    (formulas.map f).map (.ex k p) = .ex k ((formulas.map f).map p) ∧
      Formula.Supported Y.symbols (.ex k ((formulas.map f).map p)) N :=
  ⟨rfl, Formula.substitute_supported f p (insert k N) hp⟩

theorem unit_and_counit (A : HSet.{u}) (X : Signature.{u}) :
    (∀ x, (signatureAdjunction.unit.app A).map x = Formula.symbol x) ∧
      (∀ p, (signatureAdjunction.counit.app X).map p = p) := ⟨fun _ ↦ rfl, fun _ ↦ rfl⟩

end CategoricalEssentialIncompleteness.V46.Voutsadakis.Checks

open CategoricalEssentialIncompleteness.V46.Voutsadakis

#print axioms signatureAdjunction
#print axioms Checks.hom_equivalence
#print axioms Checks.substitution_under_quantifier
#print axioms Checks.unit_and_counit
