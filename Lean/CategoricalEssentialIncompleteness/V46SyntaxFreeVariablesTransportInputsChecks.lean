/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SyntaxFreeVariablesTransportInputs


/-! # Statement checks in `V46SyntaxFreeVariablesTransportInputsChecks` -/

@[expose] public section
noncomputable section
universe v₁ v₂ u₁ u₂
open CategoryTheory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness.V46.SyntaxFreeVariablesTransportInputsChecks
open SyntaxOperationsTransport
variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
variable [Regular C] [FinitaryExtensive C] [Regular D] [FinitaryExtensive D]
variable (E : C ≌ D) {X : C} {Y : D} (ℓ : E.functor.obj X ≅ Y)
example (n : ℕ) :
    (powerInputIso E ℓ (n+2)).hom ≫ prod.snd = E.functor.map prod.snd ≫ ℓ.hom :=
  powerInputIso_snd E ℓ n
example : (powerInputIso E ℓ 2).hom = (SyntaxOptionTransport.productIso E ℓ ℓ).hom :=
  powerInputIso_two E ℓ
example (V : D) (σ π : ℕ → D) (d : ℕ) :
    ((languageJointIso E V σ π d).hom.app (X,X)).1 ≫
      (SyntaxPolynomial.termExpression V σ d).eval.map (listPairIso E ℓ).hom =
        (termInputIso E ℓ V σ d).hom := language_term_input E ℓ V σ π d
end CategoricalEssentialIncompleteness.V46.SyntaxFreeVariablesTransportInputsChecks
