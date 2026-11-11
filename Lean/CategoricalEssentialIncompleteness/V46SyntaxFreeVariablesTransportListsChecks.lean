/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SyntaxFreeVariablesTransportLists


/-! # Statement checks in `V46SyntaxFreeVariablesTransportListsChecks` -/

@[expose] public section
noncomputable section
universe v₁ v₂ u₁ u₂
open CategoryTheory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness.V46.SyntaxFreeVariablesTransportListsChecks
open SyntaxOperationsTransport
variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
variable [Regular C] [FinitaryExtensive C] [Regular D] [FinitaryExtensive D]
variable (E : C ≌ D) {V₀ : C} {V₁ : D}
variable (L₀ : StableListAlgebra V₀) (L₁ : StableListAlgebra V₁)
variable (ℓ : E.functor.obj L₀.algebra.carrier ≅ L₁.algebra.carrier)
variable (hnil : E.functor.map L₀.algebra.nil ≫ ℓ.hom = terminalComparison E.functor ≫ L₁.algebra.nil)
variable (happend : E.functor.map L₀.append ≫ ℓ.hom =
  (SyntaxOptionTransport.productIso E ℓ ℓ).hom ≫ L₁.append)
example (n : ℕ) : E.functor.map (L₀.tupleAppend n) ≫ ℓ.hom =
    (powerInputIso E ℓ n).hom ≫ L₁.tupleAppend n :=
  tupleAppend_comparison E L₀ L₁ ℓ hnil happend n
example (σ : ℕ → D) (n : ℕ) :
    E.functor.map (L₀.constructorOccurrences (fun k => E.inverse.obj (σ k)) n) ≫ ℓ.hom =
      (constructorInputIso E ℓ σ n).hom ≫ L₁.constructorOccurrences σ n :=
  constructorOccurrences_comparison E L₀ L₁ ℓ hnil happend σ n
end CategoricalEssentialIncompleteness.V46.SyntaxFreeVariablesTransportListsChecks
