/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SyntaxSubstitutionTransportAlgebraTerm


/-! # Statement checks in `V46SyntaxSubstitutionTransportAlgebraTermChecks` -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v₁ v₂ u₁ u₂
open CategoryTheory CategoryTheory.Limits

namespace CategoricalEssentialIncompleteness.V46.SyntaxOperationsTransport
open SyntacticLists.Transport
open DecidableVariables.Transport
variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
variable [Regular C] [FinitaryExtensive C] [Regular D] [FinitaryExtensive D]
variable (E : C ≌ D) (V : D) (σ π : ℕ → D) (d : ℕ)
variable (S₀ : CategoricalSyntax (E.inverse.obj V)
  (fun n => E.inverse.obj (σ n)) (fun n => E.inverse.obj (π n)) d)
variable (S₁ : CategoricalSyntax V σ π d)
variable (c : mappedSyntaxAlgebra E V σ π d S₀ ≅ S₁.algebra)
local notation "P₀" => S₀.substitutionParameters
local notation "P₁" => S₁.substitutionParameters
local notation "b" => substitutionParameterIso E V σ π d S₀ S₁ c
local notation "H" => sliceEquivalence E b
local notation "a" => substitutionStateIso E V σ π d S₀ S₁ c
local notation "f" => substitutionFormulaStateIso E V σ π d S₀ S₁ c
local notation "t" => substitutionTermStateIso E V σ π d S₀ S₁ c


example :
    (H).functor.map S₀.substitutionAlgebra.str.1 ≫
        (coefficientComparison E b S₀.substitutionCarriers.1 S₁.substitutionCarriers.1 t).hom =
      (syntaxParameterTermInputIso E b V σ d S₀.substitutionCarriers S₁.substitutionCarriers a).hom ≫
        S₁.substitutionAlgebra.str.1 :=
  substitutionTargetTerm_structure E V σ π d S₀ S₁ c

end CategoricalEssentialIncompleteness.V46.SyntaxOperationsTransport
