/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SyntaxSubstitutionTransportValues


/-! # Intrinsic term substitution and option-valued formula substitution commute with the input and output comparisons -/

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

variable (ℓ : E.functor.obj S₀.lists.algebra.carrier ≅ S₁.lists.algebra.carrier)
variable (hnil : E.functor.map S₀.lists.algebra.nil ≫ ℓ.hom =
  terminalComparison E.functor ≫ S₁.lists.algebra.nil)
variable (hsingleton : E.functor.map S₀.lists.singleton ≫ ℓ.hom =
  (E.counitIso.app V).hom ≫ S₁.lists.singleton)
variable (happend : E.functor.map S₀.lists.append ≫ ℓ.hom =
  (SyntaxOptionTransport.productIso E ℓ ℓ).hom ≫ S₁.lists.append)
variable (hdeletion : E.functor.map (S₀.lists.deletion S₀.decidableVariables) ≫ ℓ.hom =
  (SyntaxOptionTransport.productIso E (E.counitIso.app V) ℓ).hom ≫
    S₁.lists.deletion S₁.decidableVariables)
variable (hmembership : E.functor.map (S₀.lists.membership S₀.decidableVariables) ≫
  (DecidableVariables.Transport.booleanIso E).hom =
    (SyntaxOptionTransport.productIso E (E.counitIso.app V) ℓ).hom ≫
      S₁.lists.membership S₁.decidableVariables)



include c hnil hsingleton happend hdeletion hmembership in
example :
    E.functor.map S₀.termSubstitution ≫ (syntaxTermIso E V σ π d S₀ c).hom =
      (SyntaxOptionTransport.productIso E (syntaxTermIso E V σ π d S₀ c) b).hom ≫
        S₁.termSubstitution :=
  map_termSubstitution E V σ π d S₀ S₁ c ℓ hnil hsingleton happend hdeletion hmembership

include c hnil hsingleton happend hdeletion hmembership in
example :
    E.functor.map S₀.formulaSubstitutionOption ≫
        (SyntaxOptionTransport.optionIso E (syntaxFormulaIso E V σ π d S₀ c)).hom =
      (SyntaxOptionTransport.productIso E (syntaxFormulaIso E V σ π d S₀ c) b).hom ≫
        S₁.formulaSubstitutionOption :=
  map_formulaSubstitutionOption E V σ π d S₀ S₁ c ℓ hnil hsingleton happend hdeletion hmembership

include c hnil hsingleton happend hdeletion hmembership in
example : E.functor.obj S₀.admissibleSubstitution ≅ S₁.admissibleSubstitution :=
  admissibleSubstitutionIso E V σ π d S₀ S₁ c ℓ hnil hsingleton happend hdeletion hmembership

end CategoricalEssentialIncompleteness.V46.SyntaxOperationsTransport
