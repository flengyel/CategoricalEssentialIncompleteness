/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SyntaxSubstitutionTransportFormula


/-! # Substitution under equality, relation, negation and implication -/

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
    E.functor.map S₀.equalitySubstitutionPair ≫
        (substitutionFormulaStateIso E V σ π d S₀ S₁ c).hom =
      (normalizedPolynomialIso E S₀.substitutionCarriers S₁.substitutionCarriers
        (substitutionStateIso E V σ π d S₀ S₁ c) (SyntaxPolynomial.power .term 2)
        (SyntaxPolynomial.power .term 2) (SyntaxPolynomial.power .term 2) rfl rfl).hom ≫
        S₁.equalitySubstitutionPair :=
  map_equalitySubstitutionPair E V σ π d S₀ S₁ c

example :
    E.functor.map S₀.relationSubstitutionPair ≫
        (substitutionFormulaStateIso E V σ π d S₀ S₁ c).hom =
      (substitutionStateConstructorsInputIso E V σ π d S₀ S₁ c π d).hom ≫
        S₁.relationSubstitutionPair :=
  map_relationSubstitutionPair E V σ π d S₀ S₁ c

example :
    E.functor.map S₀.negationSubstitutionPair ≫
        (substitutionFormulaStateIso E V σ π d S₀ S₁ c).hom =
      (substitutionFormulaStateIso E V σ π d S₀ S₁ c).hom ≫ S₁.negationSubstitutionPair :=
  map_negationSubstitutionPair E V σ π d S₀ S₁ c

example :
    E.functor.map S₀.implicationSubstitutionPair ≫
        (substitutionFormulaStateIso E V σ π d S₀ S₁ c).hom =
      (SyntaxOptionTransport.productIso E
        (substitutionFormulaStateIso E V σ π d S₀ S₁ c)
        (substitutionFormulaStateIso E V σ π d S₀ S₁ c)).hom ≫ S₁.implicationSubstitutionPair :=
  map_implicationSubstitutionPair E V σ π d S₀ S₁ c

end CategoricalEssentialIncompleteness.V46.SyntaxOperationsTransport
