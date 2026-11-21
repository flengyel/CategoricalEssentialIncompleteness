/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SyntaxSubstitutionTransportConstructorsFormula


/-! # Formula constructors under the algebra isomorphism -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v₁ v₂ u₁ u₂
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46
open CategoricalEssentialIncompleteness.V46.SyntaxOperationsTransport
variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
variable [Regular C] [FinitaryExtensive C] [Regular D] [FinitaryExtensive D]
variable (E : C ≌ D) (V : D) (σ π : ℕ → D) (d : ℕ)
variable (S₀ : CategoricalSyntax (E.inverse.obj V)
  (fun n => E.inverse.obj (σ n)) (fun n => E.inverse.obj (π n)) d)
variable (S₁ : CategoricalSyntax V σ π d)
variable (c : mappedSyntaxAlgebra E V σ π d S₀ ≅ S₁.algebra)

example : E.functor.map S₀.equalityConstructor ≫ (syntaxFormulaIso E V σ π d S₀ c).hom =
    (SyntaxOptionTransport.productIso E (syntaxTermIso E V σ π d S₀ c)
      (syntaxTermIso E V σ π d S₀ c)).hom ≫ S₁.equalityConstructor :=
  syntax_equality_constructor E V σ π d S₀ S₁ c

example : E.functor.map S₀.relationConstructors ≫ (syntaxFormulaIso E V σ π d S₀ c).hom =
    (syntaxConstructorsInputIso E V σ π d S₀ S₁ c π d).hom ≫ S₁.relationConstructors :=
  syntax_relation_constructors E V σ π d S₀ S₁ c

example : E.functor.map S₀.negationConstructor ≫ (syntaxFormulaIso E V σ π d S₀ c).hom =
    (syntaxFormulaIso E V σ π d S₀ c).hom ≫ S₁.negationConstructor :=
  syntax_negation_constructor E V σ π d S₀ S₁ c

example : E.functor.map S₀.implicationConstructor ≫ (syntaxFormulaIso E V σ π d S₀ c).hom =
    (SyntaxOptionTransport.productIso E (syntaxFormulaIso E V σ π d S₀ c)
      (syntaxFormulaIso E V σ π d S₀ c)).hom ≫ S₁.implicationConstructor :=
  syntax_implication_constructor E V σ π d S₀ S₁ c

example : E.functor.map S₀.quantifierConstructor ≫ (syntaxFormulaIso E V σ π d S₀ c).hom =
    (SyntaxOptionTransport.productIso E (E.counitIso.app V)
      (syntaxFormulaIso E V σ π d S₀ c)).hom ≫ S₁.quantifierConstructor :=
  syntax_quantifier_constructor E V σ π d S₀ S₁ c
