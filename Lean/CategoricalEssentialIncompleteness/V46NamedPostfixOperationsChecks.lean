/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NamedPostfixOperations


/-! # Standard polynomial operations on ordered named payloads -/

@[expose] public section
noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
namespace CategoricalEssentialIncompleteness.V46.NamedPostfixOperationsChecks
open NamedPostfixEncoding SyntacticSyntax SyntacticSyntax.NatVectors
example (σ : ℕ → Carrier) (f g : ℕ → ℕ) (d : ℕ) (k : Fin (d + 1))
    (s : ℕ) (children : Fin k.val → ℕ) :
    ConcreteNamedSubstitution.mapChildren f g (SyntaxPolynomial.constructors σ d)
      (arityInput d k (Arithmetic.pair s (childTuple k.val children))) =
      arityInput d k (Arithmetic.pair s (childTuple k.val (fun i => f (children i)))) :=
  mapChildren_arityInput σ f g d k s children
example (σ : ℕ → Carrier) (d : ℕ) (k : Fin (d + 1)) (s : ℕ)
    (lists : Fin k.val → List ℕ) :
    ConcreteNamedSubstitution.gather (SyntaxPolynomial.constructors σ d)
      (arityInput d k (Arithmetic.pair s (childTuple k.val (fun i => pack (lists i))))) =
      pack (List.ofFn lists).flatten := gather_arityInput σ d k s lists
example (σ π : ℕ → Carrier) (d : ℕ) :
    Function.Injective (optionCode (σ := σ) (π := π) (d := d)) := optionCode_injective
end CategoricalEssentialIncompleteness.V46.NamedPostfixOperationsChecks
