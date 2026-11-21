/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NamedArithmeticStandardCodes


/-! # Positive Sigma-one graph instances commute with standard numeral parameters in every PA model -/

@[expose] public section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.V46
open SyntacticPredicates NamedArithmeticStandardCodes
example {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (C : Carrier) (n : ℕ) (hn : C.val.Evalb ![n]) : C.val.Evalb (M := M) ![(n : M)] :=
  carrier_natCast C n hn
example {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] (name : M) (l : List ℕ) :
    ConcreteNamedSubstitution.member name ((SyntacticSyntax.NatVectors.pack l : ℕ) : M) = 1 ↔
      ∃ y ∈ l,(y : M) = name := member_pack_natCast name l
