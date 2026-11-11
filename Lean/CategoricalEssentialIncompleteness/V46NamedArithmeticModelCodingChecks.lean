/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NamedArithmeticModelCoding


/-! # Statement checks in `V46NamedArithmeticModelCodingChecks` -/

@[expose] public section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.V46
open SyntacticPredicates NamedPostfixEncoding NamedArithmeticModelCoding
example {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    {σ π : ℕ → Carrier} {d : ℕ} (φ : NamedFiniteSyntax.Formula (Symbols σ) (Symbols π) d) :
    (formulaCode φ : M) = formulaWord φ := formulaWord_natCast φ
example {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] (name : M) (n : ℕ) (c : Fin n → M) :
    ConcreteNamedSubstitution.member name (gatherTuple n c) = 1 ↔
      ∃ i,ConcreteNamedSubstitution.member name (c i) = 1 := member_gatherTuple name n c
