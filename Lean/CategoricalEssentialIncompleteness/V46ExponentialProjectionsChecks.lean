/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ExponentialProjections

/-! The literal bounded projections, their inverse equations and certificates. -/

@[expose] public section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoricalEssentialIncompleteness.V46.ExponentialPairing

example : Primrec first := first_primrec
example : Primrec second := second_primrec
example (n : ℕ) : code (first n) (second n) = n := code_first_second n
example (a b : ℕ) : first (code a b) = a := first_code a b
example (a b : ℕ) : second (code a b) = b := second_code a b

example : 𝗣𝗔 ⊢ projectionsSentence := projections_PA
example : 𝗣𝗔 ⊢ projectionTotalSentence firstGraph := first_total_PA
example : 𝗣𝗔 ⊢ projectionTotalSentence secondGraph := second_total_PA
example (n a : ℕ) : firstGraph.val.Evalb ![n, a] ↔ a = first n := firstGraph_nat n a
example (n b : ℕ) : secondGraph.val.Evalb ![n, b] ↔ b = second n := secondGraph_nat n b
