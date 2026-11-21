/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NamedArithmeticClosedSubstitutionTheory


/-! # PA itself proves closed-replacement admissibility for the independent free-for algorithm, and existence of its typed option result -/

@[expose] public section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoricalEssentialIncompleteness.V46
open SyntacticPredicates NamedArithmeticClosedSubstitution
example (V : Carrier) (σ π : ℕ → Carrier) (d : ℕ) : 𝗣𝗔 ⊢ closedReplacementSentence V σ π d := closedReplacement_PA V σ π d
