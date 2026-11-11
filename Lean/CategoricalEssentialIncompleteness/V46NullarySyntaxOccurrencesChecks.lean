/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NullarySyntaxOccurrences

/-! # Checks for the free-syntax interpretation prerequisites -/

@[expose] public section

noncomputable section

universe v u

open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness CategoricalEssentialIncompleteness.V46

variable {D : Type u} [Category.{v} D] [Regular D] [FinitaryExtensive D]
variable {V : D}


open NullaryInterpretation
variable {X : D}
variable (S : CategoricalSyntax V (fun _ => ⊥_ D) (fun _ => X) 0)
variable {σ π : ℕ → D} {d : ℕ} (Q : CategoricalSyntax V σ π d)
variable (f : X ⟶ Q.sentenceObject)

example : (interpretation S Q f).2 ≫ Q.formulaOccurrences =
    S.formulaOccurrences ≫ StableListAlgebra.Comparison.map S.lists Q.lists :=
  formula_occurrences S Q f
example : sentenceInterpretation S Q f ≫ Q.sentenceInclusion =
    S.sentenceInclusion ≫ (interpretation S Q f).2 := sentenceInterpretation_inclusion S Q f
example : atomSentence S ≫ sentenceInterpretation S Q f = f := sentenceInterpretation_atom S Q f

#print axioms CategoricalEssentialIncompleteness.V46.NullaryInterpretation.occurrence_comparison
#print axioms CategoricalEssentialIncompleteness.V46.NullaryInterpretation.sentenceInterpretation
#print axioms
  CategoricalEssentialIncompleteness.V46.NullaryInterpretation.sentenceInterpretation_atom
