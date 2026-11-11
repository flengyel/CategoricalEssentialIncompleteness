/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NullarySyntaxTerms

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
example : V ≅ S.algebra.a.1 := variableIso S
example : (interpretation S Q f).1 = (variableIso S).inv ≫ Q.variableConstructor :=
  interpretation_term S Q f

#print axioms CategoricalEssentialIncompleteness.V46.NullaryInterpretation.variable_isIso
#print axioms CategoricalEssentialIncompleteness.V46.NullaryInterpretation.interpretation_term
