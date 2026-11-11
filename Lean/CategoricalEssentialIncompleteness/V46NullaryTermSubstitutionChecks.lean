/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NullaryTermSubstitution

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
example : S.termSubstitution ≫ (interpretation S Q f).1 =
    prod.map (interpretation S Q f).1 (prod.map (𝟙 V) (interpretation S Q f).1) ≫
      Q.termSubstitution := term_substitution S Q f
example {Z : D} (t : Z ⟶ S.algebra.a.1) (p : Z ⟶ S.substitutionParameters) :
    prod.lift t p ≫ S.termSubstitution ≫ (interpretation S Q f).1 =
      prod.lift (t ≫ (interpretation S Q f).1) (p ≫ substitutionParameterMap S Q f) ≫
        Q.termSubstitution := term_substitution_value S Q f t p

#print axioms CategoricalEssentialIncompleteness.V46.NullaryInterpretation.term_substitution
#print axioms CategoricalEssentialIncompleteness.V46.NullaryInterpretation.term_substitution_value
