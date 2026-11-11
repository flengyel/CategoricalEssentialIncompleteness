/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NullarySubstitutionAlgebra

/-! # Statement checks for NullarySubstitutionAlgebra -/

@[expose] public section

noncomputable section

universe v u
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness CategoricalEssentialIncompleteness.V46

variable {D : Type u} [Category.{v} D] [Regular D] [FinitaryExtensive D]
variable {V X : D}
variable (S : CategoricalSyntax V (fun _ => ⊥_ D) (fun _ => X) 0)
variable {σ π : ℕ → D} {d : ℕ} (Q : CategoricalSyntax V σ π d)
variable (f : X ⟶ Q.sentenceObject)
open NullaryInterpretation

example : Endofunctor.Algebra (SyntaxPolynomial.jointFunctor
    ((SyntaxPolynomial.termExpression V (fun _ => ⊥_ D) 0).withParameters S.substitutionParameters)
    ((SyntaxPolynomial.formulaExpression V (fun _ => X) 0).withParameters S.substitutionParameters)) :=
  targetSubstitutionAlgebra S Q f

#print axioms CategoricalEssentialIncompleteness.V46.NullaryInterpretation.targetSubstitutionAlgebra
