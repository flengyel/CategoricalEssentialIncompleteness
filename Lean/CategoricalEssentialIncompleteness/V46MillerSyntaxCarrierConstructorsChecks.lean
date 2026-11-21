/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerSyntaxCarrierConstructors


/-! # Constructor membership for arbitrary uniform coefficients -/

@[expose] public section
noncomputable section
open CategoryTheory
open CategoricalEssentialIncompleteness.V46
open CategoricalEssentialIncompleteness.V46.Miller
open CategoricalEssentialIncompleteness.V46.Miller.Syntax
variable {P : Uniform.Family}

example (p q : SyntaxPolynomial (Total.TotalCategory P)) (formula : Bool) {u : ℕ}
    (hu : u ∈ (Raw.carrier (Raw.uniformWords false p q) (Raw.uniformWords true p q)
      (if formula then q else p)).support) :
    SyntacticSyntax.Coding.constructor formula (Raw.skeleton (if formula then q else p)) u ∈
      (Raw.uniformWords formula p q).support := Raw.uniformWords_constructor p q formula hu

example (p q Q : SyntaxPolynomial (Total.TotalCategory P)) {u : ℕ}
    (hu : u ∈ (Raw.carrier (Raw.uniformWords false p q) (Raw.uniformWords true p q) Q).support) :
    Raw.wordGuard p q (SyntacticSyntax.Coding.childrenWord (Raw.skeleton Q) u) :=
  Raw.wordGuard_children p q Q hu
