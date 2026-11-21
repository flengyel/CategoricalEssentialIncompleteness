/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerSyntaxChildren


/-! # The ordered child computations of a uniform syntax constructor -/

@[expose] public section
noncomputable section
open CategoryTheory
open CategoricalEssentialIncompleteness.V46
open CategoricalEssentialIncompleteness.V46.Miller
open CategoricalEssentialIncompleteness.V46.Miller.Syntax
variable {P : Uniform.Family} {R : Total.TotalCategory P} {X Y : Over R}
variable (a b : SyntacticSyntax.RawPolynomial)
variable (hT : Raw.object R X Y (a.mapCoefficients (predicateFunctor P).obj) ⟶ X)
variable (hF : Raw.object R X Y (b.mapCoefficients (predicateFunctor P).obj) ⟶ Y)

example (Q : SyntacticSyntax.RawPolynomial) {r u v : ℕ}
    (hm : Raw.MapValues a b hT hF Q r u v) :
    Raw.fiber R X Y (Q.mapCoefficients (predicateFunctor P).obj) (r,v) :=
  Raw.mapValues_fiber a b hT hF Q hm

example (Q : SyntacticSyntax.RawPolynomial) {r u v : ℕ}
    (hm : Raw.MapValues a b hT hF Q r u v) (tail : ℕ) :
    Raw.Trace hT hF r (Nat.natToList (SyntacticSyntax.Coding.childrenWord Q u)) (tail+1)
      (SyntacticSyntax.Coding.childStack Q v tail+1) := Raw.children_trace a b hT hF Q hm tail
