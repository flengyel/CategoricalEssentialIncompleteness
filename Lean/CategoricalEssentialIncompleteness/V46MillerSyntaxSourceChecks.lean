/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerSyntaxSource


/-! # Statement checks in `V46MillerSyntaxSourceChecks` -/

@[expose] public section
noncomputable section
open CategoryTheory FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.V46
open CategoricalEssentialIncompleteness.V46.Miller
open CategoricalEssentialIncompleteness.V46.Miller.Syntax
variable {P : Uniform.Family}

example {R : Total.TotalCategory P} (a b : SyntacticSyntax.RawPolynomial)
    (formula : Bool) (r word : ℕ) (hr : r ∈ R.obj.support)
    (hw : word ∈ (words P formula a b).support) :
    Raw.coefficientWord (R := R) (p := a.mapCoefficients (predicateFunctor P).obj)
      (q := b.mapCoefficients (predicateFunctor P).obj) (Nat.pair r word) :=
  Raw.source_coefficientWord a b formula r word hr hw

example (a b : SyntacticSyntax.RawPolynomial) (formula : Bool) (word : ℕ)
    (hw : word ∈ (words P formula a b).support) :
    SyntacticSyntax.Postfix.run (Raw.skeleton (a.mapCoefficients (predicateFunctor P).obj))
      (Raw.skeleton (b.mapCoefficients (predicateFunctor P).obj)) word 1=
        adjoin (Nat.pair word (if formula then 1 else 0)) 0+1 :=
  Raw.source_parser_success a b formula word hw

example {R : Total.TotalCategory P} {X Y : Over R}
    (a b : SyntacticSyntax.RawPolynomial)
    (hT : Raw.object R X Y (a.mapCoefficients (predicateFunctor P).obj) ⟶ X)
    (hF : Raw.object R X Y (b.mapCoefficients (predicateFunctor P).obj) ⟶ Y)
    (formula : Bool) {r word new : ℕ}
    (hw : word ∈ (words P formula a b).support)
    (hn : new ∈ Raw.evaluation hT hF (Nat.pair r word)) :
    ∃ value,new=adjoin (Nat.pair value (if formula then 1 else 0)) 0+1 :=
  Raw.source_evaluation_singleton a b hT hF formula hw hn
