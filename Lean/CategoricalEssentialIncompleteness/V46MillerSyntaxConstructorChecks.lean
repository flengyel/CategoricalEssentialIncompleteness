/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerSyntaxConstructor


/-! # Constructor equations of the uniform finite-record evaluator -/

@[expose] public section
noncomputable section
open CategoryTheory FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.V46
open CategoricalEssentialIncompleteness.V46.Miller
open CategoricalEssentialIncompleteness.V46.Miller.Syntax
variable {P : Uniform.Family} {R : Total.TotalCategory P} {X Y : Over R}
variable (a b : SyntacticSyntax.RawPolynomial)
variable (hT : Raw.object R X Y (a.mapCoefficients (predicateFunctor P).obj) ⟶ X)
variable (hF : Raw.object R X Y (b.mapCoefficients (predicateFunctor P).obj) ⟶ Y)

example (formula : Bool) (r u value : ℕ) (hr : r ∈ R.obj.support)
    (hu : (SyntacticSyntax.rawCarrier (SyntacticSyntax.Postfix.plainCarrier false a b)
      (SyntacticSyntax.Postfix.plainCarrier true a b) (if formula then b else a)).val.Evalb (M := ℕ) ![u]) :
    (value ∈ Total.val (Raw.fold a b hT hF formula).left.hom
      (Nat.pair r (SyntacticSyntax.Coding.constructor formula (if formula then b else a) u)) ↔
      ∃ v,Raw.MapValues a b hT hF (if formula then b else a) r u v ∧
        value ∈ (if formula then Raw.operation hF else Raw.operation hT) (r,v)) :=
  Raw.fold_constructor a b hT hF formula r u value hr hu
