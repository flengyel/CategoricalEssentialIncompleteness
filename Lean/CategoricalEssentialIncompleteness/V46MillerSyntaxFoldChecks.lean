/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerSyntaxFold


/-! # Arbitrary-slice fold morphisms on the original literal words -/

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

example : Raw.wordFamily (R := R) a b false ⟶ X := Raw.fold a b hT hF false
example : Raw.wordFamily (R := R) a b true ⟶ Y := Raw.fold a b hT hF true

example (formula : Bool) :
    Raw.foldLeft a b hT hF formula ≫ (if formula then Y else X).hom=
      (Raw.wordFamily (R := R) a b formula).hom := Raw.fold_parameter a b hT hF formula

example (formula : Bool) (r word value : ℕ) :
    value ∈ Total.val (Raw.fold a b hT hF formula).left.hom (Nat.pair r word) ↔
      r ∈ R.obj.support ∧ word ∈ (words P formula a b).support ∧
        adjoin (Nat.pair value (if formula then 1 else 0)) 0+1 ∈ Raw.evaluation hT hF (Nat.pair r word) :=
  Raw.fold_graph a b hT hF formula r word value
