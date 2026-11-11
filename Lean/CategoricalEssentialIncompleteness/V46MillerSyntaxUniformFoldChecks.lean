/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerSyntaxUniformFold


/-! # Statement checks in `V46MillerSyntaxUniformFoldChecks` -/

@[expose] public section
noncomputable section
open CategoryTheory FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.V46
open CategoricalEssentialIncompleteness.V46.Miller
open CategoricalEssentialIncompleteness.V46.Miller.Syntax
variable {P : Uniform.Family} {R : Total.TotalCategory P} {X Y : Over R}
variable {p q : SyntaxPolynomial (Total.TotalCategory P)}
variable (hT : Raw.object R X Y p ⟶ X) (hF : Raw.object R X Y q ⟶ Y)

example : Raw.uniformWordFamily R false p q ⟶ X := Raw.uniformFold hT hF false
example : Raw.uniformWordFamily R true p q ⟶ Y := Raw.uniformFold hT hF true

example (formula : Bool) :
    Raw.uniformFoldLeft hT hF formula ≫ (if formula then Y else X).hom=
      (Raw.uniformWordFamily R formula p q).hom := Raw.uniformFold_parameter hT hF formula

example (formula : Bool) (r word value : ℕ) :
    value ∈ Total.val (Raw.uniformFold hT hF formula).left.hom (Nat.pair r word) ↔
      r ∈ R.obj.support ∧ word ∈ (Raw.uniformWords formula p q).support ∧
        adjoin (Nat.pair value (if formula then 1 else 0)) 0+1 ∈ Raw.evaluation hT hF (Nat.pair r word) :=
  Raw.uniformFold_graph hT hF formula r word value
