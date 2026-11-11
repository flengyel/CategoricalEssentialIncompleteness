/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerSyntaxOperations


/-! # Statement checks in `V46MillerSyntaxOperationsChecks` -/

@[expose] public section
noncomputable section
open CategoryTheory
open CategoricalEssentialIncompleteness.V46
open CategoricalEssentialIncompleteness.V46.Miller
open CategoricalEssentialIncompleteness.V46.Miller.Syntax
variable {P : Uniform.Family} {R : Total.TotalCategory P} {X Y Z : Over R}
variable {p : SyntaxPolynomial (Total.TotalCategory P)} (h : Raw.object R X Y p ⟶ Z)

example : Uniform.Represented P (.product .nat .nat) .nat (Raw.operation h) :=
  Raw.operation_represented h

example : Uniform.Enumerable P (fun a : (ℕ × ℕ) × ℕ => a.2 ∈ Raw.operation h a.1) :=
  Raw.operation_enumerable h

example {r u : ℕ} (hu : Raw.fiber R X Y p (r,u)) : ∃! v,v ∈ Raw.operation h (r,u) :=
  Raw.operation_existsUnique h hu

example {r u v : ℕ} (hv : v ∈ Raw.operation h (r,u)) :
    Raw.fiber R X Y p (r,u) ∧ r ∈ Total.val Z.hom.hom v := Raw.operation_support h hv

example {r u v w : ℕ} (hv : v ∈ Raw.operation h (r,u)) (hw : w ∈ Raw.operation h (r,u)) : v=w :=
  Raw.operation_functional h hv hw
