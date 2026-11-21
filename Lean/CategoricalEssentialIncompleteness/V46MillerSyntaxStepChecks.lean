/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerSyntaxStep


/-! # A uniformly represented postfix step for arbitrary slice operations -/

@[expose] public section
noncomputable section
open CategoryTheory
open CategoricalEssentialIncompleteness.V46
open CategoricalEssentialIncompleteness.V46.Miller
open CategoricalEssentialIncompleteness.V46.Miller.Syntax
variable {P : Uniform.Family} {R : Total.TotalCategory P} {X Y : Over R}
variable {p : SyntaxPolynomial (Total.TotalCategory P)}

example {Z : Over R} (h : Raw.object R X Y p ⟶ Z) (formula : Bool) :
    Uniform.Represented P (.product .nat (.product .nat .nat)) .nat (Raw.outcome h formula) :=
  Raw.outcome_represented h formula

example (h : Raw.object R X Y p ⟶ X) (r s stack : ℕ)
    (hr : r ∈ R.obj.support)
    (hs : s ∈ (Raw.carrier (Total.terminalCarrier (P := P)) (Total.terminalCarrier (P := P)) p).support)
    (hst : Raw.fiberStack R X Y (r,stack)) :
    ∃ new,new ∈ Raw.outcome h false (r,(s,stack)) ∧ Raw.status R X Y (r,new) :=
  Raw.outcome_exists h r s stack hr hs hst

example (h : Raw.object R X Y p ⟶ Y) (r s stack : ℕ)
    (hr : r ∈ R.obj.support)
    (hs : s ∈ (Raw.carrier (Total.terminalCarrier (P := P)) (Total.terminalCarrier (P := P)) p).support)
    (hst : Raw.fiberStack R X Y (r,stack)) :
    ∃ new,new ∈ Raw.outcome h true (r,(s,stack)) ∧ Raw.status R X Y (r,new) :=
  Raw.formulaOutcome_exists h r s stack hr hs hst
