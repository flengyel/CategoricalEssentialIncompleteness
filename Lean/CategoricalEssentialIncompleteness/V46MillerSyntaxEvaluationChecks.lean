/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerSyntaxEvaluation


/-! # Evaluation of postfix words in a parameter slice -/

@[expose] public section
noncomputable section
open CategoryTheory
open CategoricalEssentialIncompleteness.V46
open CategoricalEssentialIncompleteness.V46.Miller
open CategoricalEssentialIncompleteness.V46.Miller.Syntax
variable {P : Uniform.Family} {R : Total.TotalCategory P} {X Y : Over R}
variable {p q : SyntaxPolynomial (Total.TotalCategory P)}
variable (hT : Raw.object R X Y p ⟶ X) (hF : Raw.object R X Y q ⟶ Y)

example : Uniform.Represented P .nat .nat (Raw.evaluation hT hF) := Raw.evaluation_represented hT hF

example {x : ℕ} (hx : Raw.coefficientWord (R := R) (p := p) (q := q) x) :
    (Raw.evaluation hT hF x).Dom := Raw.evaluation_total hT hF hx

example {x : ℕ} (hx : Raw.coefficientWord (R := R) (p := p) (q := q) x) :
    ∃! s,s ∈ Raw.evaluation hT hF x ∧ Raw.status R X Y ((Nat.unpair x).1,s) :=
  Raw.evaluation_existsUnique hT hF hx

example (x s : ℕ) : s ∈ Raw.evaluation hT hF x ↔
    ∃ states,UniformTrees.Record (Raw.loopStep hT hF) (fun _ => 1) x (Raw.loopLength x) states ∧
      states.getD (Raw.loopLength x) 0=s := Raw.evaluation_graph hT hF x s
