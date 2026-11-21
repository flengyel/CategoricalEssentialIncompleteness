/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerSyntaxSimulation


/-! # The uniform evaluator preserves the original parser skeleton -/

@[expose] public section
noncomputable section
open CategoryTheory FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.V46
open CategoricalEssentialIncompleteness.V46.Miller
open CategoricalEssentialIncompleteness.V46.Miller.Syntax
variable {P : Uniform.Family} {R : Total.TotalCategory P} {X Y : Over R}
variable {p q : SyntaxPolynomial (Total.TotalCategory P)}
variable (hT : Raw.object R X Y p ⟶ X) (hF : Raw.object R X Y q ⟶ Y)

example {r word new : ℕ} (hn : new ∈ Raw.evaluation hT hF (Nat.pair r word)) :
    SyntacticSyntax.Coding.statusSort (SyntacticSyntax.Postfix.run (Raw.skeleton p) (Raw.skeleton q) word 1)=
      SyntacticSyntax.Coding.statusSort new := Raw.evaluation_sorts hT hF hn

example (formula : Bool) {r word new : ℕ}
    (hn : new ∈ Raw.evaluation hT hF (Nat.pair r word))
    (hword : SyntacticSyntax.Postfix.run (Raw.skeleton p) (Raw.skeleton q) word 1=
      adjoin (Nat.pair word (if formula then 1 else 0)) 0+1) :
    ∃ value,new=adjoin (Nat.pair value (if formula then 1 else 0)) 0+1 :=
  Raw.evaluation_singleton hT hF formula hn hword
