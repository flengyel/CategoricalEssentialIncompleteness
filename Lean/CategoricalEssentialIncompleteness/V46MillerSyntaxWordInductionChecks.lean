/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerSyntaxWordInduction


/-! # Statement checks in `V46MillerSyntaxWordInductionChecks` -/

@[expose] public section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax.Coding
namespace CategoricalEssentialIncompleteness.V46.Miller.Syntax.WordInduction.Checks
example (a b : RawPolynomial) (H : Bool → ℕ → Prop)
    (root : ∀ (formula : Bool) (u : ℕ),
      (rawCarrier (Postfix.carrier false a b) (Postfix.carrier true a b)
        (if formula then b else a)).val.Evalb ![u] →
      ChildHolds H (if formula then b else a) u →
        H formula (constructor formula (if formula then b else a) u)) :
    ∀ formula word,(Postfix.plainCarrier formula a b).val.Evalb (M := ℕ) ![word] → H formula word :=
  plain_word_induction a b H root
end CategoricalEssentialIncompleteness.V46.Miller.Syntax.WordInduction.Checks
