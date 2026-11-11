/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerSyntaxUniformInduction


/-! # Statement checks in `V46MillerSyntaxUniformInductionChecks` -/

@[expose] public section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace CategoricalEssentialIncompleteness.V46.Miller.Syntax.Raw.Checks
example {P : Uniform.Family} (p q : SyntaxPolynomial (Total.TotalCategory P)) (H : Bool → ℕ → Prop)
    (root : ∀ (formula : Bool) (u : ℕ),
      u ∈ (carrier (uniformWords false p q) (uniformWords true p q) (if formula then q else p)).support →
      UniformChildren H (if formula then q else p) u →
        H formula (SyntacticSyntax.Coding.constructor formula (skeleton (if formula then q else p)) u)) :
    ∀ formula word,word ∈ (uniformWords formula p q).support → H formula word :=
  uniform_word_induction p q H root
end CategoricalEssentialIncompleteness.V46.Miller.Syntax.Raw.Checks
