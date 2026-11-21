/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ConcreteNamedComparisonOriginal


/-! # The original payload field is identified by stable initiality -/

@[expose] public section
noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticLists
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax
open CategoricalEssentialIncompleteness.V46.ConcreteNamedComparison
namespace CategoricalEssentialIncompleteness.V46.ConcreteNamedComparison.OriginalChecks
variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
variable (U V : PredicateCategory T) (σ π : ℕ → PredicateCategory T) (d : ℕ)
example : originalProjectionPair T U V σ π d = 𝟙 (projectionSourceAlgebra T U V σ π d).a :=
  originalProjectionPair_eq_id T U V σ π d
example : projectionSourceAlgebra T U V σ π d ⟶ projectionSourceAlgebra T U V σ π d :=
  originalProjectionHom T U V σ π d
end CategoricalEssentialIncompleteness.V46.ConcreteNamedComparison.OriginalChecks
