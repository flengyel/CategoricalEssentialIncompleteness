/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ConcreteNamedComparisonSubstitutionHom


/-! # Statement checks in `V46ConcreteNamedComparisonSubstitutionHomChecks` -/

@[expose] public section
noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticLists
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax
open CategoricalEssentialIncompleteness.V46.ConcreteNamedComparison
namespace CategoricalEssentialIncompleteness.V46.ConcreteNamedComparison.SubstitutionHomChecks
variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
variable (V : PredicateCategory T) (σ π : ℕ → PredicateCategory T) (d : ℕ)
example : projectionSourceAlgebra T V V σ π d ⟶
    (categoricalSyntax T V σ π d).substitutionAlgebra :=
  computedSubstitutionHom T V σ π d
example : computedStatePair T V σ π d = (categoricalSyntax T V σ π d).substitutionFold :=
  computedStatePair_eq_fold T V σ π d
end CategoricalEssentialIncompleteness.V46.ConcreteNamedComparison.SubstitutionHomChecks
