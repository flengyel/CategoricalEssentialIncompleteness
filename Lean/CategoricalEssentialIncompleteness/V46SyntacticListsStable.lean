/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SyntacticListsInitial
public import CategoricalEssentialIncompleteness.V46SyntacticListsTransport

/-! # Constructed parameter-stable list algebras for arbitrary Sigma-one predicates -/

@[expose] public section

noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates

namespace CategoricalEssentialIncompleteness.V46.SyntacticLists
variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]

/-- The canonical arithmetic list object satisfies both the base and
every parameter-slice initiality, proved from its coded evaluation graph. -/
def stableListAlgebra (V : PredicateCategory T) : StableListAlgebra V where
  algebra := algebra T V
  initial := Transport.initialOfTerminalParameters (algebra T V)
    (withParametersInitial T (⊤_ (PredicateCategory T)) V)
  stable P := withParametersInitial T P V

end CategoricalEssentialIncompleteness.V46.SyntacticLists
