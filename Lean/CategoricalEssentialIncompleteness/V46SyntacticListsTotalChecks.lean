/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SyntacticListsTotal

/-! # Checks for actual stable lists in both syntactic presentations -/

@[expose] public section

noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46
open SyntacticPredicates SyntacticLists

variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]

example (V : PredicateCategory T) : StableListAlgebra V := stableListAlgebra T V

example (V : TotalSplit T) : StableListAlgebra V := totalStableListAlgebra T V

example (V P : TotalSplit T) :
    IsInitial ((totalStableListAlgebra T V).algebra.withParameters P).asAlgebra :=
  (totalStableListAlgebra T V).stable P

example (V : TotalSplit T) : IsInitial (totalStableListAlgebra T V).algebra.asAlgebra :=
  (totalStableListAlgebra T V).initial
