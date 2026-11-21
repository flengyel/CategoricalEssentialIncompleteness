/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SyntacticListsStable
public import CategoricalEssentialIncompleteness.V46SyntacticListsEquivalence
public import CategoricalEssentialIncompleteness.V46SyntacticPredicatesExtensive

/-! # Constructed stable lists in the total split syntactic category -/

@[expose] public section

noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates

namespace CategoricalEssentialIncompleteness.V46.SyntacticLists
variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]

/-- Every object of the total split category carries a stable list algebra, obtained from
its arbitrary Sigma-one predicate presentation. -/
def totalStableListAlgebra (V : TotalSplit T) : StableListAlgebra V :=
  Transport.mappedStableListAlgebra (predicateEquivalence T)
    ((predicateEquivalence T).inverse.obj V) V ((predicateEquivalence T).counitIso.app V)
      (stableListAlgebra T ((predicateEquivalence T).inverse.obj V))

end CategoricalEssentialIncompleteness.V46.SyntacticLists
