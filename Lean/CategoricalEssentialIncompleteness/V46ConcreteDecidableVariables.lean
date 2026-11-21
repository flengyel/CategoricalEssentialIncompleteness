/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46DecidableVariablesTransport
public import CategoricalEssentialIncompleteness.V46SyntacticDecidableVariables
public import CategoricalEssentialIncompleteness.V46NumericalStableLists

/-! # Internal decidable equality in the syntactic total and numerical categories -/

@[expose] public section

noncomputable section
open CategoryTheory
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment

namespace CategoricalEssentialIncompleteness.V46.ConcreteDecidableVariables

variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]

/-- The predicate equivalence transports the diagonal pullback to every object of the
total restriction splitting. -/
def total (V : SyntacticPredicates.TotalSplit T) : DecidableVariables V :=
  let E := SyntacticPredicates.predicateEquivalence T
  DecidableVariables.Transport.mapped E
    (SyntacticDecidableVariables.decidableVariables T (E.inverse.obj V))
    V (E.counitIso.app V)

/-- The full standard theory compares ordinary computable total maps with the finite-tuple
numerical category. -/
def numerical (V : NumericalTuples.Object) : DecidableVariables V :=
  let E := NumericalStableLists.numericalEquivalence
  DecidableVariables.Transport.mapped E (total 𝗧𝗔 (E.inverse.obj V))
    V (E.counitIso.app V)

end CategoricalEssentialIncompleteness.V46.ConcreteDecidableVariables
