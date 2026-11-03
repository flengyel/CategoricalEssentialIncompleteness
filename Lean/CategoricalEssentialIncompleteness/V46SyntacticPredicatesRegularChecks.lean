/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46SyntacticPredicatesRegular

/-! # Explicit regularity statements with their effective hypotheses -/

noncomputable section

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates

namespace CategoricalEssentialIncompleteness.V46.SyntacticPredicates.RegularChecks

variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]

example : Regular (PredicateCategory T) := inferInstance

example : Regular (TotalSplit T) := inferInstance

example {C D : PredicateCategory T} (f : C ⟶ D) [IsRegularEpi f] :
    IsSplitEpi f := regularEpi_split T f

example {X Y : TotalSplit T} (f : X ⟶ Y) [StrongEpi f] :
    IsSplitEpi f := totalSplit_strongEpi_split T f

end CategoricalEssentialIncompleteness.V46.SyntacticPredicates.RegularChecks
