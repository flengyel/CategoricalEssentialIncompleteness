/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ArithmeticIndexedFamily

/-! # The constructed shared arithmetic proof object, without a fiber-initiality assumption -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates

namespace CategoricalEssentialIncompleteness.V46.ArithmeticIndexedFamilyChecks
open ArithmeticIndexedFamily

example (AxPA : Carrier) : IsInitial (algebra AxPA) := initial AxPA

example (AxPA : Carrier) :
    axiomIntroduction AxPA ≫ conclusion AxPA =
      ArithmeticIndexedAxioms.axioms AxPA ≫ prod.map (𝟙 parameter) sentenceInclusion :=
  axiomIntroduction_conclusion AxPA

example (AxPA : Carrier) (B : Endofunctor.Algebra (rules AxPA).inference)
    (f : algebra AxPA ⟶ B) : f = fold AxPA B := fold_unique AxPA B f

example (AxPA : Carrier) :
    sentenceTheory AxPA =
      (Subobject.pullback (prod.map (𝟙 parameter) sentenceInclusion)).obj (formulaTheory AxPA) :=
  sentenceTheory_pullback AxPA

end CategoricalEssentialIncompleteness.V46.ArithmeticIndexedFamilyChecks
