/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ArithmeticIndexedRules

/-! # Parameter-preserving rule data and constructed family initiality -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates

namespace CategoricalEssentialIncompleteness.V46.ArithmeticIndexedRulesChecks
open ArithmeticIndexedRules
variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
variable (E : TotalSplit T) {V F L S A : TotalSplit T}
variable (logical : L ⟶ F) (sentence : S ⟶ F) (axioms : A ⟶ E ⨯ S)
  (all : V ⨯ F ⟶ F) (imp : F ⨯ F ⟶ F)

example : IsInitial (algebra T E logical sentence axioms all imp) :=
  initial T E logical sentence axioms all imp

example :
    (rules E logical sentence axioms all imp).premises 2 ≫ prod.fst ≫ prod.fst =
      (rules E logical sentence axioms all imp).conclusion 2 ≫ prod.fst ∧
    (rules E logical sentence axioms all imp).premises 2 ≫ prod.snd ≫ prod.fst =
      (rules E logical sentence axioms all imp).conclusion 2 ≫ prod.fst :=
  ⟨binary_first_parameter E logical sentence axioms all imp,
    binary_second_parameter E logical sentence axioms all imp⟩

example :
    sentenceTheory T E logical sentence axioms all imp =
      (Subobject.pullback (prod.map (𝟙 E) sentence)).obj
        (formulaTheory T E logical sentence axioms all imp) :=
  sentenceTheory_pullback T E logical sentence axioms all imp

end CategoricalEssentialIncompleteness.V46.ArithmeticIndexedRulesChecks
