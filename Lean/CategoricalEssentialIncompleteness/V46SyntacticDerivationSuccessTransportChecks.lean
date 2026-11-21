/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SyntacticDerivationSuccessTransport

/-! The total split carrier is the image of an explicit Sigma-one word predicate. -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticDerivation.SuccessTransport
variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] {W F : TotalSplit T} (v : W ⟶ OptionSyntax.obj F)
example : Carrier := carrier T v
example : codeObject T v = (predicateEquivalence T).functor.obj (carrier T v) := rfl
example : IsPullback (inclusion T v) (conclusion T v) v
    (coprod.inr : F ⟶ OptionSyntax.obj F) := isPullback T v
example : Over.mk (conclusion T v) ≅
    (Over.pullback (coprod.inr : F ⟶ OptionSyntax.obj F)).obj (Over.mk v) := overIso T v
