/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SyntacticDerivationEncoderIsos

/-! The original chosen finite powers are actually isomorphic to literal premise tuples. -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticDerivation
variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] (F : PredicateCategory T) (n : ℕ)
example : IsIso (representedArrow T (finitePowerEncoder T F n)) := finitePowerEncoder_isIso T F n
example : CategoryTheory.Iso (C := PredicateCategory T)
    (finitePower (D := PredicateCategory T) F n) (tupleCarrier F n) :=
  finitePowerIso T F n
