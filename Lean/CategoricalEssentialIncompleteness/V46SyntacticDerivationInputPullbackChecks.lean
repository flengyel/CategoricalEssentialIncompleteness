/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SyntacticDerivationInputPullback

/-! The literal rule-input guards satisfy the actual categorical universal property. -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticDerivation
variable {T : ArithmeticTheory} [𝗣𝗔 ⪯ T] {A B F : Carrier}
variable (p : GraphMorphism T A F) (q : GraphMorphism T B F)
example : IsPullback (representedArrow T (RuleInput.label p q))
    (representedArrow T (RuleInput.children p q))
    (representedArrow T p) (representedArrow T q) := RuleInput.isPullback p q
example {F Q : PredicateCategory T} {N : ℕ} (R : RulePresentation F N)
    (q : GraphMorphism T Q F) (i : Fin (N + 1)) :
    IsPullback (representedArrow T (ruleInputLabel R q i))
      (representedArrow T (ruleInputChildren R q i))
      (representedArrow T (encodedPremises T R i))
      (representedArrow T (tupleMorphism q i.val)) :=
  RuleInput.isPullback (encodedPremises T R i) (tupleMorphism q i.val)
