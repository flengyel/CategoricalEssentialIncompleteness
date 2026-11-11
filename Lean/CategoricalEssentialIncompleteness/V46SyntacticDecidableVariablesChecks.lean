/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SyntacticDecidableVariables

/-! Internal equality for arbitrary variable predicates under only T extending PA. -/

@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoricalEssentialIncompleteness.V46
open SyntacticPredicates
variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]

example (V : PredicateCategory T) : DecidableVariables V :=
  SyntacticDecidableVariables.decidableVariables T V

example {C : PredicateCategory T} (V : PredicateCategory T) (a : C ⟶ V ⨯ V) :
    a ≫ SyntacticDecidableVariables.test T V = terminal.from C ≫ coprod.inr ↔
      a ≫ prod.fst = a ≫ prod.snd :=
  SyntacticDecidableVariables.test_true_iff T V a

example (V : PredicateCategory T) :
    IsPullback (prod.lift (𝟙 V) (𝟙 V)) (terminal.from V)
      (SyntacticDecidableVariables.decidableVariables T V).test
      (coprod.inr : ⊤_ (PredicateCategory T) ⟶
        (⊤_ (PredicateCategory T)) ⨿ (⊤_ (PredicateCategory T))) :=
  (SyntacticDecidableVariables.decidableVariables T V).diagonal
