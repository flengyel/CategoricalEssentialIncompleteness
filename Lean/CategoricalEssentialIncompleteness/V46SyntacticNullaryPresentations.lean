/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SyntacticSyntaxPlain
public import CategoricalEssentialIncompleteness.V46SyntacticDerivationInitial
public import CategoricalEssentialIncompleteness.V46NullaryPresentationAdjunction

/-! # First-order presentations with propositional atoms in the arithmetic category -/

@[expose] public section
noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates

namespace CategoricalEssentialIncompleteness.V46.SyntacticDerivation
variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]

/-- Syntax with propositional atoms and an initial proof algebra for each axiom subobject. -/
def nullaryPresentations (V : PredicateCategory T) : NullaryPresentations V where
  syntaxData X := SyntacticSyntax.plainCategoricalSyntax T V
    (fun _ => ⊥_ (PredicateCategory T)) (fun _ => X) 0
  proofs X A := derivationAlgebra T
    ((SyntacticSyntax.plainCategoricalSyntax T V
      (fun _ => ⊥_ (PredicateCategory T)) (fun _ => X) 0).logicalRules A.arrow)
  initial X A := derivationInitial T
    ((SyntacticSyntax.plainCategoricalSyntax T V
      (fun _ => ⊥_ (PredicateCategory T)) (fun _ => X) 0).logicalRules A.arrow)

end CategoricalEssentialIncompleteness.V46.SyntacticDerivation
