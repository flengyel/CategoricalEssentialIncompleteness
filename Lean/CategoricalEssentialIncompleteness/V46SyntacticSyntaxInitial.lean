/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46SyntacticSyntaxUnique
import CategoricalEssentialIncompleteness.V46SyntacticSyntaxTerminal
import CategoricalEssentialIncompleteness.V46SyntacticPredicatesRegular
import CategoricalEssentialIncompleteness.V46SyntacticDecidableVariables
import CategoricalEssentialIncompleteness.V46SyntacticListsStable

/-! # The actual parameter-stable initial algebra on literal postfix syntax -/

noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates

namespace CategoricalEssentialIncompleteness.V46.SyntacticSyntax
variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]

/-- Every actual algebra over an arbitrary parameter receives exactly
one algebra morphism from the canonical postfix algebra over that parameter. -/
def withParametersInitial (P : PredicateCategory T)
    (a b : SyntaxPolynomial (PredicateCategory T)) :
    IsInitial (SyntaxPolynomial.algebraWithParameters a b (postfixAlgebra T a b) P) :=
  IsInitial.ofUniqueHom (fun B => foldHom T a b B)
    (fun B H => foldHom_unique T a b B H)

def postfixInitial (a b : SyntaxPolynomial (PredicateCategory T)) :
    IsInitial (postfixAlgebra T a b) :=
  initialOfTerminalParameters a b (postfixAlgebra T a b)
    (withParametersInitial T (⊤_ (PredicateCategory T)) a b)

/-- This realizes all fields of Definition A.1 at arbitrary variable,
function-symbol and relation-symbol predicates and finite arity bound. -/
def categoricalSyntax (V : PredicateCategory T) (σ π : ℕ → PredicateCategory T) (d : ℕ) :
    CategoricalSyntax V σ π d where
  decidableVariables := SyntacticDecidableVariables.decidableVariables T V
  algebra := postfixAlgebra T (SyntaxPolynomial.termExpression V σ d)
    (SyntaxPolynomial.formulaExpression V π d)
  initial := postfixInitial T (SyntaxPolynomial.termExpression V σ d)
    (SyntaxPolynomial.formulaExpression V π d)
  stable P := withParametersInitial T P (SyntaxPolynomial.termExpression V σ d)
    (SyntaxPolynomial.formulaExpression V π d)
  lists := SyntacticLists.stableListAlgebra T V

end CategoricalEssentialIncompleteness.V46.SyntacticSyntax
