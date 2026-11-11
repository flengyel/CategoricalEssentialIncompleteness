/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NumericalNamedLiteralEquivalence
public import CategoricalEssentialIncompleteness.V46SyntaxSubstitutionTransportMappedLists

/-! # Parameter-stable numerical syntax on literal tuple-code labels -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates

namespace CategoricalEssentialIncompleteness.V46.NumericalNamed
open SyntacticSyntax SyntacticLists.Transport SyntaxOperationsTransport
variable (V : NumericalTuples.Object) (σ π : ℕ → NumericalTuples.Object) (d : ℕ)
local notation "E" => literalEquivalence

def literalSourceSyntax : CategoricalSyntax (D := PredicateCategory 𝗧𝗔) (NumericalCoordinates.codedPredicate V)
    (fun n => NumericalCoordinates.codedPredicate (σ n))
    (fun n => NumericalCoordinates.codedPredicate (π n)) d :=
  plainCategoricalSyntax 𝗧𝗔 (NumericalCoordinates.codedPredicate V)
    (fun n => NumericalCoordinates.codedPredicate (σ n))
    (fun n => NumericalCoordinates.codedPredicate (π n)) d

def literalData := mappedPlainPostfixData 𝗧𝗔 (E)
  (SyntaxPolynomial.termExpression V σ d) (SyntaxPolynomial.formulaExpression V π d)

/-- The word labels are the specified tuple codes. The parameterized
initiality is the already proved mapped plain-parser initiality. -/
def literalCategoricalSyntax : CategoricalSyntax V σ π d where
  decidableVariables := ConcreteDecidableVariables.numerical V
  algebra := (literalData V σ π d).1
  initial := (literalData V σ π d).2.1
  stable := (literalData V σ π d).2.2
  lists := mappedStableListAlgebra (E) (NumericalCoordinates.codedPredicate V) V
    ((E).counitIso.app V) (literalSourceSyntax V σ π d).lists

local notation "S₀" => literalSourceSyntax V σ π d
local notation "S₁" => literalCategoricalSyntax V σ π d

/-- This comparison proves the constructor diagram; it is obtained from
the two initiality proofs, without assuming a code or fold equation. -/
opaque literalAlgebraIso : mappedSyntaxAlgebra (E) V σ π d (S₀) ≅ (S₁).algebra :=
  syntaxAlgebraIso (E) V σ π d (S₀) (S₁)

def literalTermIso : (E).functor.obj (S₀).algebra.a.1 ≅ (S₁).algebra.a.1 :=
  syntaxTermIso («S₁» := (S₁)) (E) V σ π d (S₀) (literalAlgebraIso V σ π d)

def literalFormulaIso : (E).functor.obj (S₀).algebra.a.2 ≅ (S₁).algebra.a.2 :=
  syntaxFormulaIso («S₁» := (S₁)) (E) V σ π d (S₀) (literalAlgebraIso V σ π d)

abbrev literal_constructor_comparison :=
  language_structure_comparison (E) V σ π d (S₀) (literalAlgebraIso V σ π d)

theorem literalListsEquality : (S₁).lists =
    mappedStableListAlgebra (E) ((E).inverse.obj V) V ((E).counitIso.app V) (S₀).lists := rfl

def literalListIso : (E).functor.obj (S₀).lists.algebra.carrier ≅ (S₁).lists.algebra.carrier :=
  syntaxListIso (E) V σ π d (S₀) (S₁) (literalListsEquality V σ π d)

/-- This is an isomorphism of algebras, with every constructor preserved,
to the original numerical realization. Neither carrier is replaced silently. -/
def literalOriginalAlgebraIso : (S₁).algebra ≅ (NumericalSyntax.categoricalSyntax V σ π d).algebra :=
  (S₁).initial.uniqueUpToIso (NumericalSyntax.categoricalSyntax V σ π d).initial

end CategoricalEssentialIncompleteness.V46.NumericalNamed
