/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SyntaxMappedListOccurrenceComparison
public import CategoricalEssentialIncompleteness.V46SyntacticSyntaxPlainTotal

/-! # Concrete occurrence transport in the total restriction splitting -/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
namespace CategoricalEssentialIncompleteness.V46.ConcreteSyntaxOperationsTransport
open SyntacticSyntax SyntacticLists.Transport SyntaxOperationsTransport
variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
variable (V : TotalSplit T) (σ π : ℕ → TotalSplit T) (d : ℕ)
local notation "E" => predicateEquivalence T

def sourceSyntax : CategoricalSyntax ((E).inverse.obj V)
    (fun n => (E).inverse.obj (σ n)) (fun n => (E).inverse.obj (π n)) d :=
  plainCategoricalSyntax T ((E).inverse.obj V)
    (fun n => (E).inverse.obj (σ n)) (fun n => (E).inverse.obj (π n)) d

def targetSyntax : CategoricalSyntax V σ π d := plainTotalCategoricalSyntax T V σ π d
local notation "S₀" => sourceSyntax T V σ π d
local notation "S₁" => targetSyntax T V σ π d

/-- Both sides are already proved initial algebras of the polynomial; their comparison
includes all constructor equations. -/
def algebraIso : mappedSyntaxAlgebra (E) V σ π d (S₀) ≅ (S₁).algebra :=
  syntaxAlgebraIso (E) V σ π d (S₀) (S₁)

def termIso : (E).functor.obj (S₀).algebra.a.1 ≅ (S₁).algebra.a.1 :=
  syntaxTermIso («S₁» := (S₁)) (E) V σ π d (S₀) (algebraIso T V σ π d)

def formulaIso : (E).functor.obj (S₀).algebra.a.2 ≅ (S₁).algebra.a.2 :=
  syntaxFormulaIso («S₁» := (S₁)) (E) V σ π d (S₀) (algebraIso T V σ π d)

/-- The equality is a fact about the constructed list-algebra record;
it does not assert a fold equation or identify an inverse code chart. -/
theorem targetListsEquality : (S₁).lists =
    mappedStableListAlgebra (E) ((E).inverse.obj V) V ((E).counitIso.app V) (S₀).lists := rfl

def listIso : (E).functor.obj (S₀).lists.algebra.carrier ≅ (S₁).lists.algebra.carrier :=
  syntaxListIso (E) V σ π d (S₀) (S₁) (targetListsEquality T V σ π d)

/-- The predicate unfolds to the term occurrence diagram. All list-operation equations and
fold uniqueness were proved before E was specialized to the concrete predicate
equivalence. -/
theorem termOccurrences_comparison :
    termOccurrenceComparison (E) V σ π d (S₀) (S₁)
      (targetListsEquality T V σ π d) (algebraIso T V σ π d) :=
  mapped_termOccurrence_comparison (E) V σ π d (S₀) (S₁)
    (targetListsEquality T V σ π d) (algebraIso T V σ π d)

theorem formulaOccurrences_comparison :
    formulaOccurrenceComparison (E) V σ π d (S₀) (S₁)
      (targetListsEquality T V σ π d) (algebraIso T V σ π d) :=
  mapped_formulaOccurrence_comparison (E) V σ π d (S₀) (S₁)
    (targetListsEquality T V σ π d) (algebraIso T V σ π d)

end CategoricalEssentialIncompleteness.V46.ConcreteSyntaxOperationsTransport
