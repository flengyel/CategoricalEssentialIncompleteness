/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module
public import CategoricalEssentialIncompleteness.V46DiagramStableLists
public import CategoricalEssentialIncompleteness.V46DiagramDecidableVariables
public import CategoricalEssentialIncompleteness.V46NullarySyntaxTerms
public import CategoricalEssentialIncompleteness.V46CategoricalSubstitutionIdentity

/-! # Full categorical syntax, occurrences and substitution in the fork category -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness.V46.ForkCategoricalSyntax
open ForkFirstOrderFormula
variable (D : Object)

abbrev data := NumericalDiagramParameterStability.data
  (SyntaxPolynomial.termExpression numbers (fun _ => ⊥_ Object) 0)
  (SyntaxPolynomial.formulaExpression numbers (fun _ => D) 0)

/-- Definition A.1 for the printed language, with no function symbols,
arbitrary nullary predicates, and full numerical variables. -/
def categoricalSyntax : CategoricalSyntax numbers (fun _ => ⊥_ Object) (fun _ => D) 0 where
  decidableVariables := DiagramDecidableVariables.fork
  algebra := (data D).1
  initial := (data D).2.1
  stable := (data D).2.2
  lists := DiagramStableLists.stableListAlgebra numbers

def variableIso : numbers ≅ (categoricalSyntax D).algebra.a.1 := NullaryInterpretation.variableIso (categoricalSyntax D)
abbrev terms := (categoricalSyntax D).algebra.a.1
abbrev formulas := (categoricalSyntax D).algebra.a.2
abbrev lists := (categoricalSyntax D).lists.algebra.carrier
abbrev termOccurrences := (categoricalSyntax D).termOccurrences
abbrev formulaOccurrences := (categoricalSyntax D).formulaOccurrences
abbrev sentences := (categoricalSyntax D).sentenceObject
abbrev sentenceInclusion := (categoricalSyntax D).sentenceInclusion
abbrev termSubstitution := (categoricalSyntax D).termSubstitution
abbrev formulaSubstitutionOption := (categoricalSyntax D).formulaSubstitutionOption
abbrev admissibleSubstitution := (categoricalSyntax D).admissibleSubstitution
abbrev admissibleInclusion := (categoricalSyntax D).admissibleInclusion
abbrev formulaSubstitution := (categoricalSyntax D).formulaSubstitution

/-- Occurrence lists commute with every fork transition; no reflection
of atom-label equality is used. -/
theorem occurrences_natural {j k : WalkingSpan} (f : j ⟶ k) :
    (formulas D).map f ≫ (formulaOccurrences D).app k =
      (formulaOccurrences D).app j ≫ (lists D).map f :=
  (formulaOccurrences D).naturality f

theorem substitution_natural {j k : WalkingSpan} (f : j ⟶ k) :
    ((formulas D) ⨯ (categoricalSyntax D).substitutionParameters).map f ≫ (formulaSubstitutionOption D).app k =
      (formulaSubstitutionOption D).app j ≫ (OptionSyntax.obj (formulas D)).map f :=
  (formulaSubstitutionOption D).naturality f

theorem sentence_pullback : IsPullback (sentenceInclusion D)
    (pullback.snd (formulaOccurrences D) (categoricalSyntax D).lists.algebra.nil)
    (formulaOccurrences D) (categoricalSyntax D).lists.algebra.nil := IsPullback.of_hasPullback _ _

theorem substitution_pullback : IsPullback (admissibleInclusion D) (formulaSubstitution D)
    (formulaSubstitutionOption D) coprod.inr := (categoricalSyntax D).formulaSubstitution_isPullback

theorem substitution_original : (categoricalSyntax D).substitutionFold ≫
    (categoricalSyntax D).substitutionOriginalHom.f =
      𝟙 (constantFamily (categoricalSyntax D).substitutionParameters (terms D),
        constantFamily (categoricalSyntax D).substitutionParameters (formulas D)) :=
  (categoricalSyntax D).substitutionFold_original
end CategoricalEssentialIncompleteness.V46.ForkCategoricalSyntax
