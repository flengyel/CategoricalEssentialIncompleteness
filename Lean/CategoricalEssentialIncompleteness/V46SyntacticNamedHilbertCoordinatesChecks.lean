/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SyntacticNamedHilbertCoordinates


/-! # Statement checks in `V46SyntacticNamedHilbertCoordinatesChecks` -/

@[expose] public section
noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticLists
namespace CategoricalEssentialIncompleteness.V46.SyntacticNamedHilbert.CoordinatesChecks
open NamedFiniteSyntax NamedPostfixEncoding SyntacticSyntax
variable (σ π : ℕ → Carrier) (d : ℕ)
local notation "S" => plainCategoricalSyntax 𝗣𝗔 variableCarrier σ π d
local notation "Tm" => NamedFiniteSyntax.Term (Symbols σ) d
local notation "Fm" => NamedFiniteSyntax.Formula (Symbols σ) (Symbols π) d

example (x : ℕ) (φ : Fm) (t : Tm) (ψ : Fm)
    (hff : φ.FreeFor x t) (hs : φ.substitute x t = some ψ) :
    ∃ a : Obj 𝗣𝗔 ℕ (S).admissibleSubstitution,
      (F 𝗣𝗔 ℕ).map (S).admissibleInclusion a = substitutionPoint σ π d x φ t ∧
        (F 𝗣𝗔 ℕ).map (S).formulaSubstitution a = formulaPoint σ π d ψ :=
  substitution_instance σ π d x φ t ψ hff hs

example (φ ψ : Fm) :
    (F 𝗣𝗔 ℕ).map (S).implicationConstructor
      (pairPoint 𝗣𝗔 ℕ (formulaPoint σ π d φ) (formulaPoint σ π d ψ)) =
        formulaPoint σ π d (.imp φ ψ) := implication_point σ π d φ ψ
end CategoricalEssentialIncompleteness.V46.SyntacticNamedHilbert.CoordinatesChecks
