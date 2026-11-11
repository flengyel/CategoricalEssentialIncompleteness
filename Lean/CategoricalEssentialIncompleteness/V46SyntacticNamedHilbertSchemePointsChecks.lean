/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SyntacticNamedHilbertSchemePoints


/-! # Statement checks in `V46SyntacticNamedHilbertSchemePointsChecks` -/

@[expose] public section
noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticLists
namespace CategoricalEssentialIncompleteness.V46.SyntacticNamedHilbert.SchemePointsChecks
open NamedFiniteSyntax NamedPostfixEncoding SyntacticSyntax
variable (σ π : ℕ → Carrier) (d : ℕ)
local notation "S" => plainCategoricalSyntax 𝗣𝗔 variableCarrier σ π d
local notation "Tm" => NamedFiniteSyntax.Term (Symbols σ) d
local notation "Fm" => NamedFiniteSyntax.Formula (Symbols σ) (Symbols π) d

example (φ ψ : Fm) :
    (F 𝗣𝗔 ℕ).map (S).hilbertOne
      (pairPoint 𝗣𝗔 ℕ (formulaPoint σ π d φ) (formulaPoint σ π d ψ)) =
        formulaPoint σ π d (.imp φ (.imp ψ φ)) := hilbertOne_point σ π d φ ψ

example (φ ψ χ : Fm) :
    (F 𝗣𝗔 ℕ).map (S).hilbertTwo
      (pairPoint 𝗣𝗔 ℕ
        (pairPoint 𝗣𝗔 ℕ (formulaPoint σ π d φ) (formulaPoint σ π d ψ))
        (formulaPoint σ π d χ)) =
        formulaPoint σ π d (.imp (.imp φ (.imp ψ χ))
          (.imp (.imp φ ψ) (.imp φ χ))) := hilbertTwo_point σ π d φ ψ χ

example (φ ψ : Fm) :
    (F 𝗣𝗔 ℕ).map (S).hilbertThree
      (pairPoint 𝗣𝗔 ℕ (formulaPoint σ π d φ) (formulaPoint σ π d ψ)) =
        formulaPoint σ π d (.imp (.imp (.neg ψ) (.neg φ)) (.imp φ ψ)) :=
  hilbertThree_point σ π d φ ψ

example (t : Tm) :
    (F 𝗣𝗔 ℕ).map (S).hilbertReflexivity (termPoint σ π d t) =
      formulaPoint σ π d (.equal t t) := hilbertReflexivity_point σ π d t

example (x : ℕ) (φ : Fm) (t : Tm) :
    (F 𝗣𝗔 ℕ).map (S).instantiationInput
      (pairPoint 𝗣𝗔 ℕ (namePoint x)
        (pairPoint 𝗣𝗔 ℕ (formulaPoint σ π d φ) (termPoint σ π d t))) =
      substitutionPoint σ π d x φ t := instantiationInput_point σ π d x φ t

example (x : ℕ) (φ : Fm) (t : Tm) (ψ : Fm)
    (hff : φ.FreeFor x t) (hs : φ.substitute x t = some ψ) :
    ∃ p : Obj 𝗣𝗔 ℕ (S).instantiationParameters,
      (F 𝗣𝗔 ℕ).map (S).hilbertInstantiation p = formulaPoint σ π d (.imp (.all x φ) ψ) :=
  hilbertInstantiation_point σ π d x φ t ψ hff hs

example (x : ℕ) (φ ψ : Fm) (h : x ∉ φ.freeVariables) :
    ∃ p : Obj 𝗣𝗔 ℕ (S).distributionParameters,
      (F 𝗣𝗔 ℕ).map (S).hilbertDistribution p =
        formulaPoint σ π d (.imp (.all x (.imp φ ψ)) (.imp φ (.all x ψ))) :=
  hilbertDistribution_point σ π d x φ ψ h

example (x : ℕ) (φ : Fm) (u t : Tm) (ψ χ : Fm)
    (hfu : φ.FreeFor x u) (hft : φ.FreeFor x t)
    (hsu : φ.substitute x u = some ψ) (hst : φ.substitute x t = some χ) :
    ∃ p : Obj 𝗣𝗔 ℕ (S).equalitySchemeParameters,
      (F 𝗣𝗔 ℕ).map (S).hilbertEquality p =
        formulaPoint σ π d (.imp (.equal u t) (.imp ψ χ)) :=
  hilbertEquality_point σ π d x φ u t ψ χ hfu hft hsu hst
end CategoricalEssentialIncompleteness.V46.SyntacticNamedHilbert.SchemePointsChecks
