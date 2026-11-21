/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerNamedProofImageSchemePoints

/-! # Seven scheme witnesses in the uniform parameter objects -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.RestrictionCategory CategoryTheory.Limits
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
namespace CategoricalEssentialIncompleteness.V46.Miller.NamedProofImage
namespace SchemePointsChecks
open CategoricalEssentialIncompleteness.V46.Miller.NamedProofImage.Points
open NamedFiniteSyntax NamedPostfixEncoding
variable (P : Uniform.Family) (σ π : ℕ → Carrier) (d : ℕ)
local notation "F" => Syntax.predicateFunctor P
local notation "U" => Total.underlying (P:=P)
local notation "N" => PredicateInterpretation.functor 𝗣𝗔 ℕ
local notation "V" => (variableCarrier : PredicateCategory 𝗣𝗔)
local notation "S₀" => NamedSyntaxComparison.sourceSyntax (V) σ π d
local notation "S" => syntaxData P σ π d
local notation "Tm" => NamedFiniteSyntax.Term (Symbols σ) d
local notation "Fm" => NamedFiniteSyntax.Formula (Symbols σ) (Symbols π) d

example (x : ℕ) (φ : Fm) (t₀ : Tm) (ψ : Fm)
    (hff : φ.FreeFor x t₀) (hs : φ.substitute x t₀=some ψ) :
    ∃ a : (U).obj (S).admissibleSubstitution,
      (U).map (S).admissibleInclusion a=substitutionPoint P σ π d x φ t₀ ∧
        (U).map (S).formulaSubstitution a=formulaPoint P σ π d ψ := substitution_instance P σ π d x φ t₀ ψ hff hs

example (φ ψ : Fm) :
    (U).map (S).hilbertOne
      (pairPoint (formulaPoint P σ π d φ) (formulaPoint P σ π d ψ)) =
        formulaPoint P σ π d (.imp φ (.imp ψ φ)) := hilbertOne_point P σ π d φ ψ

example (φ ψ χ : Fm) :
    (U).map (S).hilbertTwo
      (pairPoint
        (pairPoint (formulaPoint P σ π d φ) (formulaPoint P σ π d ψ))
        (formulaPoint P σ π d χ)) =
        formulaPoint P σ π d (.imp (.imp φ (.imp ψ χ))
          (.imp (.imp φ ψ) (.imp φ χ))) := hilbertTwo_point P σ π d φ ψ χ

example (φ ψ : Fm) :
    (U).map (S).hilbertThree
      (pairPoint (formulaPoint P σ π d φ) (formulaPoint P σ π d ψ)) =
        formulaPoint P σ π d (.imp (.imp (.neg ψ) (.neg φ)) (.imp φ ψ)) := hilbertThree_point P σ π d φ ψ

example (t : Tm) :
    (U).map (S).hilbertReflexivity (termPoint P σ π d t) =
      formulaPoint P σ π d (.equal t t) := hilbertReflexivity_point P σ π d t

example (x : ℕ) (φ : Fm) (t : Tm) :
    (U).map (S).instantiationInput
      (pairPoint (namePoint P x)
        (pairPoint (formulaPoint P σ π d φ) (termPoint P σ π d t))) =
      substitutionPoint P σ π d x φ t := instantiationInput_point P σ π d x φ t

example (x : ℕ) (φ : Fm) (t : Tm) (ψ : Fm)
    (hff : φ.FreeFor x t) (hs : φ.substitute x t = some ψ) :
    ∃ z : (U).obj (S).instantiationParameters,
      (U).map (S).hilbertInstantiation z = formulaPoint P σ π d (.imp (.all x φ) ψ) := hilbertInstantiation_point P σ π d x φ t ψ hff hs

end SchemePointsChecks
end CategoricalEssentialIncompleteness.V46.Miller.NamedProofImage
