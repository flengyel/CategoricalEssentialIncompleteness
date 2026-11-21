/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerNamedProofImageLogicalReflection

/-! # All seven-scheme parameters yield finite Hilbert proofs from Γ

The target success points prove both free-for conditions and their literal
substitution results. The distribution parameter is reflected through the false
classifier and the PA false fiber. No logical scheme coverage, source axiom
admissibility or semantic validity premise is supplied.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.RestrictionCategory CategoryTheory.Limits
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
namespace CategoricalEssentialIncompleteness.V46.Miller.NamedProofImage
namespace V46MillerNamedProofImageLogicalReflectionChecks
open CategoricalEssentialIncompleteness.V46.Miller.NamedProofImage.SchemeReflection
open NamedFiniteSyntax NamedPostfixEncoding
open Points
variable (P : Uniform.Family) (σ π : ℕ → Carrier) (d : ℕ) (Γ : Set ℕ)
local notation "F" => Syntax.predicateFunctor P
local notation "U" => Total.underlying (P:=P)
local notation "N" => PredicateInterpretation.functor 𝗣𝗔 ℕ
local notation "V" => (variableCarrier : PredicateCategory 𝗣𝗔)
local notation "S₀" => NamedSyntaxComparison.sourceSyntax (V) σ π d
local notation "S" => syntaxData P σ π d
local notation "Fm" => NamedFiniteSyntax.Formula (Symbols σ) (Symbols π) d

example (p : (U).obj ((S).algebra.a.2 ⨯ (S).algebra.a.2)) :
    FiniteAxiomProof σ π d Γ (decodeFormula P σ π d ((U).map (S).hilbertOne p)) := one P σ π d Γ p

example (p : (U).obj (((S).algebra.a.2 ⨯ (S).algebra.a.2) ⨯ (S).algebra.a.2)) :
    FiniteAxiomProof σ π d Γ (decodeFormula P σ π d ((U).map (S).hilbertTwo p)) := two P σ π d Γ p

example (p : (U).obj ((S).algebra.a.2 ⨯ (S).algebra.a.2)) :
    FiniteAxiomProof σ π d Γ (decodeFormula P σ π d ((U).map (S).hilbertThree p)) := three P σ π d Γ p

example (p : (U).obj (S).algebra.a.1) :
    FiniteAxiomProof σ π d Γ (decodeFormula P σ π d ((U).map (S).hilbertReflexivity p)) := reflexivity P σ π d Γ p

end V46MillerNamedProofImageLogicalReflectionChecks
end CategoricalEssentialIncompleteness.V46.Miller.NamedProofImage
