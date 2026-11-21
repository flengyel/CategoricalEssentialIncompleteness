/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerNamedProofImageSchemes
public import CategoricalEssentialIncompleteness.V46MillerNamedProofImageSubstitutionReflection
/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
public import CategoricalEssentialIncompleteness.V46MillerNamedProofImageSentenceReflection
public import CategoricalEssentialIncompleteness.V46MillerDerivationWordFirstOrderInduction
public import Mathlib.CategoryTheory.Limits.Types.Coproducts
public import Mathlib.Tactic.FinCases

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
namespace SchemeReflection
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

theorem one (p : (U).obj ((S).algebra.a.2 ⨯ (S).algebra.a.2)) :
    FiniteAxiomProof σ π d Γ (decodeFormula P σ π d ((U).map (S).hilbertOne p)) := by
  let φ := decodeFormula P σ π d ((U).map prod.fst p)
  let ψ := decodeFormula P σ π d ((U).map prod.snd p)
  have hp : pairPoint (formulaPoint P σ π d φ) (formulaPoint P σ π d ψ)=p := by
    simp only [φ,ψ,formulaPoint_decode,pairPoint_eta]
  rw [← hp,hilbertOne_point,decode_formulaPoint]
  exact FiniteAxiomProof.one σ π d φ ψ

theorem two (p : (U).obj (((S).algebra.a.2 ⨯ (S).algebra.a.2) ⨯ (S).algebra.a.2)) :
    FiniteAxiomProof σ π d Γ (decodeFormula P σ π d ((U).map (S).hilbertTwo p)) := by
  let φ := decodeFormula P σ π d ((U).map prod.fst ((U).map prod.fst p))
  let ψ := decodeFormula P σ π d ((U).map prod.snd ((U).map prod.fst p))
  let χ := decodeFormula P σ π d ((U).map prod.snd p)
  have hp : pairPoint (pairPoint (formulaPoint P σ π d φ) (formulaPoint P σ π d ψ))
      (formulaPoint P σ π d χ)=p := by
    simp only [φ,ψ,χ,formulaPoint_decode,pairPoint_eta]
  rw [← hp,hilbertTwo_point,decode_formulaPoint]
  exact FiniteAxiomProof.two σ π d φ ψ χ

theorem three (p : (U).obj ((S).algebra.a.2 ⨯ (S).algebra.a.2)) :
    FiniteAxiomProof σ π d Γ (decodeFormula P σ π d ((U).map (S).hilbertThree p)) := by
  let φ := decodeFormula P σ π d ((U).map prod.fst p)
  let ψ := decodeFormula P σ π d ((U).map prod.snd p)
  have hp : pairPoint (formulaPoint P σ π d φ) (formulaPoint P σ π d ψ)=p := by
    simp only [φ,ψ,formulaPoint_decode,pairPoint_eta]
  rw [← hp,hilbertThree_point,decode_formulaPoint]
  exact FiniteAxiomProof.three σ π d φ ψ

theorem reflexivity (p : (U).obj (S).algebra.a.1) :
    FiniteAxiomProof σ π d Γ (decodeFormula P σ π d ((U).map (S).hilbertReflexivity p)) := by
  let t := decodeTerm P σ π d p
  have hp : termPoint P σ π d t=p := termPoint_decode P σ π d p
  rw [← hp,hilbertReflexivity_point,decode_formulaPoint]
  exact FiniteAxiomProof.reflexivity σ π d t

end SchemeReflection
end CategoricalEssentialIncompleteness.V46.Miller.NamedProofImage
