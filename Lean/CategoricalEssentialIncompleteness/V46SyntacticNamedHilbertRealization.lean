/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SyntacticNamedHilbertSchemePoints
public import CategoricalEssentialIncompleteness.V46SyntacticGeneratedAxioms

/-! # Literal finite named proofs in the constructed Γ derivation object

Only standard finite named trees are used here. Their rule parameters
are actual points of the constructed scheme domains; no comparison
with a different deductive calculus is assumed.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticLists
namespace CategoricalEssentialIncompleteness.V46.SyntacticNamedHilbert
open SyntacticSyntax NamedFiniteSyntax NamedPostfixEncoding ConcreteNamedComparison
variable (σ π : ℕ → Carrier) (d : ℕ) (Γ : Carrier)
local notation "S" => plainCategoricalSyntax 𝗣𝗔 variableCarrier σ π d
local notation "Tm" => NamedFiniteSyntax.Term (Symbols σ) d
local notation "Fm" => NamedFiniteSyntax.Formula (Symbols σ) (Symbols π) d
local notation "G" => F 𝗣𝗔 ℕ
local notation "D" => SyntacticFiniteNamedDerivations.Derives 𝗣𝗔 variableCarrier σ π d Γ ℕ

/-- Literal enumerated sentencehood supplies a point of the actual
filtered axiom domain. Its word coordinate is the original formula. -/
theorem axiom_point (φ : Fm) (henum : Γ.val.Evalb ![formulaCode φ])
    (hsent : φ.freeVariables = []) :
    ∃ p : Obj 𝗣𝗔 ℕ (SyntacticAxiomPredicates.axiomCarrier 𝗣𝗔 variableCarrier σ π d Γ),
      (G).map (SyntacticAxiomPredicates.axioms 𝗣𝗔 variableCarrier σ π d Γ ≫
        (S).sentenceInclusion) p = formulaPoint σ π d φ := by
  have hsource : (Postfix.plainCarrier true (termPolynomial σ d) (formulaPolynomial π d)).val.Evalb
      ![formulaCode φ] := by
    simpa only [formulaPoint_value,termPolynomial,formulaPolynomial] using (formulaPoint σ π d φ).property
  have hs : (literalSentenceCarrier 𝗣𝗔 variableCarrier σ π d).val.Evalb ![formulaCode φ] :=
    (literalSentenceCarrier_eval 𝗣𝗔 variableCarrier σ π d ℕ _).mpr
      ⟨hsource,(@sentence_formulaCode_iff σ π d φ).mpr hsent⟩
  let p : Obj 𝗣𝗔 ℕ (SyntacticAxiomPredicates.axiomCarrier 𝗣𝗔 variableCarrier σ π d Γ) :=
    ⟨formulaCode φ,(SyntacticAxiomPredicates.axiomCarrier_literal
      𝗣𝗔 variableCarrier σ π d ℕ Γ _).mpr ⟨henum,hs⟩⟩
  refine ⟨p,Subtype.ext ?_⟩
  exact (SyntacticAxiomPredicates.axioms_formula_value
    𝗣𝗔 variableCarrier σ π d ℕ Γ p).trans (formulaPoint_value σ π d φ).symm

/-- Each constructor of the single literal named calculus is realized
using its genuine seven-scheme parameter or original ordered rule label. -/
theorem native_derives {φ : Fm} (h : Derives σ π d Γ φ) : D (formulaPoint σ π d φ) := by
  induction h with
  | «axiom» φ he hs =>
      obtain ⟨p,hp⟩ := axiom_point σ π d Γ φ he hs
      have h := SyntacticFiniteNamedDerivations.nonlogical_axiom
        𝗣𝗔 variableCarrier σ π d Γ ℕ p
      rw [hp] at h
      exact h
  | one φ ψ =>
      have h := SyntacticFiniteNamedDerivations.logical_scheme 𝗣𝗔 variableCarrier σ π d Γ ℕ
        0 (pairPoint 𝗣𝗔 ℕ (formulaPoint σ π d φ) (formulaPoint σ π d ψ))
      change D ((G).map (S).hilbertOne _) at h
      rw [hilbertOne_point] at h
      exact h
  | two φ ψ χ =>
      have h := SyntacticFiniteNamedDerivations.logical_scheme 𝗣𝗔 variableCarrier σ π d Γ ℕ
        1 (pairPoint 𝗣𝗔 ℕ
          (pairPoint 𝗣𝗔 ℕ (formulaPoint σ π d φ) (formulaPoint σ π d ψ))
          (formulaPoint σ π d χ))
      change D ((G).map (S).hilbertTwo _) at h
      rw [hilbertTwo_point] at h
      exact h
  | three φ ψ =>
      have h := SyntacticFiniteNamedDerivations.logical_scheme 𝗣𝗔 variableCarrier σ π d Γ ℕ
        2 (pairPoint 𝗣𝗔 ℕ (formulaPoint σ π d φ) (formulaPoint σ π d ψ))
      change D ((G).map (S).hilbertThree _) at h
      rw [hilbertThree_point] at h
      exact h
  | instantiation x φ t ψ hff hs =>
      obtain ⟨p,hp⟩ := hilbertInstantiation_point σ π d x φ t ψ hff hs
      have h := SyntacticFiniteNamedDerivations.logical_scheme 𝗣𝗔 variableCarrier σ π d Γ ℕ 3 p
      change D ((G).map (S).hilbertInstantiation p) at h
      rw [hp] at h
      exact h
  | distribution x φ ψ hx =>
      obtain ⟨p,hp⟩ := hilbertDistribution_point σ π d x φ ψ hx
      have h := SyntacticFiniteNamedDerivations.logical_scheme 𝗣𝗔 variableCarrier σ π d Γ ℕ 4 p
      change D ((G).map (S).hilbertDistribution p) at h
      rw [hp] at h
      exact h
  | reflexivity t =>
      have h := SyntacticFiniteNamedDerivations.logical_scheme 𝗣𝗔 variableCarrier σ π d Γ ℕ
        5 (termPoint σ π d t)
      change D ((G).map (S).hilbertReflexivity _) at h
      rw [hilbertReflexivity_point] at h
      exact h
  | equality x φ u t ψ χ hfu hft hsu hst =>
      obtain ⟨p,hp⟩ := hilbertEquality_point σ π d x φ u t ψ χ hfu hft hsu hst
      have h := SyntacticFiniteNamedDerivations.logical_scheme 𝗣𝗔 variableCarrier σ π d Γ ℕ 6 p
      change D ((G).map (S).hilbertEquality p) at h
      rw [hp] at h
      exact h
  | @generalization x φ h ih =>
      let p := pairPoint 𝗣𝗔 ℕ (namePoint x) (formulaPoint σ π d φ)
      have hp : D ((G).map prod.snd p) := by
        rw [pairPoint_snd]
        exact ih
      have h := SyntacticFiniteNamedDerivations.generalization 𝗣𝗔 variableCarrier σ π d Γ ℕ p hp
      erw [quantifier_point] at h
      exact h
  | @modusPonens φ ψ hφ himp ihφ ihimp =>
      let p := pairPoint 𝗣𝗔 ℕ (formulaPoint σ π d φ) (formulaPoint σ π d ψ)
      have hp : D ((G).map prod.fst p) := by
        rw [pairPoint_fst]
        exact ihφ
      have hi : D ((G).map (S).implicationConstructor p) := by
        rw [implication_point]
        exact ihimp
      have h := SyntacticFiniteNamedDerivations.modus_ponens
        𝗣𝗔 variableCarrier σ π d Γ ℕ p hp hi
      erw [pairPoint_snd] at h
      exact h

/-- A literal finite named proof supplies an actual point of the
constructed Γ proof object with precisely the literal conclusion word. -/
theorem native_realizes {φ : Fm} (h : Derives σ π d Γ φ) :
    ∃ p : Obj 𝗣𝗔 ℕ (SyntacticGeneratedAxioms.proofs 𝗣𝗔 variableCarrier σ π d Γ).a.left,
      ((G).map (SyntacticGeneratedAxioms.conclusion 𝗣𝗔 variableCarrier σ π d Γ) p).val =
        formulaCode φ := by
  obtain ⟨p,hp⟩ := SyntacticFiniteNamedDerivations.realizes
    𝗣𝗔 variableCarrier σ π d Γ ℕ (native_derives σ π d Γ h)
  exact ⟨p,(congrArg Subtype.val hp).trans (formulaPoint_value σ π d φ)⟩

/-- Sentence conclusions enter the literal selected theorem program.
Open derived formulas are not reclassified as sentences. -/
theorem native_sentence_theorem {φ : Fm} (h : Derives σ π d Γ φ)
    (hs : φ.freeVariables = []) :
    (SyntacticGeneratedAxioms.literalTheoremCarrier 𝗣𝗔 variableCarrier σ π d Γ).val.Evalb
      ![formulaCode φ] := by
  obtain ⟨p,hp⟩ := native_realizes σ π d Γ h
  apply (SyntacticGeneratedAxioms.literalTheoremCarrier_model
    𝗣𝗔 variableCarrier σ π d ℕ Γ _).mpr
  apply (SyntacticGeneratedAxioms.theoremCarrier_model
    𝗣𝗔 variableCarrier σ π d ℕ Γ _).mpr
  refine ⟨?_,p,hp⟩
  apply (literalSentenceCarrier_eval 𝗣𝗔 variableCarrier σ π d ℕ _).mpr
  constructor
  · simpa only [formulaPoint_value,termPolynomial,formulaPolynomial] using (formulaPoint σ π d φ).property
  · exact (@sentence_formulaCode_iff σ π d φ).mpr hs

/-- A finite literal named sentence proof yields its individual PA proof
in the actual selected positive theorem predicate. This is Sigma-one
completeness, rather than an identification of deductive calculi. -/
theorem native_sentence_numeral_PA {φ : Fm} (h : Derives σ π d Γ φ)
    (hs : φ.freeVariables = []) :
    𝗣𝗔 ⊢ ((SyntacticGeneratedAxioms.literalTheoremCarrier
      𝗣𝗔 variableCarrier σ π d Γ).val/[(↑(formulaCode φ) : ArithmeticSemiterm Empty 0)] :
        ArithmeticSentence) := by
  let : 𝗥₀ ⪯ 𝗣𝗔 := WeakerThan.trans (𝓣 := 𝗣𝗔⁻) inferInstance inferInstance
  apply sigma_one_completeness (by simp)
  simpa [models_iff] using native_sentence_theorem σ π d Γ h hs

end CategoricalEssentialIncompleteness.V46.SyntacticNamedHilbert
