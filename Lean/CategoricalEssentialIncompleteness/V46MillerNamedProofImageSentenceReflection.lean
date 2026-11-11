/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerFiniteAxiomProofs
public import CategoricalEssentialIncompleteness.V46MillerNamedProofImageDecoding
public import CategoricalEssentialIncompleteness.V46NamedPlainDistributionSemantics

/-! # Literal sentence and Gamma-leaf reflection

Every nonlogical leaf is recovered from the actual sentence-axiom
pullback. Its finite support is the singleton of the original formula
word. No proof is selected from an arbitrary family of nonempty fibers.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.RestrictionCategory CategoryTheory.Limits
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
namespace CategoricalEssentialIncompleteness.V46.Miller.NamedProofImage
open NamedFiniteSyntax NamedPostfixEncoding
variable (P : Uniform.Family) (σ π : ℕ → Carrier) (d : ℕ)
local notation "F" => Syntax.predicateFunctor P
local notation "U" => (Total.underlying (P := P))
local notation "N" => PredicateInterpretation.functor 𝗣𝗔 ℕ
local notation "V" => (variableCarrier : PredicateCategory 𝗣𝗔)
local notation "S₀" => NamedSyntaxComparison.sourceSyntax (V) σ π d
local notation "S" => syntaxData P σ π d
local notation "Fm" => NamedFiniteSyntax.Formula (Symbols σ) (Symbols π) d
local notation "ifm" => NamedSyntaxComparison.formulaIso P (V) σ π d
local notation "is" => NamedSyntaxComparison.sentenceIso P (V) σ π d

theorem sentence_inclusion_closed (s : (U).obj (S).sentenceObject) :
    (decodeFormula P σ π d ((U).map (S).sentenceInclusion s)).freeVariables=[] := by
  let φ := decodeFormula P σ π d ((U).map (S).sentenceInclusion s)
  let s₀ := (sourcePointEquiv P (S₀).sentenceObject).symm ((U).map (is).hom s)
  have hs₀ : sourcePoint P _ s₀=(U).map (is).hom s :=
    (sourcePointEquiv P _).apply_symm_apply _
  have hf : (N).map (S₀).sentenceInclusion s₀=SyntacticNamedHilbert.formulaPoint σ π d φ := by
    apply (sourcePointEquiv P (S₀).algebra.a.2).injective
    change sourcePoint P (S₀).algebra.a.2 ((N).map (S₀).sentenceInclusion s₀) =
      sourcePoint P (S₀).algebra.a.2 (SyntacticNamedHilbert.formulaPoint σ π d φ)
    rw [← map_sourcePoint,hs₀,← CategoryTheory.Functor.map_comp_apply,
      NamedSyntaxComparison.sentenceIso_inclusion,CategoryTheory.Functor.map_comp_apply]
    exact (congrArg ((U).map (ifm).hom) (formulaPoint_decode P σ π d ((U).map (S).sentenceInclusion s))).symm.trans
      (formulaPoint_chart P σ π d φ)
  have hs : (ConcreteNamedComparison.literalSentenceCarrier 𝗣𝗔 (V) σ π d).val.Evalb
      (M := ℕ) ![formulaCode φ] :=
    (SyntacticGeneratedAxioms.sentence_points 𝗣𝗔 (V) σ π d ℕ (formulaCode φ)).mpr
      ⟨s₀,(congrArg Subtype.val hf).trans (SyntacticNamedHilbert.formulaPoint_value σ π d φ)⟩
  exact (@NamedPostfixEncoding.sentence_formulaCode_iff σ π d φ).mp
    ((ConcreteNamedComparison.literalSentenceCarrier_eval 𝗣𝗔 (V) σ π d ℕ (formulaCode φ)).mp hs).2

variable (Γ : Set ℕ) (hΓ : Uniform.Enumerable P (· ∈ Γ))

theorem axiom_word_member (a : (U).obj (axiomCarrier P σ π d Γ hΓ)) :
    formulaCode (decodeFormula P σ π d
      ((U).map (axioms P σ π d Γ hΓ ≫ (S).sentenceInclusion) a))∈Γ := by
  obtain ⟨w,hw,hΓw⟩ := (SentenceAxiomPullbacks.axCarrier_support (sentenceWord P σ π d) Γ hΓ a.val).mp a.property
  let s := (U).map (axioms P σ π d Γ hΓ) a
  let φ := (U).map (S).sentenceInclusion s
  let w' := (U).map (ifm).hom φ
  have hs : s.val=a.val :=
    ((SentenceAxiomPullbacks.inclusion_graph (sentenceWord P σ π d) Γ hΓ _ _).mp
      (Total.totalFunction_mem (axioms P σ π d Γ hΓ) a)).2
  have hword : w'.val∈Total.val (sentenceWord P σ π d).hom a.val := by
    rw [← hs]
    change w'.val∈Total.val ((S).sentenceInclusion.hom ≫ (ifm).hom.hom) s.val
    exact (Total.mem_val_comp (S).sentenceInclusion.hom (ifm).hom.hom s.val w'.val).mpr
      ⟨φ.val,Total.totalFunction_mem (S).sentenceInclusion s,Total.totalFunction_mem (ifm).hom φ⟩
  have hv : w'.val=φ.val :=
    ((NamedSyntaxComparison.sourcePairIso_formula_graph P (V) σ π d _ _).mp
      (Total.totalFunction_mem (ifm).hom φ)).2
  have he : w=φ.val := (Part.mem_unique hw hword).trans hv
  rw [CategoryTheory.Functor.map_comp_apply,decodeFormula_code]
  exact he ▸ hΓw

/-- This is the actual finite leaf support extracted from any point of
the nonlogical axiom carrier, including an arbitrary uniform Γ. -/
theorem axiom_finite_proof (a : (U).obj (axiomCarrier P σ π d Γ hΓ)) :
    FiniteAxiomProof σ π d Γ (decodeFormula P σ π d
      ((U).map (axioms P σ π d Γ hΓ ≫ (S).sentenceInclusion) a)) := by
  apply FiniteAxiomProof.axiom_of_mem σ π d
  · exact axiom_word_member P σ π d Γ hΓ a
  · rw [CategoryTheory.Functor.map_comp_apply]
    exact sentence_inclusion_closed P σ π d ((U).map (axioms P σ π d Γ hΓ) a)

end CategoricalEssentialIncompleteness.V46.Miller.NamedProofImage
