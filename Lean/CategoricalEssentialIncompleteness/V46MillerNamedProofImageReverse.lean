import CategoricalEssentialIncompleteness.V46MillerNamedProofImageSchemeReflection
import CategoricalEssentialIncompleteness.V46MillerNamedProofImageNativeClosure
import CategoricalEssentialIncompleteness.V46MillerNamedProofImageForward

/-! # Exact native proof images for arbitrary uniformly enumerable Gamma

The reverse implication uses the actual ordered-word derivation rank.
Each nonlogical leaf contributes its literal formula word to a finite
Gamma support; Gen retains that support and MP combines the two finite
supports. No Gamma proof selector or PA description of Gamma is used.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.RestrictionCategory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.LocalConnectedness
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
namespace CategoricalEssentialIncompleteness.V46.Miller.NamedProofImage
open NamedFiniteSyntax NamedPostfixEncoding
variable (P : Uniform.Family) (σ π : ℕ → Carrier) (d : ℕ)
variable (Γ : Set ℕ) (hΓ : Uniform.Enumerable P (· ∈ Γ))
local notation "U" => (Total.underlying (P := P))
local notation "S" => syntaxData P σ π d
local notation "c" => conclusion P σ π d Γ hΓ
local notation "Fm" => NamedFiniteSyntax.Formula (Symbols σ) (Symbols π) d

/-- Every actual constructed conclusion has a proof in the original
native calculus using a finite subset of the external Gamma set. -/
theorem conclusion_finite (p : (U).obj (proofObject P σ π d Γ hΓ)) :
    FiniteAxiomProof σ π d Γ (decodeFormula P σ π d ((U).map (c) p)) := by
  apply Derivation.WordInduction.firstOrder_conclusion_induction
    (S).logicalAxioms (S).sentenceInclusion (axioms P σ π d Γ hΓ)
    (S).quantifierConstructor (S).implicationConstructor
    (fun q => FiniteAxiomProof σ π d Γ (decodeFormula P σ π d q))
    (logical_parameter_finite P σ π d Γ)
    (axiom_finite_proof P σ π d Γ hΓ)
    (generalization_finite P σ π d Γ)
    (modusPonens_finite P σ π d Γ) p

theorem realizes_iff_finite (φ : Fm) :
    (∃ p : (U).obj (proofObject P σ π d Γ hΓ),(U).map (c) p=formulaPoint P σ π d φ) ↔
      FiniteAxiomProof σ π d Γ φ := by
  constructor
  · rintro ⟨p,hp⟩
    have h := conclusion_finite P σ π d Γ hΓ p
    rwa [hp,decode_formulaPoint] at h
  · exact finite_realizes P σ π d Γ hΓ

theorem formula_range_iff (φ : Fm) :
    formulaCode φ∈Total.Subobjects.imageCodes (c) ↔ FiniteAxiomProof σ π d Γ φ := by
  constructor
  · rintro ⟨n,hn⟩
    let p : (U).obj (proofObject P σ π d Γ hΓ) := ⟨n,Total.val_source (c).hom n _ hn⟩
    apply (realizes_iff_finite P σ π d Γ hΓ φ).mp
    refine ⟨p,(Total.totalFunction_eq_iff _ _ _).mpr ?_⟩
    simpa only [formulaPoint_value] using hn
  · exact finite_formula_range P σ π d Γ hΓ

theorem formula_image_iff (φ : Fm) :
    formulaCode φ∈Total.Subobjects.imageCodes (image.ι (c)) ↔ FiniteAxiomProof σ π d Γ φ := by
  rw [Total.Subobjects.imageCodes_image_ι]
  exact formula_range_iff P σ π d Γ hΓ φ

/-- Sentence-range membership is stated at the actual chosen sentence
point. It is not an equality between its selected code and formulaCode. -/
theorem sentence_range_iff (φ : Fm) (hc : φ.freeVariables=[]) :
    (sentencePoint P σ π d φ hc).val∈Total.Subobjects.imageCodes
      (sentenceConclusion P σ π d Γ hΓ) ↔ FiniteAxiomProof σ π d Γ φ := by
  constructor
  · rintro ⟨n,hn⟩
    let q : (U).obj (sentenceProofObject P σ π d Γ hΓ) :=
      ⟨n,Total.val_source (sentenceConclusion P σ π d Γ hΓ).hom n _ hn⟩
    have hq : (U).map (sentenceConclusion P σ π d Γ hΓ) q=sentencePoint P σ π d φ hc :=
      (Total.totalFunction_eq_iff _ _ _).mpr hn
    let p := (U).map (pullback.fst (c) (S).sentenceInclusion) q
    have hp : (U).map (c) p=formulaPoint P σ π d φ := by
      have hv := congrArg (fun k : sentenceProofObject P σ π d Γ hΓ ⟶ (S).algebra.a.2 =>
        (U).map k q) (pullback.condition (f := (c)) (g := (S).sentenceInclusion))
      simp only [CategoryTheory.Functor.map_comp_apply] at hv
      have hi : (U).map (S).sentenceInclusion ((U).map (sentenceConclusion P σ π d Γ hΓ) q)=
          formulaPoint P σ π d φ :=
        (congrArg ((U).map (S).sentenceInclusion) hq).trans (sentencePoint_inclusion P σ π d φ hc)
      exact hv.trans hi
    exact (realizes_iff_finite P σ π d Γ hΓ φ).mp ⟨p,hp⟩
  · exact fun h => finite_sentence_range P σ π d Γ hΓ h hc

theorem sentence_image_iff (φ : Fm) (hc : φ.freeVariables=[]) :
    (sentencePoint P σ π d φ hc).val∈Total.Subobjects.imageCodes
      (image.ι (sentenceConclusion P σ π d Γ hΓ)) ↔ FiniteAxiomProof σ π d Γ φ := by
  rw [Total.Subobjects.imageCodes_image_ι]
  exact sentence_range_iff P σ π d Γ hΓ φ hc

theorem sentence_word_value (s : (U).obj (S).sentenceObject) :
    ((U).map (sentenceWord P σ π d) s).val=((U).map (S).sentenceInclusion s).val := by
  rw [sentenceWord,CategoryTheory.Functor.map_comp_apply]
  exact ((NamedSyntaxComparison.sourcePairIso_formula_graph P
    (variableCarrier : PredicateCategory 𝗣𝗔) σ π d _ _).mp
      (Total.totalFunction_mem (NamedSyntaxComparison.formulaIso P
        (variableCarrier : PredicateCategory 𝗣𝗔) σ π d).hom ((U).map (S).sentenceInclusion s))).2

/-- The formula-word image of the actual sentence conclusion consists
exactly of the closed literal native Gamma theorems. -/
theorem sentence_word_range_iff (φ : Fm) :
    formulaCode φ∈Total.Subobjects.imageCodes
      (sentenceConclusion P σ π d Γ hΓ ≫ sentenceWord P σ π d) ↔
      FiniteAxiomProof σ π d Γ φ ∧ φ.freeVariables=[] := by
  constructor
  · rintro ⟨n,hn⟩
    let q : (U).obj (sentenceProofObject P σ π d Γ hΓ) :=
      ⟨n,Total.val_source (sentenceConclusion P σ π d Γ hΓ ≫ sentenceWord P σ π d).hom n _ hn⟩
    let s := (U).map (sentenceConclusion P σ π d Γ hΓ) q
    let f := (U).map (S).sentenceInclusion s
    let p := (U).map (pullback.fst (c) (S).sentenceInclusion) q
    have hp : (U).map (c) p=f := by
      have hv := congrArg (fun k : sentenceProofObject P σ π d Γ hΓ ⟶ (S).algebra.a.2 =>
        (U).map k q) (pullback.condition (f := (c)) (g := (S).sentenceInclusion))
      simp only [CategoryTheory.Functor.map_comp_apply] at hv
      exact hv
    have hw : ((U).map (sentenceWord P σ π d) s).val=formulaCode φ := by
      have hm := Part.mem_unique (Total.totalFunction_mem
        (sentenceConclusion P σ π d Γ hΓ ≫ sentenceWord P σ π d) q) hn
      have hh : ((U).map (sentenceConclusion P σ π d Γ hΓ ≫ sentenceWord P σ π d) q).val=
          formulaCode φ := hm
      have hv := congrArg Subtype.val ((U).map_comp_apply
        (sentenceConclusion P σ π d Γ hΓ) (sentenceWord P σ π d) q)
      exact hv.symm.trans hh
    have hf : f.val=formulaCode φ := (sentence_word_value P σ π d s).symm.trans hw
    have hdecode : decodeFormula P σ π d f=φ :=
      NamedPostfixEncoding.formulaCode_injective ((decodeFormula_code P σ π d f).trans hf)
    have hproof := conclusion_finite P σ π d Γ hΓ p
    rw [hp,hdecode] at hproof
    have hclosed : (decodeFormula P σ π d f).freeVariables=[] :=
      sentence_inclusion_closed P σ π d s
    rw [hdecode] at hclosed
    exact ⟨hproof,hclosed⟩
  · rintro ⟨h,hc⟩
    exact finite_sentence_word_range P σ π d Γ hΓ h hc

def formulaIdem : Idem (S).algebra.a.2.obj := Ranges.range (c).hom
def sentenceIdem : Idem (S).sentenceObject.obj :=
  Ranges.range (sentenceConclusion P σ π d Γ hΓ).hom

theorem formulaIdem_literal (φ : Fm) :
    formulaCode φ∈Total.support (formulaIdem P σ π d Γ hΓ) ↔ FiniteAxiomProof σ π d Γ φ := by
  rw [formulaIdem,Total.support_range]
  exact formula_range_iff P σ π d Γ hΓ φ

theorem sentenceIdem_literal (φ : Fm) (hc : φ.freeVariables=[]) :
    (sentencePoint P σ π d φ hc).val∈Total.support (sentenceIdem P σ π d Γ hΓ) ↔
      FiniteAxiomProof σ π d Γ φ := by
  rw [sentenceIdem,Total.support_range]
  exact sentence_range_iff P σ π d Γ hΓ φ hc

end CategoricalEssentialIncompleteness.V46.Miller.NamedProofImage
