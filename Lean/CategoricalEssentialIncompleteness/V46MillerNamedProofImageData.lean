/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerNamedSyntaxComparisonSentences
public import CategoricalEssentialIncompleteness.V46MillerSentenceAxiomPullbacks
public import CategoricalEssentialIncompleteness.V46MillerDerivationWordCarrier
public import CategoricalEssentialIncompleteness.V46SyntacticNamedHilbertSchemePoints
public import CategoricalEssentialIncompleteness.V46SyntacticGeneratedRefutations

/-! # Named points, arbitrary external axioms and constructed proofs

Only the recursive signature is PA-described. The external axiom set is an arbitrary
uniformly enumerable set; it is pulled back along the sentence inclusion. No code of a
chosen sentence point is identified with the word of its formula.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.RestrictionCategory CategoryTheory.Limits
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.LocalConnectedness
namespace CategoricalEssentialIncompleteness.V46.Miller.NamedProofImage
open NamedFiniteSyntax NamedPostfixEncoding
variable (P : Uniform.Family)
local notation "F" => Syntax.predicateFunctor P
local notation "N" => PredicateInterpretation.functor 𝗣𝗔 ℕ

def sourcePoint (C : PredicateCategory 𝗣𝗔) (q : PredicateInterpretation.Obj ℕ C) :
    Total.underlying.obj ((F).obj C) :=
  ⟨q.val,(AxiomSubobjects.mapped_support P C q.val).mpr q.property⟩

theorem map_sourcePoint {C D : PredicateCategory 𝗣𝗔} (f : C ⟶ D)
    (q : PredicateInterpretation.Obj ℕ C) :
    Total.underlying.map ((F).map f) (sourcePoint P C q)=
      sourcePoint P D ((N).map f q) := by
  apply Subtype.ext
  exact Part.mem_unique (Total.totalFunction_mem ((F).map f) (sourcePoint P C q))
    ((Syntax.predicateFunctor_graph P f q.val ((N).map f q).val).mpr ⟨q,rfl,rfl⟩)

variable (σ π : ℕ → Carrier) (d : ℕ)
local notation "V" => (NamedPostfixEncoding.variableCarrier : PredicateCategory 𝗣𝗔)
local notation "S₀" => NamedSyntaxComparison.sourceSyntax (V) σ π d
local notation "S" => NamedSyntaxComparison.presentedSyntax P (V) σ π d
local notation "Tm" => NamedFiniteSyntax.Term (NamedPostfixEncoding.Symbols σ) d
local notation "Fm" => NamedFiniteSyntax.Formula (NamedPostfixEncoding.Symbols σ) (NamedPostfixEncoding.Symbols π) d
local notation "it" => NamedSyntaxComparison.termIso P (V) σ π d
local notation "ifm" => NamedSyntaxComparison.formulaIso P (V) σ π d
local notation "is" => NamedSyntaxComparison.sentenceIso P (V) σ π d

abbrev syntaxData := (S)

def sourceTermPoint (t : Tm) : Total.underlying.obj ((F).obj (S₀).algebra.a.1) :=
  sourcePoint P _ (SyntacticNamedHilbert.termPoint σ π d t)

def sourceFormulaPoint (φ : Fm) : Total.underlying.obj ((F).obj (S₀).algebra.a.2) :=
  sourcePoint P _ (SyntacticNamedHilbert.formulaPoint σ π d φ)

def termPoint (t : Tm) : Total.underlying.obj (S).algebra.a.1 :=
  Total.underlying.map (it).inv (sourceTermPoint P σ π d t)

def formulaPoint (φ : Fm) : Total.underlying.obj (S).algebra.a.2 :=
  Total.underlying.map (ifm).inv (sourceFormulaPoint P σ π d φ)

theorem termPoint_chart (t : Tm) :
    Total.underlying.map (it).hom (termPoint P σ π d t)=sourceTermPoint P σ π d t := by
  simp only [termPoint,← CategoryTheory.Functor.map_comp_apply,Iso.inv_hom_id,CategoryTheory.Functor.map_id_apply]

theorem formulaPoint_chart (φ : Fm) :
    Total.underlying.map (ifm).hom (formulaPoint P σ π d φ)=sourceFormulaPoint P σ π d φ := by
  simp only [formulaPoint,← CategoryTheory.Functor.map_comp_apply,Iso.inv_hom_id,CategoryTheory.Functor.map_id_apply]

theorem termPoint_value (t : Tm) : (termPoint P σ π d t).val=termCode t := by
  have h := (Total.totalFunction_eq_iff (it).hom _ _).mp (termPoint_chart P σ π d t)
  have hv := ((NamedSyntaxComparison.sourcePairIso_term_graph P (V) σ π d _ _).mp h).2
  exact hv.symm.trans (SyntacticNamedHilbert.termPoint_value σ π d t)

theorem formulaPoint_value (φ : Fm) : (formulaPoint P σ π d φ).val=formulaCode φ := by
  have h := (Total.totalFunction_eq_iff (ifm).hom _ _).mp (formulaPoint_chart P σ π d φ)
  have hv := ((NamedSyntaxComparison.sourcePairIso_formula_graph P (V) σ π d _ _).mp h).2
  exact hv.symm.trans (SyntacticNamedHilbert.formulaPoint_value σ π d φ)

/-- The source sentence point is chosen only from the PA sentence pullback. Its formula is
fixed by its monic inclusion. -/
theorem sourceSentencePoint_exists (φ : Fm) (hc : φ.freeVariables=[]) :
    ∃ s : PredicateInterpretation.Obj ℕ (S₀).sentenceObject,
      (N).map (S₀).sentenceInclusion s=SyntacticNamedHilbert.formulaPoint σ π d φ := by
  have hf : (SyntacticSyntax.Postfix.plainCarrier true
      (NamedPostfixEncoding.termPolynomial σ d) (NamedPostfixEncoding.formulaPolynomial π d)).val.Evalb
        (M := ℕ) ![formulaCode φ] := by
    simpa only [SyntacticNamedHilbert.formulaPoint_value,NamedPostfixEncoding.termPolynomial,
      NamedPostfixEncoding.formulaPolynomial] using
      (SyntacticNamedHilbert.formulaPoint σ π d φ).property
  have hs : (ConcreteNamedComparison.literalSentenceCarrier 𝗣𝗔 (V) σ π d).val.Evalb
      (M := ℕ) ![formulaCode φ] :=
    (ConcreteNamedComparison.literalSentenceCarrier_eval 𝗣𝗔 (V) σ π d ℕ _).mpr
      ⟨hf,(@NamedPostfixEncoding.sentence_formulaCode_iff σ π d φ).mpr hc⟩
  obtain ⟨s,h⟩ := (SyntacticGeneratedAxioms.sentence_points 𝗣𝗔 (V) σ π d ℕ (formulaCode φ)).mp hs
  exact ⟨s,Subtype.ext (h.trans (SyntacticNamedHilbert.formulaPoint_value σ π d φ).symm)⟩

def sourceSentencePoint (φ : Fm) (hc : φ.freeVariables=[]) :
    PredicateInterpretation.Obj ℕ (S₀).sentenceObject :=
  Classical.choose (sourceSentencePoint_exists σ π d φ hc)

theorem sourceSentencePoint_inclusion (φ : Fm) (hc : φ.freeVariables=[]) :
    (N).map (S₀).sentenceInclusion (sourceSentencePoint σ π d φ hc)=
      SyntacticNamedHilbert.formulaPoint σ π d φ :=
  Classical.choose_spec (sourceSentencePoint_exists σ π d φ hc)

def sentencePoint (φ : Fm) (hc : φ.freeVariables=[]) :
    Total.underlying.obj (S).sentenceObject :=
  Total.underlying.map (is).inv (sourcePoint P _ (sourceSentencePoint σ π d φ hc))

theorem sentencePoint_inclusion (φ : Fm) (hc : φ.freeVariables=[]) :
    Total.underlying.map (S).sentenceInclusion (sentencePoint P σ π d φ hc)=
      formulaPoint P σ π d φ := by
  change Total.underlying.map (S).sentenceInclusion
    (Total.underlying.map (is).inv _)=_
  rw [← CategoryTheory.Functor.map_comp_apply,NamedSyntaxComparison.sentenceIso_inverse_inclusion,
    CategoryTheory.Functor.map_comp_apply,map_sourcePoint,sourceSentencePoint_inclusion]
  rfl

def sentenceWord : (S).sentenceObject ⟶ (F).obj (S₀).algebra.a.2 :=
  (S).sentenceInclusion ≫ (ifm).hom

instance sentenceWord_mono : Mono (sentenceWord P σ π d) := by
  dsimp [sentenceWord]
  infer_instance

theorem sentencePoint_word (φ : Fm) (hc : φ.freeVariables=[]) :
    formulaCode φ∈Total.val (sentenceWord P σ π d).hom (sentencePoint P σ π d φ hc).val := by
  have h : Total.underlying.map (sentenceWord P σ π d) (sentencePoint P σ π d φ hc)=
      sourceFormulaPoint P σ π d φ := by
    rw [sentenceWord,CategoryTheory.Functor.map_comp_apply,sentencePoint_inclusion,formulaPoint_chart]
  have hm := (Total.totalFunction_eq_iff _ _ _).mp h
  simpa only [sourceFormulaPoint,sourcePoint,SyntacticNamedHilbert.formulaPoint_value] using hm

theorem formulaPoint_negation (φ : Fm) :
    Total.underlying.map (S).negationConstructor (formulaPoint P σ π d φ)=
      formulaPoint P σ π d (.neg φ) := by
  apply ((CategoryTheory.isIso_iff_bijective (Total.underlying.map (ifm).hom)).mp inferInstance).1
  rw [← CategoryTheory.Functor.map_comp_apply,← NamedSyntaxComparison.formula_negation_comparison,
    CategoryTheory.Functor.map_comp_apply,formulaPoint_chart,sourceFormulaPoint,map_sourcePoint]
  exact (congrArg (sourcePoint P (S₀).algebra.a.2)
    (SyntacticNamedHilbert.negation_point σ π d φ)).trans
      (formulaPoint_chart P σ π d (.neg φ)).symm

variable (Γ : Set ℕ) (hΓ : Uniform.Enumerable P (· ∈ Γ))

def axiomCarrier : Total.TotalCategory P := SentenceAxiomPullbacks.axCarrier (sentenceWord P σ π d) Γ hΓ

def axioms : axiomCarrier P σ π d Γ hΓ ⟶ (S).sentenceObject :=
  SentenceAxiomPullbacks.inclusion (sentenceWord P σ π d) Γ hΓ

instance axioms_mono : Mono (axioms P σ π d Γ hΓ) :=
  SentenceAxiomPullbacks.inclusion_mono (sentenceWord P σ π d) Γ hΓ

def axiomPoint (φ : Fm) (hc : φ.freeVariables=[]) (hφ : formulaCode φ∈Γ) :
    Total.underlying.obj (axiomCarrier P σ π d Γ hΓ) :=
  ⟨(sentencePoint P σ π d φ hc).val,
    (SentenceAxiomPullbacks.axCarrier_support (sentenceWord P σ π d) Γ hΓ _).mpr
      ⟨formulaCode φ,sentencePoint_word P σ π d φ hc,hφ⟩⟩

theorem axiomPoint_sentence (φ : Fm) (hc : φ.freeVariables=[]) (hφ : formulaCode φ∈Γ) :
    Total.underlying.map (axioms P σ π d Γ hΓ) (axiomPoint P σ π d Γ hΓ φ hc hφ)=
      sentencePoint P σ π d φ hc := by
  apply (Total.totalFunction_eq_iff _ _ _).mpr
  exact (SentenceAxiomPullbacks.inclusion_graph (sentenceWord P σ π d) Γ hΓ _ _).mpr
    ⟨(axiomPoint P σ π d Γ hΓ φ hc hφ).property,rfl⟩

theorem axiomPoint_formula (φ : Fm) (hc : φ.freeVariables=[]) (hφ : formulaCode φ∈Γ) :
    Total.underlying.map (axioms P σ π d Γ hΓ ≫ (S).sentenceInclusion)
      (axiomPoint P σ π d Γ hΓ φ hc hφ)=formulaPoint P σ π d φ := by
  rw [CategoryTheory.Functor.map_comp_apply,axiomPoint_sentence,sentencePoint_inclusion]

def rules : RulePresentation (S).algebra.a.2 2 := (S).logicalRules (axioms P σ π d Γ hΓ)
def proofAlgebra : Endofunctor.Algebra (rules P σ π d Γ hΓ).inference :=
  Derivation.wordAlgebra (rules P σ π d Γ hΓ)
def proofInitial : IsInitial (proofAlgebra P σ π d Γ hΓ) :=
  Derivation.wordInitial (rules P σ π d Γ hΓ)
def proofObject : Total.TotalCategory P := (proofAlgebra P σ π d Γ hΓ).a.left
def conclusion : proofObject P σ π d Γ hΓ ⟶ (S).algebra.a.2 :=
  Derivation.wordConclusion (rules P σ π d Γ hΓ)
def formulaTheory : Subobject (S).algebra.a.2 := imageSubobject (conclusion P σ π d Γ hΓ)
def sentenceProofObject : Total.TotalCategory P := pullback (conclusion P σ π d Γ hΓ) (S).sentenceInclusion
def sentenceConclusion : sentenceProofObject P σ π d Γ hΓ ⟶ (S).sentenceObject :=
  pullback.snd (conclusion P σ π d Γ hΓ) (S).sentenceInclusion
def sentenceTheory : Subobject (S).sentenceObject := imageSubobject (sentenceConclusion P σ π d Γ hΓ)

end CategoricalEssentialIncompleteness.V46.Miller.NamedProofImage
