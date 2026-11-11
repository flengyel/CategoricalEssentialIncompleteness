/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerOrderedFieldSentenceMembership
public import CategoricalEssentialIncompleteness.V46MillerNamedProofImageReverse
public import CategoricalEssentialIncompleteness.V46MillerTheorySentenceMorphisms

/-! # The chosen sentence object and its actual literal-word carrier

The chart uses the existing sentence-word monomorphism and its proved
partial inverse. The chosen sentence point keeps its own coordinate;
only its image under the sentence-word morphism is a formula word.
-/

@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.RestrictionCategory CategoryTheory.Limits
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
namespace CategoricalEssentialIncompleteness.V46.Miller.TheorySentenceWords
open OrderedFieldSyntax
variable (P : Uniform.Family)
local notation "σ" => functionSymbols
local notation "π" => relationSymbols
local notation "d" => bound
local notation "F" => Syntax.predicateFunctor P
local notation "U" => (Total.underlying (P := P))
local notation "S" => NamedProofImage.syntaxData P σ π d
local notation "S₀" => NamedSyntaxComparison.sourceSyntax NamedPostfixEncoding.variableCarrier σ π d
local notation "wordMap" => NamedProofImage.sentenceWord P σ π d

/-- The original recursive set of closed ordered-field formula words. -/
def literalSet : Set ℕ := {word | sentencePredicate.val.Evalb ![word]}

def literalObject : Total.TotalCategory P := (F).obj sentencePredicate

theorem literal_support (word : ℕ) :
    word∈(literalObject P).obj.support ↔ word∈literalSet :=
  AxiomSubobjects.mapped_support P sentencePredicate word

/-- Literal membership means the original named formula has no free
variables. The decoding is the proved plain-parser bijection. -/
theorem literal_iff_native (word : ℕ) : word∈literalSet ↔
    ∃ φ : Formula,φ.freeVariables=[] ∧ formulaCode φ=word := by
  constructor
  · intro hw
    have hp := ((ConcreteNamedComparison.literalSentenceCarrier_eval 𝗣𝗔
      variableSymbols σ π d ℕ word).mp hw).1
    let q : (PredicateInterpretation.functor 𝗣𝗔 ℕ).obj (S₀).algebra.a.2 := ⟨word,hp⟩
    let φ := (NamedPostfixPlainComparison.plainFormulaModelEquiv σ π d).symm q
    have hc : formulaCode φ=word :=
      (NamedPostfixPlainComparison.plainFormulaModelEquiv_val φ).symm.trans
        (congrArg Subtype.val ((NamedPostfixPlainComparison.plainFormulaModelEquiv σ π d).apply_symm_apply q))
    exact ⟨φ,(sentence_formulaCode φ).mp (hc.symm ▸ hw),hc⟩
  · rintro ⟨φ,hc,rfl⟩
    exact (sentence_formulaCode φ).mpr hc

/-- Every chosen sentence point is the actual point over its decoded
formula. This states equality of points through their monic inclusion. -/
theorem sentencePoint_surjective (s : (U).obj (S).sentenceObject) :
    ∃ φ : Formula,∃ hc : φ.freeVariables=[],NamedProofImage.sentencePoint P σ π d φ hc=s := by
  let φ := NamedProofImage.decodeFormula P σ π d ((U).map (S).sentenceInclusion s)
  have hc : φ.freeVariables=[] := NamedProofImage.sentence_inclusion_closed P σ π d s
  refine ⟨φ,hc,?_⟩
  apply TheorySentenceMorphisms.sentence_point_ext P
  rw [NamedProofImage.sentencePoint_inclusion]
  exact NamedProofImage.formulaPoint_decode P σ π d ((U).map (S).sentenceInclusion s)

/-- This is the full output image, not an assertion about the selected
scalar code of a chosen pullback point. -/
theorem sentenceWord_image : Total.Subobjects.imageCodes (wordMap)=literalSet := by
  ext word
  constructor
  · rintro ⟨n,hn⟩
    let s : (U).obj (S).sentenceObject := ⟨n,Total.val_source (wordMap).hom n word hn⟩
    obtain ⟨φ,hc,hs⟩ := sentencePoint_surjective P s
    have hsval : (NamedProofImage.sentencePoint P σ π d φ hc).val=n := congrArg Subtype.val hs
    have hφ : formulaCode φ∈Total.val (wordMap).hom n :=
      hsval ▸ NamedProofImage.sentencePoint_word P σ π d φ hc
    have hv : word=formulaCode φ := Part.mem_unique hn hφ
    rw [hv]
    exact (sentence_formulaCode φ).mpr hc
  · intro hw
    obtain ⟨φ,hc,rfl⟩ := (literal_iff_native word).mp hw
    exact ⟨(NamedProofImage.sentencePoint P σ π d φ hc).val,
      NamedProofImage.sentencePoint_word P σ π d φ hc⟩

theorem literal_formula_supported (word : ℕ)
    (hw : word∈(literalObject P).obj.support) : word∈((F).obj (S₀).algebra.a.2).obj.support := by
  apply (AxiomSubobjects.mapped_support P (S₀).algebra.a.2 word).mpr
  exact ((ConcreteNamedComparison.literalSentenceCarrier_eval 𝗣𝗔
    variableSymbols σ π d ℕ word).mp ((literal_support P word).mp hw)).1

/-- Guarded identity into the actual mapped plain formula object. -/
def literalInclusion : literalObject P ⟶ (F).obj (S₀).algebra.a.2 :=
  AxiomSubobjects.supportInclusion (literalObject P) ((F).obj (S₀).algebra.a.2)
    (literal_formula_supported P)

theorem literalInclusion_graph (word out : ℕ) :
    out∈Total.val (literalInclusion P).hom word ↔ word∈literalSet ∧ out=word :=
  (AxiomSubobjects.supportInclusion_graph (literalObject P) ((F).obj (S₀).algebra.a.2)
    (literal_formula_supported P) word out).trans
      (and_congr_left (fun _ => literal_support P word))

instance literalInclusion_mono : Mono (literalInclusion P) :=
  AxiomSubobjects.supportInclusion_mono (literalObject P) ((F).obj (S₀).algebra.a.2)
    (literal_formula_supported P)

theorem literalInclusion_image : Total.Subobjects.imageCodes (literalInclusion P)=literalSet := by
  ext word
  constructor
  · rintro ⟨n,hn⟩
    obtain ⟨hn,rfl⟩ := (literalInclusion_graph P n word).mp hn
    exact hn
  · intro hw
    exact ⟨word,(literalInclusion_graph P word word).mpr ⟨hw,rfl⟩⟩

/-- The total chart is constructed from the actual mono inverse. -/
def toLiteral : (S).sentenceObject ⟶ literalObject P :=
  Total.Subobjects.factorThroughMono (wordMap) (literalInclusion P) (by
    simpa only [sentenceWord_image,literalInclusion_image] using (Set.Subset.refl literalSet))

def fromLiteral : literalObject P ⟶ (S).sentenceObject :=
  Total.Subobjects.factorThroughMono (literalInclusion P) (wordMap) (by
    simpa only [sentenceWord_image,literalInclusion_image] using (Set.Subset.refl literalSet))

theorem toLiteral_inclusion : toLiteral P ≫ literalInclusion P=wordMap :=
  Total.Subobjects.factorThroughMono_fac _ _ _

theorem fromLiteral_word : fromLiteral P ≫ wordMap=literalInclusion P :=
  Total.Subobjects.factorThroughMono_fac _ _ _

def sentenceIso : (S).sentenceObject ≅ literalObject P where
  hom := toLiteral P
  inv := fromLiteral P
  hom_inv_id := by
    apply (cancel_mono (wordMap)).mp
    rw [Category.assoc,fromLiteral_word,toLiteral_inclusion,Category.id_comp]
  inv_hom_id := by
    apply (cancel_mono (literalInclusion P)).mp
    rw [Category.assoc,toLiteral_inclusion,fromLiteral_word,Category.id_comp]

theorem toLiteral_graph (s word : ℕ) :
    word∈Total.val (sentenceIso P).hom.hom s ↔ word∈Total.val (wordMap).hom s := by
  rw [show (sentenceIso P).hom=toLiteral P from rfl,toLiteral,
    Total.Subobjects.factorThroughMono_graph]
  constructor
  · rintro ⟨w,hw,hi⟩
    exact ((literalInclusion_graph P word w).mp hi).2 ▸ hw
  · intro hw
    refine ⟨word,hw,(literalInclusion_graph P word word).mpr ⟨?_,rfl⟩⟩
    exact (Set.ext_iff.mp (sentenceWord_image P) word).mp ⟨s,hw⟩

theorem fromLiteral_graph (word s : ℕ) :
    s∈Total.val (sentenceIso P).inv.hom word ↔ word∈Total.val (wordMap).hom s := by
  rw [show (sentenceIso P).inv=fromLiteral P from rfl,fromLiteral,
    Total.Subobjects.factorThroughMono_graph]
  constructor
  · rintro ⟨w,hi,hw⟩
    exact ((literalInclusion_graph P word w).mp hi).2 ▸ hw
  · intro hw
    refine ⟨word,(literalInclusion_graph P word word).mpr ⟨?_,rfl⟩,hw⟩
    exact (Set.ext_iff.mp (sentenceWord_image P) word).mp ⟨s,hw⟩

theorem sentenceIso_value (s : (U).obj (S).sentenceObject) :
    ((U).map (sentenceIso P).hom s).val=((U).map (wordMap) s).val :=
  Part.mem_unique ((toLiteral_graph P _ _).mp (Total.totalFunction_mem (sentenceIso P).hom s))
    (Total.totalFunction_mem (wordMap) s)

theorem sentencePoint_value (φ : Formula) (hc : φ.freeVariables=[]) :
    ((U).map (sentenceIso P).hom (NamedProofImage.sentencePoint P σ π d φ hc)).val=formulaCode φ :=
  Part.mem_unique ((toLiteral_graph P _ _).mp (Total.totalFunction_mem (sentenceIso P).hom _))
    (NamedProofImage.sentencePoint_word P σ π d φ hc)

theorem negation_supported (word : ℕ) (hw : word∈(literalObject P).obj.support) :
    negationWord word∈(literalObject P).obj.support := by
  obtain ⟨φ,hc,rfl⟩ := (literal_iff_native word).mp ((literal_support P word).mp hw)
  exact (literal_support P _).mpr (negation_sentence φ hc)

/-- Literal negation uses the original primitive-recursive constructor. -/
def literalNegation : literalObject P ⟶ literalObject P :=
  ⟨Total.totalFromFunction negationWord negationWord_primrec.to_comp (negation_supported P),
    Total.totalFromFunction_total _ _ _⟩

theorem literalNegation_graph (word out : ℕ) :
    out∈Total.val (literalNegation P).hom word ↔ word∈literalSet ∧ out=negationWord word :=
  (Total.mem_totalFromFunction negationWord negationWord_primrec.to_comp
    (negation_supported P) word out).trans (and_congr_left (fun _ => literal_support P word))

theorem negation_word_value (s : (U).obj (S).sentenceObject) :
    ((U).map (TheorySentenceMorphisms.negation P ≫ (sentenceIso P).hom) s).val=
      negationWord (((U).map (sentenceIso P).hom s).val) := by
  obtain ⟨φ,hc,rfl⟩ := sentencePoint_surjective P s
  rw [CategoryTheory.Functor.map_comp_apply,TheorySentenceMorphisms.negation_point]
  erw [sentencePoint_value P (.neg φ) hc, sentencePoint_value P φ hc]
  exact formulaCode_negation φ

private theorem total_ext {X Y : Total.TotalCategory P} (f g : X ⟶ Y)
    (h : ∀ s : (U).obj X,(U).map f s=(U).map g s) : f=g := by
  apply WideSubcategory.hom_ext
  apply Total.val_ext_on_source f.hom g.hom
  intro n hn
  let s : (U).obj X := ⟨n,hn⟩
  exact (Part.eq_some_iff.mpr (Total.totalFunction_mem f s)).trans
    ((congrArg Part.some (congrArg Subtype.val (h s))).trans
      (Part.eq_some_iff.mpr (Total.totalFunction_mem g s)).symm)

/-- The square concerns the actual S₁ sentence-negation morphism. -/
theorem negation_square : TheorySentenceMorphisms.negation P ≫ (sentenceIso P).hom=
    (sentenceIso P).hom ≫ literalNegation P := by
  apply total_ext
  intro s
  apply Subtype.ext
  apply (negation_word_value P s).trans
  symm
  rw [CategoryTheory.Functor.map_comp_apply]
  exact ((literalNegation_graph P _ _).mp (Total.totalFunction_mem (literalNegation P)
    ((U).map (sentenceIso P).hom s))).2

/-- One fixed numerical-to-literal-sentence morphism, chosen before Γ. -/
def literalTheta : TheorySentenceMorphisms.numericalObject P ⟶ literalObject P :=
  TheorySentenceMorphisms.theta P ≫ (sentenceIso P).hom

theorem theta_word_value (n : ℕ) :
    ((U).map (literalTheta P) (TheorySentenceMorphisms.numericalPoint P n)).val=theta n := by
  rw [literalTheta,CategoryTheory.Functor.map_comp_apply,TheorySentenceMorphisms.theta_point]
  exact sentencePoint_value P (thetaSentence n) (thetaSentence_closed n)

theorem negation_theta_word_value (n : ℕ) :
    ((U).map (literalTheta P ≫ literalNegation P) (TheorySentenceMorphisms.numericalPoint P n)).val=
      negationWord (theta n) := by
  rw [literalTheta,Category.assoc,← negation_square,← Category.assoc,
    CategoryTheory.Functor.map_comp_apply,TheorySentenceMorphisms.negation_theta_point]
  exact sentencePoint_value P (.neg (thetaSentence n)) (thetaSentence_closed n)

end CategoricalEssentialIncompleteness.V46.Miller.TheorySentenceWords
