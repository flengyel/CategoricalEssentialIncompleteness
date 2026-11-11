/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NamedGammaModel
public import CategoricalEssentialIncompleteness.V46SyntacticGeneratedRefutations
public import CategoricalEssentialIncompleteness.V46NamedArithmeticProofSearchNegation

/-! # Literal Gamma theorem/refutation disjointness from its semantic model

The arithmetic code model and semantic structure are separate. Predicate
points are compared naturally with the canonical total-domain functor;
chosen sentence codes are never identified with literal formula words.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.Limits Filter
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticLists
namespace CategoricalEssentialIncompleteness.V46.NamedGammaEvidenceSoundness
open SyntacticSyntax SyntacticGeneratedAxioms NamedPostfixEncoding ConcreteNamedComparison

section Pullback
variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
variable (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T]

/-- A scalar graph image at a supplied point has exactly the witnesses
in the actual original pullback, whose second projection keeps that point. -/
theorem image_pullback_point {A B C : PredicateCategory T} (f : A ⟶ C) (g : B ⟶ C)
    (b : Obj T M B) :
    (imageCarrier (chosenGraph T f).graph).val.Evalb ![((F T M).map g b).val] ↔
      b ∈ Set.range ((F T M).map (pullback.snd f g)) := by
  rw [imageCarrier_points T M]
  constructor
  · rintro ⟨a,ha⟩
    have hm : (F T M).map f a = (F T M).map g b := Subtype.ext ha
    obtain ⟨p,_,hp⟩ := Types.exists_of_isPullback
      ((IsPullback.of_hasPullback f g).map (F T M)) a b hm
    exact ⟨p,hp⟩
  · rintro ⟨p,rfl⟩
    refine ⟨(F T M).map (pullback.fst f g) p,?_⟩
    have he := congrArg (fun h => (F T M).map h p) (pullback.condition (f := f) (g := g))
    rw [Functor.map_comp_apply,Functor.map_comp_apply] at he
    exact congrArg Subtype.val he

/-- The same predicate interpretation is compared with the canonical
chosen total-domain interpretation at every code-model point. -/
def modelCodeComparison :
    F T M ≅ realization T ⋙ PredicateInterpretation.canonicalDomainFunctor T M :=
  (PredicateInterpretation.predicateComparison T M).symm ≪≫
    Functor.isoWhiskerLeft (realization T) (PredicateInterpretation.totalCanonicalComparison T M)

end Pullback

section NaturalRanges
universe u v
variable {C : Type u} [Category C] {F H : C ⥤ Type v}

/-- Both the sentence inclusion coordinates and the negation morphism
are preserved by the actual natural isomorphism, so conclusion range
consistency transports back to predicate points. -/
theorem range_consistency_of_comparison (η : F ≅ H) {P S : C}
    (c : P ⟶ S) (negation : S ⟶ S)
    (hd : Disjoint (Set.range (H.map c))
      ((H.map negation) ⁻¹' Set.range (H.map c))) :
    Disjoint (Set.range (F.map c)) ((F.map negation) ⁻¹' Set.range (F.map c)) := by
  apply Set.disjoint_left.mpr
  rintro s ⟨p,rfl⟩ ⟨q,hq⟩
  have hc (r : F.obj P) : η.hom.app S (F.map c r) = H.map c (η.hom.app P r) :=
    congrArg (fun h => h r) (η.hom.naturality c)
  have hn (r : F.obj S) : η.hom.app S (F.map negation r) = H.map negation (η.hom.app S r) :=
    congrArg (fun h => h r) (η.hom.naturality negation)
  apply Set.disjoint_left.mp hd (show η.hom.app S (F.map c p) ∈ Set.range (H.map c) from
    ⟨η.hom.app P p,(hc p).symm⟩)
  refine ⟨η.hom.app P q,?_⟩
  exact (hc q).symm.trans ((congrArg (η.hom.app S) hq).trans (hn (F.map c p)))

end NaturalRanges

/-- The existing plain-presentation comparison is first used with an
arbitrary interpretation functor, before specializing its chosen domains. -/
theorem sentence_range_plain (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (H : PredicateCategory T ⥤ Type)
    (V : PredicateCategory T) (σ π : ℕ → PredicateCategory T) (d : ℕ)
    {X : PredicateCategory T}
    (ax : @Quiver.Hom (PredicateCategory T) inferInstance X
      (plainCategoricalSyntax T V σ π d).sentenceObject) :
    Set.range (H.map (FirstOrderModelSoundness.sentenceConclusion T
      (plainCategoricalSyntax T V σ π d) ax)) =
      Set.range (H.map (SyntacticGeneratedTheory.sentenceConclusion T V σ π d ax)) := by
  exact congrArg (fun f : @Quiver.Hom (PredicateCategory T) inferInstance
      (SyntacticGeneratedTheory.sentenceProofObject T V σ π d ax)
      (plainCategoricalSyntax T V σ π d).sentenceObject => Set.range (H.map f))
    (FirstOrderModelSoundness.sentenceConclusion_plain T V σ π d ax)


section Words
variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
variable (V : PredicateCategory T) (σ π : ℕ → PredicateCategory T) (d : ℕ) (A : Carrier)
variable (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T]
local notation "S" => plainCategoricalSyntax T V σ π d
local notation "a" => (SyntacticAxiomPredicates.axioms T V σ π d A :
  @Quiver.Hom (PredicateCategory T) inferInstance
    (SyntacticAxiomPredicates.axiomCarrier T V σ π d A)
    (CategoricalSyntax.sentenceObject (plainCategoricalSyntax T V σ π d)))
local notation "c" => (SyntacticGeneratedTheory.sentenceConclusion T V σ π d a :
  @Quiver.Hom (PredicateCategory T) inferInstance
    (SyntacticGeneratedTheory.sentenceProofObject T V σ π d a)
    (CategoricalSyntax.sentenceObject (plainCategoricalSyntax T V σ π d)))

/-- Literal theorem words at an actual chosen sentence point are exactly
the range of the original sentence-conclusion pullback. -/
theorem literal_theorem_sentence_point (s : Obj T M (S).sentenceObject) :
    (literalTheoremCarrier T V σ π d A).val.Evalb
      ![((F T M).map (S).sentenceInclusion s).val] ↔
      s ∈ Set.range ((F T M).map c) := by
  change (SyntacticSentenceImages.programTheoryCarrier T
    (SyntacticGeneratedTheory.conclusion T V σ π d a) (S).sentenceInclusion).val.Evalb
      ![((F T M).map (S).sentenceInclusion s).val] ↔ _
  rw [SyntacticSentenceImages.programTheoryCarrier_theory T
    (SyntacticGeneratedTheory.conclusion T V σ π d a) (S).sentenceInclusion M _,
    SyntacticSentenceImages.theoryCarrier_eval]
  have hs : (SyntacticSentenceImages.sentenceCarrier T (S).sentenceInclusion).val.Evalb
      ![((F T M).map (S).sentenceInclusion s).val] :=
    (imageCarrier_points T M (S).sentenceInclusion _).mpr ⟨s,rfl⟩
  rw [and_iff_right hs]
  exact image_pullback_point T M (SyntacticGeneratedTheory.conclusion T V σ π d a)
    (S).sentenceInclusion s

/-- Word-level theorem/refutation consistency uses the actual ordered
finite derivations and sentence-negation square, for every model point. -/
theorem word_disjoint_of_sentence_range
    (hd : Disjoint (Set.range ((F T M).map c))
      (((F T M).map (S).sentenceNegation) ⁻¹' Set.range ((F T M).map c)))
    (word : M) :
    ¬ ((literalTheoremCarrier T V σ π d A).val.Evalb ![word] ∧
      (literalRefutationCarrier T V σ π d A).val.Evalb ![word]) := by
  rintro ⟨ht,hr⟩
  rcases (literalRefutationCarrier_eval T V σ π d M A word).mp hr with ⟨hs,negative,hn,hnt⟩
  obtain ⟨s,hs⟩ := (sentence_points T V σ π d M word).mp hs
  have hpos : s ∈ Set.range ((F T M).map c) :=
    (literal_theorem_sentence_point T V σ π d A M s).mp (by simpa only [hs] using ht)
  let w := (F T M).map (S).sentenceInclusion s
  have hnv : ((F T M).map (S).negationConstructor w).val = negative :=
    (chosenGraph_value_iff T M (S).negationConstructor w negative).mp (by simpa only [w,hs] using hn)
  have hsn : ((F T M).map (S).sentenceInclusion
      ((F T M).map (S).sentenceNegation s)).val = negative := by
    have he := ((F T M).map_comp_apply (S).sentenceNegation (S).sentenceInclusion s).symm.trans
      (sentenceNegation_point T V σ π d M s)
    exact (congrArg Subtype.val he).trans hnv
  have hneg : (F T M).map (S).sentenceNegation s ∈ Set.range ((F T M).map c) :=
    (literal_theorem_sentence_point T V σ π d A M _).mp (by simpa only [hsn] using hnt)
  exact Set.disjoint_left.mp hd hpos hneg

end Words

section Models
universe w
variable (σ π : ℕ → PredicateCategory 𝗣𝗔) (d : ℕ) (A : Carrier)
local notation "V" => (variableCarrier : PredicateCategory 𝗣𝗔)
local notation "S" => plainCategoricalSyntax 𝗣𝗔 V σ π d
local notation "a" => (SyntacticAxiomPredicates.axioms 𝗣𝗔 V σ π d A :
  @Quiver.Hom (PredicateCategory 𝗣𝗔) inferInstance
    (SyntacticAxiomPredicates.axiomCarrier 𝗣𝗔 V σ π d A)
    (CategoricalSyntax.sentenceObject (plainCategoricalSyntax 𝗣𝗔 V σ π d)))
variable {K : Type w} [Nonempty K]
variable (functions : ∀ n : Fin (d+1), Symbols σ n.val → (Fin n.val → K) → K)
variable (relations : ∀ n : Fin (d+1), Symbols π n.val → (Fin n.val → K) → Prop)
variable (ρ : ℕ → K) (hA : NamedGammaSoundness.Models σ π d A functions relations ρ)
include functions relations ρ hA

/-- The given semantic Gamma model supplies the proved standard validity
factor, yielding actual literal theorem/refutation disjointness. -/
theorem standard_word_disjoint (word : ℕ) :
    ¬ ((literalTheoremCarrier 𝗣𝗔 V σ π d A).val.Evalb ![word] ∧
      (literalRefutationCarrier 𝗣𝗔 V σ π d A).val.Evalb ![word]) := by
  apply word_disjoint_of_sentence_range 𝗣𝗔 V σ π d A ℕ
  have hd := NamedPlainSemantics.sentenceConclusion_range_consistent σ π d functions relations a
    (NamedGammaSoundness.axioms_valid σ π d A functions relations ρ hA)
  change Disjoint
    (Set.range ((F 𝗣𝗔 ℕ).map (FirstOrderModelSoundness.sentenceConclusion 𝗣𝗔 (S) a)))
    (((F 𝗣𝗔 ℕ).map (S).sentenceNegation) ⁻¹'
      Set.range ((F 𝗣𝗔 ℕ).map (FirstOrderModelSoundness.sentenceConclusion 𝗣𝗔 (S) a))) at hd
  rw [sentence_range_plain 𝗣𝗔 (F 𝗣𝗔 ℕ) V σ π d a] at hd
  exact hd

/-- The canonical arithmetic ultrapower soundness transport is compared
naturally with predicate model points before word membership is used. -/
theorem ultrapower_word_disjoint {I : Type} (U : Ultrafilter I) (word : ArithmeticUltrapower.Model U) :
    ¬ ((literalTheoremCarrier 𝗣𝗔 V σ π d A).val.Evalb ![word] ∧
      (literalRefutationCarrier 𝗣𝗔 V σ π d A).val.Evalb ![word]) := by
  apply word_disjoint_of_sentence_range 𝗣𝗔 V σ π d A (ArithmeticUltrapower.Model U)
  apply range_consistency_of_comparison (modelCodeComparison 𝗣𝗔 (ArithmeticUltrapower.Model U))
  have hd := NamedPlainSemantics.canonical_ultrapower_conclusion_consistent σ π d functions relations a
    (NamedGammaSoundness.axioms_valid σ π d A functions relations ρ hA) U
  let H := realization 𝗣𝗔 ⋙ PredicateInterpretation.canonicalDomainFunctor 𝗣𝗔 (ArithmeticUltrapower.Model U)
  change Disjoint
    (Set.range (H.map (FirstOrderModelSoundness.sentenceConclusion 𝗣𝗔 (S) a)))
    ((H.map (S).sentenceNegation) ⁻¹'
      Set.range (H.map (FirstOrderModelSoundness.sentenceConclusion 𝗣𝗔 (S) a))) at hd
  rw [sentence_range_plain 𝗣𝗔 H V σ π d a] at hd
  exact hd

/-- The final arithmetic comparison can use any negative word linked by
the proved actual negation graph, including nonstandard input words. -/
theorem ultrapower_negation_graph_disjoint {I : Type} (U : Ultrafilter I)
    (word negative : ArithmeticUltrapower.Model U)
    (hs : (literalSentenceCarrier 𝗣𝗔 V σ π d).val.Evalb ![word])
    (hn : (chosenGraph 𝗣𝗔 (S).negationConstructor).graph.val.Evalb ![word,negative]) :
    ¬ ((literalTheoremCarrier 𝗣𝗔 V σ π d A).val.Evalb ![word] ∧
      (literalTheoremCarrier 𝗣𝗔 V σ π d A).val.Evalb ![negative]) := by
  rintro ⟨ht,hnt⟩
  apply ultrapower_word_disjoint σ π d A functions relations ρ hA U word
  exact ⟨ht,(literalRefutationCarrier_eval 𝗣𝗔 V σ π d
    (ArithmeticUltrapower.Model U) A word).mpr ⟨hs,negative,hn,hnt⟩⟩

end Models

section Arithmetic
open NamedArithmeticSignature
variable (A : Carrier) (hPA : ArithmeticNamedAxiomComparison.ExtendsPA A)
variable (hc : FFL.Entailment.Consistent (ArithmeticNamedProofConnectives.system A))
include hPA hc

/-- External consistency and actual named PA extension supply the
semantic model used by the constructed standard soundness factor. -/
theorem consistent_standard_word_disjoint (word : ℕ) :
    ¬ ((literalTheoremCarrier 𝗣𝗔 (variableCarrier : PredicateCategory 𝗣𝗔)
        functionSymbols relationSymbols bound A).val.Evalb ![word] ∧
      (literalRefutationCarrier 𝗣𝗔 (variableCarrier : PredicateCategory 𝗣𝗔)
        functionSymbols relationSymbols bound A).val.Evalb ![word]) := by
  rcases NamedGammaModel.exists_model A hPA hc with ⟨K,s,hK⟩
  let := s
  have : Nonempty K := ⟨0⟩
  exact standard_word_disjoint functionSymbols relationSymbols bound A
    ArithmeticNamedTranslation.functions ArithmeticNamedTranslation.relations (fun _ => (0 : K)) hK word

/-- The actual literal theorem and refutation sets are disjoint; no
separation or standard-model-truth premise is supplied. -/
theorem consistent_standard_disjoint :
    Disjoint
      {word : ℕ | (literalTheoremCarrier 𝗣𝗔 (variableCarrier : PredicateCategory 𝗣𝗔)
        functionSymbols relationSymbols bound A).val.Evalb ![word]}
      {word : ℕ | (literalRefutationCarrier 𝗣𝗔 (variableCarrier : PredicateCategory 𝗣𝗔)
        functionSymbols relationSymbols bound A).val.Evalb ![word]} :=
  Set.disjoint_left.mpr (fun word ht hr => consistent_standard_word_disjoint A hPA hc word ⟨ht,hr⟩)

/-- The same constructed semantic model gives theorem/refutation
consistency in the arithmetic ultrapower through the canonical transport. -/
theorem consistent_ultrapower_word_disjoint {I : Type} (U : Ultrafilter I)
    (word : ArithmeticUltrapower.Model U) :
    ¬ ((literalTheoremCarrier 𝗣𝗔 (variableCarrier : PredicateCategory 𝗣𝗔)
        functionSymbols relationSymbols bound A).val.Evalb ![word] ∧
      (literalRefutationCarrier 𝗣𝗔 (variableCarrier : PredicateCategory 𝗣𝗔)
        functionSymbols relationSymbols bound A).val.Evalb ![word]) := by
  rcases NamedGammaModel.exists_model A hPA hc with ⟨K,s,hK⟩
  let := s
  have : Nonempty K := ⟨0⟩
  exact ultrapower_word_disjoint functionSymbols relationSymbols bound A
    ArithmeticNamedTranslation.functions ArithmeticNamedTranslation.relations (fun _ => (0 : K)) hK U word

/-- The exact standard sentence-word endpoint used by the arithmetic
comparison: its printed Neg extension is the actual negation constructor. -/
theorem standard_sentence_evidence_disjoint (word : ℕ)
    (hs : (ConcreteNamedComparison.literalSentenceCarrier 𝗣𝗔 variableSymbols
      functionSymbols relationSymbols bound).val.Evalb ![word]) :
    ¬ ((literalTheoremCarrier 𝗣𝗔 variableSymbols functionSymbols relationSymbols bound A).val.Evalb ![word] ∧
      (literalTheoremCarrier 𝗣𝗔 variableSymbols functionSymbols relationSymbols bound A).val.Evalb
        ![NamedArithmeticProofSearch.negationWord ℕ word]) := by
  rintro ⟨ht,hn⟩
  have hx := ((ConcreteNamedComparison.literalSentenceCarrier_eval 𝗣𝗔
    variableSymbols functionSymbols relationSymbols bound ℕ word).mp hs).1
  have hg := (NamedArithmeticProofSearch.NegationCoding.constructor_graph_of_member
    𝗣𝗔 ℕ variableSymbols functionSymbols relationSymbols bound word
    (NamedArithmeticProofSearch.negationWord ℕ word) hx).mpr rfl
  apply consistent_standard_word_disjoint A hPA hc word
  exact ⟨ht,(literalRefutationCarrier_eval 𝗣𝗔 variableSymbols functionSymbols relationSymbols bound
    ℕ A word).mpr ⟨hs,NamedArithmeticProofSearch.negationWord ℕ word,hg,hn⟩⟩

/-- The exact nonstandard arithmetic-ultrapower endpoint, at every
literal sentence word, with the same fixed total Neg extension. -/
theorem ultrapower_sentence_evidence_disjoint {I : Type} (U : Ultrafilter I)
    (word : ArithmeticUltrapower.Model U)
    (hs : (ConcreteNamedComparison.literalSentenceCarrier 𝗣𝗔 variableSymbols
      functionSymbols relationSymbols bound).val.Evalb ![word]) :
    ¬ ((literalTheoremCarrier 𝗣𝗔 variableSymbols functionSymbols relationSymbols bound A).val.Evalb ![word] ∧
      (literalTheoremCarrier 𝗣𝗔 variableSymbols functionSymbols relationSymbols bound A).val.Evalb
        ![NamedArithmeticProofSearch.negationWord (ArithmeticUltrapower.Model U) word]) := by
  rintro ⟨ht,hn⟩
  have hx := ((ConcreteNamedComparison.literalSentenceCarrier_eval 𝗣𝗔
    variableSymbols functionSymbols relationSymbols bound (ArithmeticUltrapower.Model U) word).mp hs).1
  have hg := (NamedArithmeticProofSearch.NegationCoding.constructor_graph_of_member
    𝗣𝗔 (ArithmeticUltrapower.Model U) variableSymbols functionSymbols relationSymbols bound word
    (NamedArithmeticProofSearch.negationWord (ArithmeticUltrapower.Model U) word) hx).mpr rfl
  apply consistent_ultrapower_word_disjoint A hPA hc U word
  exact ⟨ht,(literalRefutationCarrier_eval 𝗣𝗔 variableSymbols functionSymbols relationSymbols bound
    (ArithmeticUltrapower.Model U) A word).mpr
      ⟨hs,NamedArithmeticProofSearch.negationWord (ArithmeticUltrapower.Model U) word,hg,hn⟩⟩

end Arithmetic
end CategoricalEssentialIncompleteness.V46.NamedGammaEvidenceSoundness
