/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46NumericalArithmeticGraphs
import CategoricalEssentialIncompleteness.V46ArithmeticLiteralModel
import CategoricalEssentialIncompleteness.V46SyntacticPredicatesExtensive

/-! # The literal arithmetic sentence-proof word presentation

The stored element is the original successful derivation word. Its
conclusion and sentence witnesses are existential variables of the carrier.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.Limits
open FailureOfComposition.ProofSearch
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticLists

namespace CategoricalEssentialIncompleteness.V46.NumericalArithmetic.ProofWords
open NamedArithmeticSignature
abbrev arithmeticSyntax := ArithmeticLiteralModel.sentenceSyntax
abbrev sentences := ArithmeticLiteralModel.sentencePredicate
abbrev allProofs (Γ : Carrier) : PredicateCategory 𝗣𝗔 :=
  (SyntacticGeneratedAxioms.proofs 𝗣𝗔 variableSymbols functionSymbols relationSymbols bound Γ).a.left
abbrev formulaConclusion (Γ : Carrier) := ArithmeticLiteralModel.formulaConclusion Γ

/-- The original proof word is the sole carrier coordinate. -/
def carrier (Γ : Carrier) : Carrier :=
  let H := (chosenGraph 𝗣𝗔 (formulaConclusion Γ)).graph
  .mkSigma “p. ∃ z, !H.val p z ∧ !sentences.val z”

def conclusionGraph (Γ : Carrier) : Graph :=
  let H := (chosenGraph 𝗣𝗔 (formulaConclusion Γ)).graph
  .mkSigma “p z. !H.val p z ∧ !sentences.val z”

section Models
variable (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

@[simp] theorem carrier_eval (Γ : Carrier) (p : M) :
    (carrier Γ).val.Evalb ![p] ↔ ∃ z : M,
      (chosenGraph 𝗣𝗔 (formulaConclusion Γ)).graph.val.Evalb ![p,z] ∧
        sentences.val.Evalb ![z] := by
  simp [carrier]

@[simp] theorem conclusionGraph_eval (Γ : Carrier) (p z : M) :
    (conclusionGraph Γ).val.Evalb ![p,z] ↔
      (chosenGraph 𝗣𝗔 (formulaConclusion Γ)).graph.val.Evalb ![p,z] ∧
        sentences.val.Evalb ![z] := by
  simp [conclusionGraph]

end Models

/-- The conclusion uses the graph of the constructed derivation algebra. -/
def conclusion (Γ : Carrier) : GraphMorphism 𝗣𝗔 (carrier Γ) sentences where
  graph := conclusionGraph Γ
  support := by
    apply complete.{0} 𝗣𝗔
    intro M _ _
    rw [models_iff,supportSentence_eval]
    intro p z h
    obtain ⟨hp,hz⟩ := (conclusionGraph_eval M Γ p z).mp h
    exact ⟨(carrier_eval M Γ p).mpr ⟨z,hp,hz⟩,hz⟩
  total := by
    apply complete.{0} 𝗣𝗔
    intro M _ _
    rw [models_iff,totalSentence_eval]
    intro p hp
    obtain ⟨z,hpz,hz⟩ := (carrier_eval M Γ p).mp hp
    refine ⟨z,(conclusionGraph_eval M Γ p z).mpr ⟨hpz,hz⟩,?_⟩
    intro y hy
    have hpy := ((conclusionGraph_eval M Γ p y).mp hy).1
    exact ((chosenGraph 𝗣𝗔 (formulaConclusion Γ)).total_model M p
      (((chosenGraph 𝗣𝗔 (formulaConclusion Γ)).support_model M p z hpz).1)).unique hpy hpz

private theorem included (Γ : Carrier) :
    𝗣𝗔 ⊢ inclusionSentence (carrier Γ) (allProofs Γ) := by
  apply complete.{0} 𝗣𝗔
  intro M _ _
  rw [models_iff,inclusionSentence_eval]
  intro p hp
  obtain ⟨z,hpz,_⟩ := (carrier_eval M Γ p).mp hp
  exact ((chosenGraph 𝗣𝗔 (formulaConclusion Γ)).support_model M p z hpz).1

/-- Forgetting the sentence restriction retains the very same proof word. -/
def inclusion (Γ : Carrier) : GraphMorphism 𝗣𝗔 (carrier Γ) (allProofs Γ) :=
  GraphMorphism.inclusion (included Γ)

section Models
variable (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

@[simp] theorem inclusion_value (Γ : Carrier) (p : Obj 𝗣𝗔 M (carrier Γ)) :
    ((F 𝗣𝗔 M).map (representedArrow 𝗣𝗔 (inclusion Γ)) p).val = p.val := by
  have h := (PredicateInterpretation.map_class_eq_iff 𝗣𝗔 M (inclusion Γ) p
    ((F 𝗣𝗔 M).map (representedArrow 𝗣𝗔 (inclusion Γ)) p)).mp rfl
  exact ((GraphMorphism.identityGraph_eval (carrier Γ) _ _).mp h).2

/-- The conclusion graph agrees with the original formula conclusion on
all models, including nonstandard proof words. -/
theorem conclusion_value (Γ : Carrier) (p : Obj 𝗣𝗔 M (carrier Γ)) :
    ((F 𝗣𝗔 M).map (formulaConclusion Γ)
      ((F 𝗣𝗔 M).map (representedArrow 𝗣𝗔 (inclusion Γ)) p)).val =
      ((F 𝗣𝗔 M).map (representedArrow 𝗣𝗔 (conclusion Γ)) p).val := by
  let z := (F 𝗣𝗔 M).map (representedArrow 𝗣𝗔 (conclusion Γ)) p
  have hg := (PredicateInterpretation.map_class_eq_iff 𝗣𝗔 M (conclusion Γ) p z).mp rfl
  have hf := ((conclusionGraph_eval M Γ p.val z.val).mp hg).1
  apply (ConcreteNamedComparison.chosenGraph_value_iff 𝗣𝗔 M (formulaConclusion Γ) _ z.val).mp
  simpa only [inclusion_value] using hf

end Models

theorem square (Γ : Carrier) :
    representedArrow 𝗣𝗔 (inclusion Γ) ≫ formulaConclusion Γ =
      (representedArrow 𝗣𝗔 (conclusion Γ) ≫ ArithmeticLiteralModel.sentenceChart.hom) ≫
        arithmeticSyntax.sentenceInclusion := by
  apply PredicateInterpretation.jointly_faithful 𝗣𝗔
  intro M _ _
  apply ConcreteCategory.hom_ext
  intro p
  apply Subtype.ext
  simp only [Functor.map_comp_apply]
  exact (conclusion_value M Γ p).trans
    (ArithmeticLiteralModel.chart_value M ((F 𝗣𝗔 M).map
      (representedArrow 𝗣𝗔 (conclusion Γ)) p)).symm

/-- The map into the actual sentence-conclusion pullback. -/
def comparison (Γ : Carrier) : @Quiver.Hom (PredicateCategory 𝗣𝗔) inferInstance
    (carrier Γ) (ArithmeticLiteralModel.proofObject Γ) :=
  pullback.lift (representedArrow 𝗣𝗔 (inclusion Γ))
    (representedArrow 𝗣𝗔 (conclusion Γ) ≫ ArithmeticLiteralModel.sentenceChart.hom) (square Γ)

@[reassoc (attr := simp)] theorem comparison_tree (Γ : Carrier) :
    comparison Γ ≫ pullback.fst (formulaConclusion Γ) arithmeticSyntax.sentenceInclusion =
      representedArrow 𝗣𝗔 (inclusion Γ) := by
  simp [comparison]

@[reassoc (attr := simp)] theorem comparison_sentence (Γ : Carrier) :
    comparison Γ ≫ ArithmeticLiteralModel.conclusion Γ = representedArrow 𝗣𝗔 (conclusion Γ) := by
  simp [comparison,ArithmeticLiteralModel.conclusion,SyntacticGeneratedTheory.sentenceConclusion,
    Category.assoc]

/-- The inverse reuses the graph of the original proof projection.
Its target support is proved from the pullback equation at graph level. -/
def backward (Γ : Carrier) : GraphMorphism 𝗣𝗔 (ArithmeticLiteralModel.proofObject Γ) (carrier Γ) where
  graph := (chosenGraph 𝗣𝗔 (pullback.fst (formulaConclusion Γ) arithmeticSyntax.sentenceInclusion)).graph
  support := by
    apply complete.{0} 𝗣𝗔
    intro M _ _
    rw [models_iff,supportSentence_eval]
    intro x p hxp
    let g := pullback.fst (formulaConclusion Γ) arithmeticSyntax.sentenceInclusion
    have hs := (chosenGraph 𝗣𝗔 g).support_model M x p hxp
    obtain ⟨z,hpz,_⟩ := (chosenGraph 𝗣𝗔 (formulaConclusion Γ)).total_model M p hs.2
    have hr : relation 𝗣𝗔 (g ≫ formulaConclusion Γ) M x z :=
      (relation_comp 𝗣𝗔 g (formulaConclusion Γ) M x z).mpr
        ⟨p,(chosenGraph_eval 𝗣𝗔 g M x p).mp hxp,
          (chosenGraph_eval 𝗣𝗔 (formulaConclusion Γ) M p z).mp hpz⟩
    have he : g ≫ formulaConclusion Γ =
        pullback.snd (formulaConclusion Γ) arithmeticSyntax.sentenceInclusion ≫
          arithmeticSyntax.sentenceInclusion := pullback.condition
    rw [he] at hr
    obtain ⟨w,_,hwz⟩ := (relation_comp 𝗣𝗔
      (pullback.snd (formulaConclusion Γ) arithmeticSyntax.sentenceInclusion)
      arithmeticSyntax.sentenceInclusion M x z).mp hr
    let ww : Obj 𝗣𝗔 M arithmeticSyntax.sentenceObject :=
      ⟨w,(relation_support 𝗣𝗔 arithmeticSyntax.sentenceInclusion M w z hwz).1⟩
    have hword : ((F 𝗣𝗔 M).map arithmeticSyntax.sentenceInclusion ww).val = z :=
      (ConcreteNamedComparison.chosenGraph_value_iff 𝗣𝗔 M arithmeticSyntax.sentenceInclusion ww z).mp
        ((chosenGraph_eval 𝗣𝗔 arithmeticSyntax.sentenceInclusion M w z).mpr hwz)
    have hz : sentences.val.Evalb ![z] :=
      (SyntacticGeneratedAxioms.sentence_points 𝗣𝗔 variableSymbols functionSymbols relationSymbols
        bound M z).mpr ⟨ww,hword⟩
    exact ⟨hs.1,(carrier_eval M Γ p).mpr ⟨z,hpz,hz⟩⟩
  total := (chosenGraph 𝗣𝗔 (pullback.fst (formulaConclusion Γ) arithmeticSyntax.sentenceInclusion)).total

theorem backward_tree (Γ : Carrier) :
    representedArrow 𝗣𝗔 (backward Γ) ≫ representedArrow 𝗣𝗔 (inclusion Γ) =
      pullback.fst (formulaConclusion Γ) arithmeticSyntax.sentenceInclusion := by
  apply hom_ext 𝗣𝗔
  intro M _ _ x p
  rw [relation_comp]
  constructor
  · rintro ⟨y,hxy,hyp⟩
    have he := (GraphMorphism.identityGraph_eval (carrier Γ) y p).mp
      ((relation_class 𝗣𝗔 (inclusion Γ) M y p).mp hyp)
    simpa only [he.2] using (chosenGraph_eval 𝗣𝗔
      (pullback.fst (formulaConclusion Γ) arithmeticSyntax.sentenceInclusion) M x y).mp
        ((relation_class 𝗣𝗔 (backward Γ) M x y).mp hxy)
  · intro hxp
    have hg := (chosenGraph_eval 𝗣𝗔
      (pullback.fst (formulaConclusion Γ) arithmeticSyntax.sentenceInclusion) M x p).mpr hxp
    exact ⟨p,(relation_class 𝗣𝗔 (backward Γ) M x p).mpr hg,
      (relation_class 𝗣𝗔 (inclusion Γ) M p p).mpr
        ((GraphMorphism.identityGraph_eval (carrier Γ) p p).mpr
          ⟨((backward Γ).support_model M x p hg).2,rfl⟩)⟩

theorem comparison_isIso (Γ : Carrier) : IsIso (comparison Γ) := by
  let _ : Mono (representedArrow 𝗣𝗔 (inclusion Γ)) := inclusion_mono (included Γ)
  refine ⟨⟨representedArrow 𝗣𝗔 (backward Γ),?_,?_⟩⟩
  · apply (cancel_mono (representedArrow 𝗣𝗔 (inclusion Γ))).mp
    rw [Category.assoc,backward_tree,comparison_tree,Category.id_comp]
  · apply (cancel_mono (pullback.fst (formulaConclusion Γ) arithmeticSyntax.sentenceInclusion)).mp
    rw [Category.assoc,comparison_tree,backward_tree,Category.id_comp]

/-- This is an isomorphism over the literal sentence object, and its
underlying tree map retains the original successful word. -/
def iso (Γ : Carrier) : @CategoryTheory.Iso (PredicateCategory 𝗣𝗔) inferInstance
    (carrier Γ) (ArithmeticLiteralModel.proofObject Γ) := by
  letI := comparison_isIso Γ
  exact asIso (comparison Γ)

@[reassoc (attr := simp)] theorem iso_conclusion (Γ : Carrier) :
    (iso Γ).hom ≫ ArithmeticLiteralModel.conclusion Γ = representedArrow 𝗣𝗔 (conclusion Γ) :=
  comparison_sentence Γ

section Models
variable (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

/-- The image of this word conclusion is the previously fixed Gamma
provability predicate, rather than a new proof presentation. -/
theorem fixed_provability (Γ : Carrier) (z : M) :
    (imageCarrier (conclusion Γ).graph).val.Evalb ![z] ↔
      (ArithmeticLiteralModel.theoremPredicate Γ).val.Evalb ![z] := by
  rw [imageCarrier_eval,SyntacticGeneratedAxioms.literalTheoremCarrier_model,
    SyntacticGeneratedAxioms.theoremCarrier_model]
  constructor
  · rintro ⟨p,hp⟩
    obtain ⟨hc,hs⟩ := (conclusionGraph_eval M Γ p z).mp hp
    let pp : Obj 𝗣𝗔 M (allProofs Γ) := ⟨p,((chosenGraph 𝗣𝗔 (formulaConclusion Γ)).support_model M p z hc).1⟩
    exact ⟨hs,pp,(ConcreteNamedComparison.chosenGraph_value_iff 𝗣𝗔 M (formulaConclusion Γ) pp z).mp hc⟩
  · rintro ⟨hs,p,hp⟩
    exact ⟨p.val,(conclusionGraph_eval M Γ p.val z).mpr
      ⟨(ConcreteNamedComparison.chosenGraph_value_iff 𝗣𝗔 M (formulaConclusion Γ) p z).mpr hp,hs⟩⟩

end Models
end CategoricalEssentialIncompleteness.V46.NumericalArithmetic.ProofWords
