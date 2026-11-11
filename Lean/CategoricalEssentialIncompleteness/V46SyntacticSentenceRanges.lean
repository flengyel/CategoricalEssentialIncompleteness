/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SyntacticSentenceImages
public import FailureOfComposition.TypedRanges

/-! # The source sentence-conclusion program and its explicit range idempotent -/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.Limits CategoryTheory.RestrictionCategory
open FailureOfComposition FailureOfComposition.TypedProgramCategory
open FailureOfComposition.TypedRanges FailureOfComposition.UniformIndexQuotient
open FailureOfComposition.ConcreteIndices
open FailureOfComposition.ProofSearch FailureOfComposition.ConcreteEvaluator
open CategoricalEssentialIncompleteness.LocalConnectedness
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates

namespace CategoricalEssentialIncompleteness.V46.SyntacticSentenceImages
variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
variable {P Fm S : PredicateCategory T}

/-- A standard program index for the actual constructed conclusion arrow. -/
def conclusionIndex (c : P ⟶ Fm) : ℕ :=
  SyntacticSearch.searchIndex (chosenGraph T c).graph

def sentenceGraph (c : P ⟶ Fm) (j : S ⟶ Fm) : Graph :=
  let G := eventualGraph (conclusionIndex T c)
  let C := sentenceCarrier T j
  .mkSigma “p z. !G.val p z ∧ !C.val z”

def sentenceDomain (c : P ⟶ Fm) (j : S ⟶ Fm) : Carrier :=
  let G := sentenceGraph T c j
  .mkSigma “p. ∃ z, !G.val p z”

/-- The literal predicate Th(z) = ∃p G_e(p,z) at the selected conclusion
index, before any replacement by a T-equivalent graph formula. -/
def programTheorems (c : P ⟶ Fm) : Carrier :=
  imageCarrier (eventualGraph (conclusionIndex T c))

@[simp] theorem programTheorems_eval (c : P ⟶ Fm)
    {M : Type} [ORingStructure M] (z : M) :
    (programTheorems T c).val.Evalb ![z] ↔
      ∃ p : M, (eventualGraph (conclusionIndex T c)).val.Evalb ![p,z] :=
  imageCarrier_eval _ z

def programTheoryCarrier (c : P ⟶ Fm) (j : S ⟶ Fm) : Carrier :=
  let C := sentenceCarrier T j
  let D := programTheorems T c
  .mkSigma “z. !C.val z ∧ !D.val z”

@[simp] theorem programTheoryCarrier_eval (c : P ⟶ Fm) (j : S ⟶ Fm)
    {M : Type} [ORingStructure M] (z : M) :
    (programTheoryCarrier T c j).val.Evalb ![z] ↔
      (sentenceCarrier T j).val.Evalb ![z] ∧
        ∃ p : M, (eventualGraph (conclusionIndex T c)).val.Evalb ![p,z] := by
  simp [programTheoryCarrier]

theorem programTheoryCarrier_theory (c : P ⟶ Fm) (j : S ⟶ Fm)
    (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T] (z : M) :
    (programTheoryCarrier T c j).val.Evalb ![z] ↔ (theoryCarrier T c j).val.Evalb ![z] := by
  rw [programTheoryCarrier_eval, theoryCarrier_eval, imageCarrier_eval]
  apply and_congr Iff.rfl
  apply exists_congr
  intro p
  exact SyntacticModel.uniform_model T M
    (SyntacticSearch.search_uniform_of_functional T (chosenGraph T c).graph
      (chosenGraph T c).functional) p z

@[simp] theorem sentenceGraph_eval (c : P ⟶ Fm) (j : S ⟶ Fm)
    {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T] (p z : M) :
    (sentenceGraph T c j).val.Evalb ![p,z] ↔
      (chosenGraph T c).graph.val.Evalb ![p,z] ∧ (sentenceCarrier T j).val.Evalb ![z] := by
  have h := SyntacticModel.uniform_model T M
    (SyntacticSearch.search_uniform_of_functional T (chosenGraph T c).graph
      (chosenGraph T c).functional) p z
  simpa [sentenceGraph, conclusionIndex] using
    and_congr h (Iff.refl ((sentenceCarrier T j).val.Evalb ![z]))

/-- The filtered program graph is functional in PA even when totality
of the original categorical conclusion arrow is proved only in T. -/
theorem sentenceGraph_functional_pa (c : P ⟶ Fm) (j : S ⟶ Fm) :
    𝗣𝗔 ⊢ functionalSentence (sentenceGraph T c j) := by
  apply complete.{0} 𝗣𝗔
  intro M _ _
  rw [models_iff, functionalSentence_eval]
  intro p z y hz hy
  have hz' : (eventualGraph (conclusionIndex T c)).val.Evalb ![p,z] ∧
      (sentenceCarrier T j).val.Evalb ![z] := by
    simpa [sentenceGraph] using hz
  have hy' : (eventualGraph (conclusionIndex T c)).val.Evalb ![p,y] ∧
      (sentenceCarrier T j).val.Evalb ![y] := by
    simpa [sentenceGraph] using hy
  exact FailureOfComposition.ConcreteEvaluator.eventualGraph_output_unique _ p z y hz'.1 hy'.1

def sentenceIndex (c : P ⟶ Fm) (j : S ⟶ Fm) : ℕ :=
  SyntacticSearch.searchIndex (sentenceGraph T c j)

theorem sentenceIndex_uniform_pa (c : P ⟶ Fm) (j : S ⟶ Fm) :
    Uniform 𝗣𝗔 (eventualGraph (sentenceIndex T c j)) (sentenceGraph T c j) :=
  SyntacticSearch.search_uniform_of_functional 𝗣𝗔 (sentenceGraph T c j)
    (sentenceGraph_functional_pa T c j)

@[simp] theorem sentenceDomain_eval (c : P ⟶ Fm) (j : S ⟶ Fm)
    {M : Type} [ORingStructure M] (p : M) :
    (sentenceDomain T c j).val.Evalb ![p] ↔
      ∃ z : M, (sentenceGraph T c j).val.Evalb ![p,z] := by
  simp [sentenceDomain]

/-- Witness search represents the actual filtered conclusion relation.
Its functionality has already been proved in PA above. -/
def sentenceMorphism (c : P ⟶ Fm) (j : S ⟶ Fm) :
    GraphMorphism T (sentenceDomain T c j) (sentenceCarrier T j) where
  graph := sentenceGraph T c j
  support := by
    apply complete.{0} T
    intro M _ _
    rw [models_iff, SyntacticPredicates.supportSentence_eval]
    intro p z h
    exact ⟨(sentenceDomain_eval T c j p).mpr ⟨z,h⟩, ((sentenceGraph_eval T c j p z).mp h).2⟩
  total := by
    apply complete.{0} T
    intro M _ _
    rw [models_iff, totalSentence_eval]
    intro p hp
    obtain ⟨z,hz⟩ := (sentenceDomain_eval T c j p).mp hp
    refine ⟨z,hz,?_⟩
    intro y hy
    have hg := (sentenceGraph_eval T c j p z).mp hz
    have hg' := (sentenceGraph_eval T c j p y).mp hy
    exact ((chosenGraph T c).total_model M p
      ((chosenGraph T c).support_model M p z hg.1).1).unique hg'.1 hg.1

def sentenceProgram (c : P ⟶ Fm) (j : S ⟶ Fm) : omegaObject T ⟶ omegaObject T :=
  omegaArrow T (sentenceMorphism T c j).programClass

theorem sentenceProgram_model (c : P ⟶ Fm) (j : S ⟶ Fm)
    (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T] (p z : M) :
    SyntacticModel.programRelation T M (sentenceProgram T c j).val p z ↔
      (chosenGraph T c).graph.val.Evalb ![p,z] ∧ (sentenceCarrier T j).val.Evalb ![z] := by
  change SyntacticModel.programRelation T M (sentenceMorphism T c j).programClass p z ↔ _
  rw [GraphMorphism.programClass_model]
  exact sentenceGraph_eval T c j p z

theorem rangeClass_model (q : ProgramQuotient T)
    (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T] (x y : M) :
    SyntacticModel.programRelation T M (rangeClass T q) x y ↔
      x = y ∧ ∃ p : M, SyntacticModel.programRelation T M q p x := by
  let : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 := models_of_subtheory (U := T) inferInstance
  induction q using Quotient.inductionOn with
  | _ q => exact rangeIndex_graph_equation q x y

/-- The selected range class is the literal sentence-and-theorem
partial identity on the original numerical object. -/
theorem sentenceProgram_rangeClass (c : P ⟶ Fm) (j : S ⟶ Fm) :
    rangeClass T (sentenceProgram T c j).val = predicateClass T (theoryCarrier T c j) := by
  apply programClass_ext T
  intro M _ _ x y
  rw [rangeClass_model, predicateClass_model, theoryCarrier_eval]
  constructor
  · rintro ⟨he,p,hp⟩
    have h := (sentenceProgram_model T c j M p x).mp hp
    exact ⟨⟨h.2, (imageCarrier_eval _ x).mpr ⟨p,h.1⟩⟩, he.symm⟩
  · rintro ⟨⟨hs,ht⟩,he⟩
    obtain ⟨p,hp⟩ := (imageCarrier_eval _ x).mp ht
    exact ⟨he.symm,p,(sentenceProgram_model T c j M p x).mpr ⟨hp,hs⟩⟩

theorem sentenceProgram_range (c : P ⟶ Fm) (j : S ⟶ Fm) :
    rangeArrow T (sentenceProgram T c j) = (theoryIdem T c j).hom := by
  apply CodedHom.ext
  change rangeClass T (sentenceProgram T c j).val = predicateClass T (theoryCarrier T c j)
  exact sentenceProgram_rangeClass T c j

/-- The range is exactly the literal restriction idempotent
[Sent(z) ∧ ∃p G_e(p,z)]_T appearing in the manuscript. -/
theorem sentenceProgram_range_literal (c : P ⟶ Fm) (j : S ⟶ Fm) :
    rangeArrow T (sentenceProgram T c j) =
      (predicateIdem T (programTheoryCarrier T c j)).hom := by
  rw [sentenceProgram_range]
  apply CodedHom.ext
  change predicateClass T (theoryCarrier T c j) =
    predicateClass T (programTheoryCarrier T c j)
  apply programClass_ext T
  intro M _ _ x y
  rw [predicateClass_model, predicateClass_model, programTheoryCarrier_theory]

theorem programTheory_inclusion (c : P ⟶ Fm) (j : S ⟶ Fm) :
    T ⊢ inclusionSentence (programTheoryCarrier T c j) (theoryCarrier T c j) := by
  apply complete.{0} T
  intro M _ _
  rw [models_iff, inclusionSentence_eval]
  intro z hz
  exact (programTheoryCarrier_theory T c j M z).mp hz

def programTheoryIso (c : P ⟶ Fm) (j : S ⟶ Fm) :
    CategoryTheory.Iso (C := PredicateCategory T)
      (programTheoryCarrier T c j) (theoryCarrier T c j) :=
  PredicateInterpretation.isoOfModelsBijective T
    (GraphMorphism.inclusion (programTheory_inclusion T c j)) (by
      intro M _ _
      constructor
      · intro x y hxy
        apply Subtype.ext
        simpa only [PredicateInterpretation.map_inclusion_val] using congrArg Subtype.val hxy
      · intro y
        let x : SyntacticLists.Obj T M (programTheoryCarrier T c j) :=
          ⟨y.val, (programTheoryCarrier_theory T c j M y.val).mpr y.property⟩
        exact ⟨x, Subtype.ext (PredicateInterpretation.map_inclusion_val T M _ x)⟩)

/-- The literal source idempotent's splitting represents the actual
generated sentence image, with the sentence chart proved above. -/
def programTheorySplittingIso (c : P ⟶ Fm) (j : S ⟶ Fm) [Mono j] :
    interpretedObject T (programTheoryCarrier T c j) ≅
      (realization T).obj (image (CategoryTheory.Limits.pullback.snd c j)) :=
  (realization T).mapIso (programTheoryIso T c j) ≪≫ theorySplittingIso T c j

end CategoricalEssentialIncompleteness.V46.SyntacticSentenceImages
