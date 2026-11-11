/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SyntacticSyntaxGeometry
public import CategoricalEssentialIncompleteness.V46PredicateInterpretationRegular
public import CategoricalEssentialIncompleteness.V46SyntacticPredicatesRegular
public import CategoricalEssentialIncompleteness.V46SyntacticPredicatesExtensive
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks

/-! # Sentence and theorem predicates use the same formula-code coordinate -/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.Limits CategoryTheory.RestrictionCategory
open FailureOfComposition.TypedProgramCategory
open CategoricalEssentialIncompleteness.LocalConnectedness
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticLists

namespace CategoricalEssentialIncompleteness.V46.SyntacticSentenceImages
variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
variable {P Fm S : PredicateCategory T}

/-- Sentence codes are formula codes in the image of the actual sentence
inclusion; the chosen pullback object can have different raw codes. -/
def sentenceCarrier (j : S ⟶ Fm) : Carrier := imageCarrier (chosenGraph T j).graph

theorem exists_sentenceChart (j : S ⟶ Fm) [Mono j] :
    ∃ i : CategoryTheory.Iso (C := PredicateCategory T) S (sentenceCarrier T j),
      i.hom ≫ representedArrow T
        (GraphMorphism.inclusion (chosenGraph T j).imageInclusionProof) = j := by
  let f := chosenGraph T j
  let : Mono (representedArrow T f) := by rw [chosenGraph_class]; infer_instance
  obtain ⟨i, hi⟩ := represented_mono_image_iso T f
  exact ⟨i, hi.trans (chosenGraph_class T j)⟩

def sentenceChart (j : S ⟶ Fm) [Mono j] :
    CategoryTheory.Iso (C := PredicateCategory T) S (sentenceCarrier T j) :=
  Classical.choose (exists_sentenceChart T j)

@[reassoc] theorem sentenceChart_over (j : S ⟶ Fm) [Mono j] :
    (sentenceChart T j).hom ≫ representedArrow T
      (GraphMorphism.inclusion (chosenGraph T j).imageInclusionProof) = j :=
  Classical.choose_spec (exists_sentenceChart T j)

def restrictedConclusion (c : P ⟶ Fm) (j : S ⟶ Fm) [Mono j] :
    pullback c j ⟶ (sentenceCarrier T j : PredicateCategory T) :=
  pullback.snd c j ≫ (sentenceChart T j).hom

/-- Both conjuncts are predicates on formula codes, independent of the
chosen numerical presentation of the sentence pullback object. -/
def theoryCarrier (c : P ⟶ Fm) (j : S ⟶ Fm) : Carrier :=
  let C := sentenceCarrier T j
  let D := imageCarrier (chosenGraph T c).graph
  .mkSigma “z. !C.val z ∧ !D.val z”

@[simp] theorem theoryCarrier_eval (c : P ⟶ Fm) (j : S ⟶ Fm)
    {M : Type} [ORingStructure M] (z : M) :
    (theoryCarrier T c j).val.Evalb ![z] ↔
      (sentenceCarrier T j).val.Evalb ![z] ∧
        (imageCarrier (chosenGraph T c).graph).val.Evalb ![z] := by
  simp [theoryCarrier]

section Models
variable (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T]

theorem sentenceChart_value (j : S ⟶ Fm) [Mono j] (s : Obj T M S) :
    ((F T M).map (sentenceChart T j).hom s).val = ((F T M).map j s).val := by
  have h := congrArg (fun f : S ⟶ Fm => (F T M).map f s) (sentenceChart_over T j)
  rw [Functor.map_comp_apply] at h
  simpa only [PredicateInterpretation.map_inclusion_val] using congrArg Subtype.val h

/-- The represented restricted image is exactly Sent(z) and Th(z),
at arbitrary elements of every T-model. -/
theorem restrictedImage_eval (c : P ⟶ Fm) (j : S ⟶ Fm) [Mono j] (z : M) :
    (imageCarrier (chosenGraph T (restrictedConclusion T c j)).graph).val.Evalb ![z] ↔
      (theoryCarrier T c j).val.Evalb ![z] := by
  rw [theoryCarrier_eval]
  constructor
  · intro hz
    obtain ⟨w, hw⟩ := (imageCarrier_eval _ z).mp hz
    let g := chosenGraph T (restrictedConclusion T c j)
    let ww : Obj T M (pullback c j) := ⟨w, (g.support_model M w z hw).1⟩
    let zz : Obj T M (sentenceCarrier T j) := ⟨z, (g.support_model M w z hw).2⟩
    have hg : (F T M).map (restrictedConclusion T c j) ww = zz :=
      (chosenGraph_map_iff T M _ ww zz).mp hw
    let pp := (F T M).map (pullback.fst c j) ww
    let ss := (F T M).map (pullback.snd c j) ww
    have hc : (F T M).map c pp = (F T M).map j ss := by
      have h := congrArg (F T M).map (pullback.condition (f := c) (g := j))
      rw [Functor.map_comp, Functor.map_comp] at h
      exact ConcreteCategory.congr_hom h ww
    have hvalue : ((F T M).map j ss).val = z := by
      have hg' : (F T M).map (sentenceChart T j).hom ss = zz := by
        simpa only [restrictedConclusion, Functor.map_comp_apply] using hg
      exact (sentenceChart_value T M j ss).symm.trans (congrArg Subtype.val hg')
    let ff : Obj T M Fm := ⟨z,
      inclusion_model T (chosenGraph T j).imageInclusionProof M z zz.property⟩
    have he : (F T M).map c pp = ff := Subtype.ext ((congrArg Subtype.val hc).trans hvalue)
    exact ⟨zz.property, (imageCarrier_eval _ z).mpr
      ⟨pp.val, (chosenGraph_map_iff T M c pp ff).mpr he⟩⟩
  · rintro ⟨hsent, hth⟩
    obtain ⟨p, hp⟩ := (imageCarrier_eval _ z).mp hth
    let pp : Obj T M P := ⟨p, ((chosenGraph T c).support_model M p z hp).1⟩
    let zz : Obj T M (sentenceCarrier T j) := ⟨z, hsent⟩
    let ss := (F T M).map (sentenceChart T j).inv zz
    have hs : (F T M).map (sentenceChart T j).hom ss = zz := by
      have h := congrArg (F T M).map (sentenceChart T j).inv_hom_id
      rw [Functor.map_comp, (F T M).map_id] at h
      exact ConcreteCategory.congr_hom h zz
    have hv : ((F T M).map j ss).val = z :=
      (sentenceChart_value T M j ss).symm.trans (congrArg Subtype.val hs)
    let ff : Obj T M Fm := ⟨z, ((chosenGraph T c).support_model M p z hp).2⟩
    have hc : (F T M).map c pp = ff := (chosenGraph_map_iff T M c pp ff).mp hp
    have hcs : (F T M).map c pp = (F T M).map j ss :=
      hc.trans (Subtype.ext hv).symm
    obtain ⟨ww, hw₁, hw₂⟩ := Types.exists_of_isPullback
      ((F T M).map_isPullback (IsPullback.of_hasPullback c j)) pp ss hcs
    have hg : (F T M).map (restrictedConclusion T c j) ww = zz := by
      change (F T M).map (pullback.snd c j ≫ (sentenceChart T j).hom) ww = zz
      rw [(F T M).map_comp]
      change (F T M).map (sentenceChart T j).hom ((F T M).map (pullback.snd c j) ww) = zz
      rw [hw₂]
      exact hs
    exact (imageCarrier_eval _ z).mpr
      ⟨ww.val, (chosenGraph_map_iff T M _ ww zz).mpr hg⟩

end Models

theorem restrictedImage_inclusion (c : P ⟶ Fm) (j : S ⟶ Fm) [Mono j] :
    T ⊢ inclusionSentence
      (imageCarrier (chosenGraph T (restrictedConclusion T c j)).graph) (theoryCarrier T c j) := by
  apply complete.{0} T
  intro M _ _
  rw [models_iff, inclusionSentence_eval]
  intro z hz
  exact (restrictedImage_eval T M c j z).mp hz

/-- The comparison is the actual partial-identity inclusion; its
inverse is the represented converse graph supplied by model bijectivity. -/
def restrictedImageIso (c : P ⟶ Fm) (j : S ⟶ Fm) [Mono j] :
    CategoryTheory.Iso (C := PredicateCategory T)
      (imageCarrier (chosenGraph T (restrictedConclusion T c j)).graph) (theoryCarrier T c j) :=
  PredicateInterpretation.isoOfModelsBijective T
    (GraphMorphism.inclusion (restrictedImage_inclusion T c j)) (by
      intro M _ _
      constructor
      · intro x y hxy
        apply Subtype.ext
        simpa only [PredicateInterpretation.map_inclusion_val] using congrArg Subtype.val hxy
      · intro y
        let x : Obj T M (imageCarrier (chosenGraph T (restrictedConclusion T c j)).graph) :=
          ⟨y.val, (restrictedImage_eval T M c j y.val).mpr y.property⟩
        exact ⟨x, Subtype.ext (PredicateInterpretation.map_inclusion_val T M _ x)⟩)

/-- The chosen sentence-conclusion image is isomorphic to the explicit
intersection predicate on formula codes. -/
def sentenceImageIso (c : P ⟶ Fm) (j : S ⟶ Fm) [Mono j] :
    CategoryTheory.Iso (C := PredicateCategory T)
      (image (pullback.snd c j)) (theoryCarrier T c j) := by
  let f := chosenGraph T (restrictedConclusion T c j)
  let e := representedArrow T f.corestriction
  let m := representedArrow T (GraphMorphism.inclusion f.imageInclusionProof)
  let n := m ≫ (sentenceChart T j).inv
  let : IsSplitEpi e := f.corestriction.isSplitEpi_of_surjective f.corestriction_surjective
  have hfac : e ≫ n = pullback.snd c j := by
    dsimp only [n]
    rw [← Category.assoc, f.image_factor, chosenGraph_class]
    change (pullback.snd c j ≫ (sentenceChart T j).hom) ≫ (sentenceChart T j).inv = _
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  exact (image.isoStrongEpiMono e n hfac).symm ≪≫ restrictedImageIso T c j

/-- The source restriction idempotent has the explicit sentence-and-theorem
predicate as its domain on the original number object. -/
def theoryIdem (c : P ⟶ Fm) (j : S ⟶ Fm) : Idem (omegaObject T) :=
  predicateIdem T (theoryCarrier T c j)

theorem theoryIdem_model (c : P ⟶ Fm) (j : S ⟶ Fm)
    (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T] (x y : M) :
    SyntacticModel.programRelation T M (theoryIdem T c j).hom.val x y ↔
      (sentenceCarrier T j).val.Evalb ![x] ∧
        (∃ p : M, (chosenGraph T c).graph.val.Evalb ![p,x]) ∧ y = x := by
  change SyntacticModel.programRelation T M (predicateClass T (theoryCarrier T c j)) x y ↔ _
  rw [predicateClass_model, theoryCarrier_eval, imageCarrier_eval]
  constructor
  · rintro ⟨⟨hs, ht⟩, he⟩
    exact ⟨hs, ht, he⟩
  · rintro ⟨hs, ht, he⟩
    exact ⟨⟨hs, ht⟩, he⟩

/-- The splitting of the source idempotent represents the actual
sentence-conclusion image after the proved predicate equivalence. -/
def theorySplittingIso (c : P ⟶ Fm) (j : S ⟶ Fm) [Mono j] :
    interpretedObject T (theoryCarrier T c j) ≅
      (realization T).obj (image (pullback.snd c j)) :=
  ((realization T).mapIso (sentenceImageIso T c j)).symm

end CategoricalEssentialIncompleteness.V46.SyntacticSentenceImages
