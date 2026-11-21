/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ConcreteNamedComparisonSentences

/-! # The concrete sentence-axiom subobject of a Sigma-one enumeration -/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticLists
namespace CategoricalEssentialIncompleteness.V46.SyntacticAxiomPredicates
open SyntacticSyntax SyntacticSentenceImages ConcreteNamedComparison
variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
variable (V : PredicateCategory T) (σ π : ℕ → PredicateCategory T) (d : ℕ)
local notation "S" => plainCategoricalSyntax T V σ π d

/-- A Sigma-one enumeration is filtered by the sentence image. The source word remains its
formula coordinate, not the pullback code. -/
def axiomCarrier (Γ : Carrier) : Carrier :=
  let Sent := sentenceCarrier T (S).sentenceInclusion
  .mkSigma “word. !Γ.val word ∧ !Sent.val word”

theorem axiomInclusionProof (Γ : Carrier) :
    T ⊢ inclusionSentence (axiomCarrier T V σ π d Γ) (sentenceCarrier T (S).sentenceInclusion) := by
  apply complete.{0} T
  intro M _ _
  rw [models_iff,inclusionSentence_eval]
  intro word hw
  exact (show Γ.val.Evalb ![word] ∧
    (sentenceCarrier T (S).sentenceInclusion).val.Evalb ![word] by
      simpa [axiomCarrier] using hw).2

def axiomImageInclusion (Γ : Carrier) :
    @Quiver.Hom (PredicateCategory T) inferInstance
      (axiomCarrier T V σ π d Γ) (sentenceCarrier T (S).sentenceInclusion) :=
  representedArrow T (GraphMorphism.inclusion (axiomInclusionProof T V σ π d Γ))

/-- The axiom subobject of the chosen sentence pullback. -/
def axioms (Γ : Carrier) :
    @Quiver.Hom (PredicateCategory T) inferInstance (axiomCarrier T V σ π d Γ) (S).sentenceObject :=
  axiomImageInclusion T V σ π d Γ ≫ (sentenceChart T (S).sentenceInclusion).inv

instance axioms_mono (Γ : Carrier) : Mono (axioms T V σ π d Γ) := by
  unfold axioms axiomImageInclusion
  infer_instance

theorem axioms_formula (Γ : Carrier) :
    axioms T V σ π d Γ ≫ (S).sentenceInclusion =
      axiomImageInclusion T V σ π d Γ ≫
        representedArrow T (GraphMorphism.inclusion (chosenGraph T (S).sentenceInclusion).imageInclusionProof) := by
  have hc : (sentenceChart T (S).sentenceInclusion).inv ≫ (S).sentenceInclusion =
      representedArrow T (GraphMorphism.inclusion (chosenGraph T (S).sentenceInclusion).imageInclusionProof) := by
    apply (cancel_epi (sentenceChart T (S).sentenceInclusion).hom).mp
    rw [← Category.assoc,Iso.hom_inv_id,Category.id_comp]
    exact (sentenceChart_over T (S).sentenceInclusion).symm
  unfold axioms
  rw [Category.assoc,hc]

section Models
variable (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T]

omit [M↓[ℒₒᵣ] ⊧* T] in
@[simp] theorem axiomCarrier_eval (Γ : Carrier) (word : M) :
    (axiomCarrier T V σ π d Γ).val.Evalb ![word] ↔
      Γ.val.Evalb ![word] ∧ (sentenceCarrier T (S).sentenceInclusion).val.Evalb ![word] := by
  simp [axiomCarrier]

/-- The filter is exactly the intended plain formula predicate with
empty numerical FV, uniformly at arbitrary internal words. -/
theorem axiomCarrier_literal (Γ : Carrier) (word : M) :
    (axiomCarrier T V σ π d Γ).val.Evalb ![word] ↔
      Γ.val.Evalb ![word] ∧ (literalSentenceCarrier T V σ π d).val.Evalb ![word] := by
  let : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 := models_of_subtheory (U := T) inferInstance
  rw [axiomCarrier_eval,sentenceCarrier_literal T V σ π d M word]

theorem axioms_formula_value (Γ : Carrier) (a : Obj T M (axiomCarrier T V σ π d Γ)) :
    ((F T M).map (axioms T V σ π d Γ ≫ (S).sentenceInclusion) a).val = a.val := by
  rw [axioms_formula,Functor.map_comp_apply]
  simp only [axiomImageInclusion,PredicateInterpretation.map_inclusion_val]

/-- The formula-coordinate axiom image is the supplied enumeration intersected with the
intended sentence codes. -/
theorem axioms_formula_image (Γ : Carrier) (word : M) :
    (imageCarrier (chosenGraph T (axioms T V σ π d Γ ≫ (S).sentenceInclusion)).graph).val.Evalb ![word] ↔
      Γ.val.Evalb ![word] ∧ (literalSentenceCarrier T V σ π d).val.Evalb ![word] := by
  let f := axioms T V σ π d Γ ≫ (S).sentenceInclusion
  rw [← axiomCarrier_literal T V σ π d M Γ word]
  change (imageCarrier (chosenGraph T f).graph).val.Evalb ![word] ↔ _
  rw [imageCarrier_eval]
  constructor
  · rintro ⟨a,ha⟩
    let aa : Obj T M (axiomCarrier T V σ π d Γ) :=
      ⟨a,((chosenGraph T f).support_model M a word ha).1⟩
    let ww : Obj T M (S).algebra.a.2 :=
      ⟨word,((chosenGraph T f).support_model M a word ha).2⟩
    have he : (F T M).map f aa = ww := (chosenGraph_map_iff T M f aa ww).mp ha
    have hv : aa.val = word := (axioms_formula_value T V σ π d M Γ aa).symm.trans
      (congrArg Subtype.val he)
    exact hv ▸ aa.property
  · intro hw
    let aa : Obj T M (axiomCarrier T V σ π d Γ) := ⟨word,hw⟩
    let ww := (F T M).map f aa
    have hval : ww.val = word := axioms_formula_value T V σ π d M Γ aa
    have hgraph := (chosenGraph_map_iff T M f aa ww).mpr rfl
    exact ⟨word,by simpa only [hval] using hgraph⟩

end Models

def axiomCarrierLiteralSentence (Γ : Carrier) : ArithmeticSentence :=
  let C := axiomCarrier T V σ π d Γ
  let Sent := literalSentenceCarrier T V σ π d
  “∀ word, !C.val word ↔ !Γ.val word ∧ !Sent.val word”

theorem axiomCarrier_literal_theory (Γ : Carrier) : T ⊢ axiomCarrierLiteralSentence T V σ π d Γ := by
  apply complete.{0} T
  intro M _ _
  simpa [models_iff,axiomCarrierLiteralSentence] using
    (fun word : M => axiomCarrier_literal T V σ π d M Γ word)

end CategoricalEssentialIncompleteness.V46.SyntacticAxiomPredicates
