/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ConcreteNamedComparisonSentences
public import CategoricalEssentialIncompleteness.V46SyntacticPredicatesExtensive

/-! # The literal sentence predicate and the actual chosen sentence object -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticLists
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax
namespace CategoricalEssentialIncompleteness.V46.SyntacticSentenceLiteralChart
open ConcreteNamedComparison SyntacticSentenceImages
variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
variable (V : PredicateCategory T) (σ π : ℕ → PredicateCategory T) (d : ℕ)
local notation "S" => plainCategoricalSyntax T V σ π d

theorem toImageProof : T ⊢ inclusionSentence (literalSentenceCarrier T V σ π d)
    (sentenceCarrier T (S).sentenceInclusion) := by
  apply complete.{0} T
  intro M _ _
  let : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 := models_of_subtheory (U := T) inferInstance
  rw [models_iff,inclusionSentence_eval]
  intro word hw
  exact (sentenceCarrier_literal T V σ π d M word).mpr hw

/-- This morphism preserves the displayed word and has the actual
image of the chosen sentence inclusion as its target. -/
def toImage : @Quiver.Hom (PredicateCategory T) inferInstance
    (literalSentenceCarrier T V σ π d) (sentenceCarrier T (S).sentenceInclusion) :=
  representedArrow T (GraphMorphism.inclusion (toImageProof T V σ π d))

instance toImage_isIso : IsIso (toImage T V σ π d) := by
  apply PredicateInterpretation.isIso_of_models_bijective T
  intro M _ _
  let : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 := models_of_subtheory (U := T) inferInstance
  constructor
  · intro x y h
    apply Subtype.ext
    have he := congrArg Subtype.val h
    simpa only [toImage,PredicateInterpretation.map_inclusion_val] using he
  · intro y
    let x : Obj T M (literalSentenceCarrier T V σ π d) :=
      ⟨y.val,(sentenceCarrier_literal T V σ π d M y.val).mp y.property⟩
    refine ⟨x,?_⟩
    apply Subtype.ext
    exact PredicateInterpretation.map_inclusion_val T M (toImageProof T V σ π d) x

/-- The isomorphism combines the proved predicate inclusion with
the existing image chart. -/
def toSentenceIso : CategoryTheory.Iso (C := PredicateCategory T)
    (literalSentenceCarrier T V σ π d) (S).sentenceObject :=
  asIso (toImage T V σ π d) ≪≫ (sentenceChart T (S).sentenceInclusion).symm

def toSentence : @Quiver.Hom (PredicateCategory T) inferInstance
    (literalSentenceCarrier T V σ π d) (S).sentenceObject :=
  (toSentenceIso T V σ π d).hom

instance toSentence_isIso : IsIso (toSentence T V σ π d) := by
  unfold toSentence
  infer_instance

def imageInclusion : @Quiver.Hom (PredicateCategory T) inferInstance
    (sentenceCarrier T (S).sentenceInclusion) (S).algebra.a.2 :=
  representedArrow T
    (GraphMorphism.inclusion (chosenGraph T (S).sentenceInclusion).imageInclusionProof)

/-- The triangle involves the actual chosen inclusion into formulas. -/
theorem toSentence_over : toSentence T V σ π d ≫ (S).sentenceInclusion =
    toImage T V σ π d ≫ imageInclusion T V σ π d := by
  have hi : (sentenceChart T (S).sentenceInclusion).inv ≫ (S).sentenceInclusion =
      imageInclusion T V σ π d := by
    apply (cancel_epi (sentenceChart T (S).sentenceInclusion).hom).mp
    rw [← Category.assoc,Iso.hom_inv_id,Category.id_comp]
    exact (sentenceChart_over T (S).sentenceInclusion).symm
  change (toImage T V σ π d ≫ (sentenceChart T (S).sentenceInclusion).inv) ≫
    (S).sentenceInclusion = _
  rw [Category.assoc,hi]

section Models
variable (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T]

/-- Reading the formula coordinate after the actual chart keeps the
literal input word in every T-model, including nonstandard ones. -/
theorem toSentence_value (word : Obj T M (literalSentenceCarrier T V σ π d)) :
    ((F T M).map (S).sentenceInclusion
      ((F T M).map (toSentence T V σ π d) word)).val = word.val := by
  have h := congrArg (fun f => ((F T M).map f word).val) (toSentence_over T V σ π d)
  have hleft := congrArg Subtype.val
    ((F T M).map_comp_apply (toSentence T V σ π d) (S).sentenceInclusion word)
  have hright := congrArg Subtype.val
    ((F T M).map_comp_apply (toImage T V σ π d) (imageInclusion T V σ π d) word)
  exact hleft.symm.trans (h.trans (hright.trans
    ((PredicateInterpretation.map_inclusion_val T M
      (chosenGraph T (S).sentenceInclusion).imageInclusionProof _).trans
        (PredicateInterpretation.map_inclusion_val T M (toImageProof T V σ π d) word))))

end Models
end CategoricalEssentialIncompleteness.V46.SyntacticSentenceLiteralChart
