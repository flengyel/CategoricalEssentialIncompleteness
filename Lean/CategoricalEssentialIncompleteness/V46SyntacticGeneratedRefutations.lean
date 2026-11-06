/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46SyntacticGeneratedAxioms
import CategoricalEssentialIncompleteness.V46ConcreteNamedComparisonStateCoordinates
import CategoricalEssentialIncompleteness.V46ConcreteNamedComparisonParameterPoints

/-! # The actual generated refutation image in sentence-word coordinates -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticLists
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax
namespace CategoricalEssentialIncompleteness.V46.SyntacticGeneratedAxioms
open ConcreteNamedComparison
variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
variable (V : PredicateCategory T) (σ π : ℕ → PredicateCategory T) (d : ℕ)
local notation "S" => plainCategoricalSyntax T V σ π d

/-- Refutation keeps the original sentence as output; its proof
concludes the negation of that sentence in the actual pullback. -/
def refutationProofs (Γ : Carrier) : PredicateCategory T :=
  pullback (conclusion T V σ π d Γ) ((S).sentenceNegation ≫ (S).sentenceInclusion)

def refutationConclusion (Γ : Carrier) : @Quiver.Hom (PredicateCategory T) inferInstance
    (refutationProofs T V σ π d Γ) (S).algebra.a.2 :=
  pullback.snd (conclusion T V σ π d Γ) ((S).sentenceNegation ≫ (S).sentenceInclusion) ≫
    (S).sentenceInclusion

def refutationCarrier (Γ : Carrier) : Carrier :=
  imageCarrier (chosenGraph T (refutationConclusion T V σ π d Γ)).graph

/-- Both predicates refer to formula words, not the raw codes of the
chosen sentence pullback. The theorem program is the constructed one. -/
def literalRefutationCarrier (Γ : Carrier) : Carrier :=
  let Sent := literalSentenceCarrier T V σ π d
  let Neg := (chosenGraph T (S).negationConstructor).graph
  let Th := literalTheoremCarrier T V σ π d Γ
  .mkSigma “word. !Sent.val word ∧ ∃ negative, !Neg.val word negative ∧ !Th.val negative”

section Models
variable (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T]

/-- The literal refutation predicate uses the original sentence word and
an existential negative word linked by the actual negation graph. -/
@[simp] theorem literalRefutationCarrier_eval (Γ : Carrier) (word : M) :
    (literalRefutationCarrier T V σ π d Γ).val.Evalb ![word] ↔
      (literalSentenceCarrier T V σ π d).val.Evalb ![word] ∧
        ∃ negative : M, (chosenGraph T (S).negationConstructor).graph.val.Evalb ![word,negative] ∧
          (literalTheoremCarrier T V σ π d Γ).val.Evalb ![negative] := by
  simp [literalRefutationCarrier]

theorem sentence_points (word : M) :
    (literalSentenceCarrier T V σ π d).val.Evalb ![word] ↔
      ∃ s : Obj T M (S).sentenceObject, ((F T M).map (S).sentenceInclusion s).val = word := by
  let : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 := models_of_subtheory (U := T) inferInstance
  exact (sentenceCarrier_literal T V σ π d M word).symm.trans
    (imageCarrier_points T M (S).sentenceInclusion word)

/-- The actual sentence-negation square gives its literal formula
coordinate without identifying the chosen sentence object's code. -/
theorem sentenceNegation_point (s : Obj T M (S).sentenceObject) :
    (F T M).map ((S).sentenceNegation ≫ (S).sentenceInclusion) s =
      (F T M).map (S).negationConstructor ((F T M).map (S).sentenceInclusion s) := by
  have h := congrArg (fun f => (F T M).map f s) (S).sentenceNegation_inclusion
  exact h.trans ((F T M).map_comp_apply (S).sentenceInclusion (S).negationConstructor s)

/-- Generated refutability is the actual proof image after negation,
expressed by the literal positive sentence/theorem predicates. -/
theorem refutationCarrier_literal (Γ : Carrier) (word : M) :
    (refutationCarrier T V σ π d Γ).val.Evalb ![word] ↔
      (literalRefutationCarrier T V σ π d Γ).val.Evalb ![word] := by
  rw [literalRefutationCarrier_eval T V σ π d M]
  change (imageCarrier (chosenGraph T (refutationConclusion T V σ π d Γ)).graph).val.Evalb ![word] ↔ _
  rw [imageCarrier_points T M]
  constructor
  · rintro ⟨input,hi⟩
    let s := (F T M).map (pullback.snd (conclusion T V σ π d Γ)
      ((S).sentenceNegation ≫ (S).sentenceInclusion)) input
    let p := (F T M).map (pullback.fst (conclusion T V σ π d Γ)
      ((S).sentenceNegation ≫ (S).sentenceInclusion)) input
    let w := (F T M).map (S).sentenceInclusion s
    let n := (F T M).map (S).negationConstructor w
    have hw : w.val = word := by
      have he := (F T M).map_comp_apply
        (pullback.snd (conclusion T V σ π d Γ) ((S).sentenceNegation ≫ (S).sentenceInclusion))
        (S).sentenceInclusion input
      exact (congrArg Subtype.val he).symm.trans hi
    have hp : (F T M).map (conclusion T V σ π d Γ) p = n := by
      have he := parameterPoint_diagram T M
        (pullback.fst (conclusion T V σ π d Γ) ((S).sentenceNegation ≫ (S).sentenceInclusion))
        (conclusion T V σ π d Γ)
        (pullback.snd (conclusion T V σ π d Γ) ((S).sentenceNegation ≫ (S).sentenceInclusion))
        ((S).sentenceNegation ≫ (S).sentenceInclusion)
        (pullback.condition (f := conclusion T V σ π d Γ)
          (g := (S).sentenceNegation ≫ (S).sentenceInclusion)) input
      exact he.trans (sentenceNegation_point T V σ π d M s)
    have hns : (literalSentenceCarrier T V σ π d).val.Evalb ![n.val] := by
      apply (sentence_points T V σ π d M n.val).mpr
      refine ⟨(F T M).map (S).sentenceNegation s,?_⟩
      exact congrArg Subtype.val (((F T M).map_comp_apply (S).sentenceNegation (S).sentenceInclusion s).symm.trans
        (sentenceNegation_point T V σ π d M s))
    refine ⟨(sentence_points T V σ π d M word).mpr ⟨s,hw⟩,n.val,?_,?_⟩
    · have hn := (chosenGraph_value_iff T M (S).negationConstructor w n.val).mpr rfl
      simpa only [hw] using hn
    · apply (literalTheoremCarrier_model T V σ π d M Γ n.val).mpr
      exact (theoremCarrier_model T V σ π d M Γ n.val).mpr
        ⟨hns,p,congrArg Subtype.val hp⟩
  · rintro ⟨hs,negative,hn,hth⟩
    obtain ⟨s,hs⟩ := (sentence_points T V σ π d M word).mp hs
    let w := (F T M).map (S).sentenceInclusion s
    have hw : w.val = word := hs
    have hn' : ((F T M).map (S).negationConstructor w).val = negative := by
      apply (chosenGraph_value_iff T M (S).negationConstructor w negative).mp
      simpa only [hw] using hn
    obtain ⟨_,p,hp⟩ := (theoremCarrier_model T V σ π d M Γ negative).mp
      ((literalTheoremCarrier_model T V σ π d M Γ negative).mp hth)
    have hm : (F T M).map (conclusion T V σ π d Γ) p =
        (F T M).map ((S).sentenceNegation ≫ (S).sentenceInclusion) s := by
      apply Subtype.ext
      exact hp.trans ((congrArg Subtype.val (sentenceNegation_point T V σ π d M s)).trans hn').symm
    obtain ⟨input,_,hi⟩ := Types.exists_of_isPullback
      ((IsPullback.of_hasPullback (conclusion T V σ π d Γ)
        ((S).sentenceNegation ≫ (S).sentenceInclusion)).map (F T M)) p s hm
    refine ⟨input,?_⟩
    have he := (F T M).map_comp_apply
      (pullback.snd (conclusion T V σ π d Γ) ((S).sentenceNegation ≫ (S).sentenceInclusion))
      (S).sentenceInclusion input
    exact (congrArg Subtype.val he).trans
      ((congrArg (fun q => ((F T M).map (S).sentenceInclusion q).val) hi).trans hs)

end Models

def refutationLiteralSentence (Γ : Carrier) : ArithmeticSentence :=
  let A := refutationCarrier T V σ π d Γ
  let B := literalRefutationCarrier T V σ π d Γ
  “∀ word, !A.val word ↔ !B.val word”

theorem refutation_literal_theory (Γ : Carrier) : T ⊢ refutationLiteralSentence T V σ π d Γ := by
  apply complete.{0} T
  intro M _ _
  simpa [models_iff,refutationLiteralSentence] using
    (fun word : M => refutationCarrier_literal T V σ π d M Γ word)

end CategoricalEssentialIncompleteness.V46.SyntacticGeneratedAxioms
