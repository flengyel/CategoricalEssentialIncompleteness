/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ConcreteNamedComparisonPayloadOccurrences

/-! # Scalar original and FV projection identities follow from stable initiality -/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticLists
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax

namespace CategoricalEssentialIncompleteness.V46.ConcreteNamedComparison
variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
variable (U V : PredicateCategory T) (σ π : ℕ → PredicateCategory T) (d : ℕ)

/-- The already identified intrinsic occurrence morphism, chosen by
sort; both codomains are the same actual list object. -/
def intrinsicOccurrences : (formula : Bool) →
    @Quiver.Hom (PredicateCategory T) inferInstance
      (syntaxCarrier V σ π d formula) (listObject T V)
  | false => (categoricalSyntax T V σ π d).termOccurrences
  | true => (categoricalSyntax T V σ π d).formulaOccurrences

theorem occurrenceProjectionFamily_eq (formula : Bool) :
    payloadProjectionFamily T U V σ π d .occurrences formula =
      (constantFamilyFunctor (projectionParameters T U V σ π d)).map
        (intrinsicOccurrences T V σ π d formula) := by
  cases formula
  · change payloadProjectionFamily T U V σ π d .occurrences false =
      (constantFamilyFunctor (projectionParameters T U V σ π d)).map
        (categoricalSyntax T V σ π d).termOccurrences
    rw [termOccurrences_eq T V σ π d]
    exact congrArg Prod.fst (payloadOccurrenceProjectionPair_eq T U V σ π d)
  · change payloadProjectionFamily T U V σ π d .occurrences true =
      (constantFamilyFunctor (projectionParameters T U V σ π d)).map
        (categoricalSyntax T V σ π d).formulaOccurrences
    rw [formulaOccurrences_eq T V σ π d]
    exact congrArg Prod.snd (payloadOccurrenceProjectionPair_eq T U V σ π d)

section Models
variable (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

theorem intrinsicOccurrences_value (formula : Bool)
    (word : Obj T M (syntaxCarrier V σ π d formula)) :
    ((F T M).map (intrinsicOccurrences T V σ π d formula) word).val =
      ConcreteNamedSubstitution.freeVariables V σ π d word.val := by
  cases formula
  · exact termOccurrences_value T V σ π d M word
  · exact formulaOccurrences_value T V σ π d M word

theorem originalComputation_at_point (formula : Bool)
    (q : Obj T M ((projectionParameters T U V σ π d) ⨯ (syntaxCarrier V σ π d formula : PredicateCategory T))) :
    originalComputation V σ π d
      ((F T M).map (prod.fst : U ⨯ (syntaxCarrier V σ π d false : PredicateCategory T) ⟶ U)
        ((F T M).map prod.fst q)).val
      ((F T M).map (prod.snd : U ⨯ (syntaxCarrier V σ π d false : PredicateCategory T) ⟶ _)
        ((F T M).map prod.fst q)).val
      ((F T M).map prod.snd q).val = ((F T M).map prod.snd q).val := by
  have hv := payloadProjectionFamily_value T U V σ π d M .original formula ((F T M).map prod.fst q) q rfl
  have he := congrArg (fun f => (F T M).map f.left q)
    (originalProjectionFamily_eq_id T U V σ π d formula)
  have hpoint : (F T M).map (payloadProjectionFamily T U V σ π d .original formula).left q = q := by
    change (F T M).map (payloadProjectionFamily T U V σ π d .original formula).left q =
      (F T M).map (𝟙 ((projectionParameters T U V σ π d) ⨯
        (syntaxCarrier V σ π d formula : PredicateCategory T))) q at he
    simpa only [Functor.map_id_apply] using he
  have hs := congrArg (fun z => ((F T M).map prod.snd z).val) hpoint
  exact hv.symm.trans hs

theorem occurrenceComputation_at_point (formula : Bool)
    (q : Obj T M ((projectionParameters T U V σ π d) ⨯ (syntaxCarrier V σ π d formula : PredicateCategory T))) :
    occurrenceComputation V σ π d
      ((F T M).map (prod.fst : U ⨯ (syntaxCarrier V σ π d false : PredicateCategory T) ⟶ U)
        ((F T M).map prod.fst q)).val
      ((F T M).map (prod.snd : U ⨯ (syntaxCarrier V σ π d false : PredicateCategory T) ⟶ _)
        ((F T M).map prod.fst q)).val
      ((F T M).map prod.snd q).val =
        ConcreteNamedSubstitution.freeVariables V σ π d ((F T M).map prod.snd q).val := by
  have hv := payloadProjectionFamily_value T U V σ π d M .occurrences formula ((F T M).map prod.fst q) q rfl
  have he := congrArg (fun f => (F T M).map f.left q) (occurrenceProjectionFamily_eq T U V σ π d formula)
  have hpoint := congrArg (fun z => ((F T M).map prod.snd z).val) he
  have hmap := model_map_snd T M (𝟙 (projectionParameters T U V σ π d))
    (intrinsicOccurrences T V σ π d formula) q
  exact hv.symm.trans (hpoint.trans ((congrArg Subtype.val hmap).trans
    (intrinsicOccurrences_value T V σ π d M formula ((F T M).map prod.snd q))))

/-- These are equations on arbitrary model values satisfying the typed
source, with no variable-membership premise beyond the selected U. -/
theorem originalComputation_identity (formula : Bool) (x replacement word : M)
    (hx : U.val.Evalb ![x]) (ht : (syntaxCarrier V σ π d false).val.Evalb ![replacement])
    (hw : (syntaxCarrier V σ π d formula).val.Evalb ![word]) :
    originalComputation V σ π d x replacement word = word := by
  let xx : Obj T M U := ⟨x,hx⟩
  let tt : Obj T M (syntaxCarrier V σ π d false) := ⟨replacement,ht⟩
  let ww : Obj T M (syntaxCarrier V σ π d formula) := ⟨word,hw⟩
  obtain ⟨p,hpx,hpt⟩ := modelProduct_exists T M U (syntaxCarrier V σ π d false) xx tt
  obtain ⟨q,hqp,hqw⟩ := modelProduct_exists T M (projectionParameters T U V σ π d)
    (syntaxCarrier V σ π d formula) p ww
  have h := originalComputation_at_point T U V σ π d M formula q
  erw [hqp,hpx,hpt,hqw] at h
  exact h

theorem occurrenceComputation_identity (formula : Bool) (x replacement word : M)
    (hx : U.val.Evalb ![x]) (ht : (syntaxCarrier V σ π d false).val.Evalb ![replacement])
    (hw : (syntaxCarrier V σ π d formula).val.Evalb ![word]) :
    occurrenceComputation V σ π d x replacement word =
      ConcreteNamedSubstitution.freeVariables V σ π d word := by
  let xx : Obj T M U := ⟨x,hx⟩
  let tt : Obj T M (syntaxCarrier V σ π d false) := ⟨replacement,ht⟩
  let ww : Obj T M (syntaxCarrier V σ π d formula) := ⟨word,hw⟩
  obtain ⟨p,hpx,hpt⟩ := modelProduct_exists T M U (syntaxCarrier V σ π d false) xx tt
  obtain ⟨q,hqp,hqw⟩ := modelProduct_exists T M (projectionParameters T U V σ π d)
    (syntaxCarrier V σ π d formula) p ww
  have h := occurrenceComputation_at_point T U V σ π d M formula q
  erw [hqp,hpx,hpt,hqw] at h
  exact h

end Models
end CategoricalEssentialIncompleteness.V46.ConcreteNamedComparison
