/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ConcreteNamedComparisonModels
public import CategoricalEssentialIncompleteness.V46ConcreteNamedSubstitutionLists
public import CategoricalEssentialIncompleteness.V46SyntacticListsStable
public import CategoricalEssentialIncompleteness.V46CategoricalListLaws

/-! # The categorical concatenation computes numerical append -/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.Limits
open FailureOfComposition.ProofSearch FailureOfComposition.CodedObjectMembership
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticLists

namespace CategoricalEssentialIncompleteness.V46.ConcreteNamedComparison
/-- The parameter is the right-hand list; the recursively consumed
list is the second input coordinate. -/
def appendParameterGraph (V : Carrier) : Graph :=
  let L := SyntacticLists.listCarrier V
  let A := SyntacticSyntax.Words.appendDef
  .mkSigma “input out. ∃ right left, !pairDef.val input right left ∧
    !L.val right ∧ !L.val left ∧ !A.val out left right”

section ArithmeticModels
variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

@[simp] theorem appendParameterGraph_eval (V : Carrier) (input out : M) :
    (appendParameterGraph V).val.Evalb ![input,out] ↔
      ∃ right left : M, input = Arithmetic.pair right left ∧
        (SyntacticLists.listCarrier V).val.Evalb ![right] ∧
        (SyntacticLists.listCarrier V).val.Evalb ![left] ∧
        out = SyntacticSyntax.Words.append left right := by
  simp [appendParameterGraph]

end ArithmeticModels

variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
variable (V : PredicateCategory T)
abbrev lists := SyntacticLists.stableListAlgebra T V

def appendParameterMorphism : GraphMorphism T
    (productCarrier (listObject T V) (listObject T V)) (listObject T V) where
  graph := appendParameterGraph V
  support := by
    apply complete.{0} T
    intro M _ _
    let : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 := models_of_subtheory (U := T) inferInstance
    rw [models_iff, SyntacticPredicates.supportSentence_eval]
    intro input out h
    obtain ⟨right,left,hi,hr,hl,rfl⟩ := (appendParameterGraph_eval V input out).mp h
    exact ⟨(productCarrier_eval _ _ input).mpr ⟨right,left,hi,hr,hl⟩,
      ConcreteNamedSubstitution.append_carrier V left right hl hr⟩
  total := by
    apply complete.{0} T
    intro M _ _
    let : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 := models_of_subtheory (U := T) inferInstance
    rw [models_iff, totalSentence_eval]
    intro input hi
    obtain ⟨right,left,rfl,hr,hl⟩ := (productCarrier_eval _ _ input).mp hi
    refine ⟨SyntacticSyntax.Words.append left right,
      (appendParameterGraph_eval V _ _).mpr ⟨right,left,rfl,hr,hl,rfl⟩, ?_⟩
    intro out hout
    obtain ⟨right',left',he,_,_,ho⟩ := (appendParameterGraph_eval V _ out).mp hout
    obtain ⟨rfl,rfl⟩ := (pair_eq_pair_iff _ _ _ _).mp he
    exact ho

def appendParameterArrow : listObject T V ⨯ listObject T V ⟶ listObject T V :=
  toRawProduct T (listObject T V) (listObject T V) ≫
    representedArrow T (appendParameterMorphism T V)

theorem appendParameterArrow_value (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T]
    [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] (q : Obj T M (listObject T V ⨯ listObject T V)) :
    ((F T M).map (appendParameterArrow T V) q).val =
      SyntacticSyntax.Words.append
        ((F T M).map (prod.snd : listObject T V ⨯ listObject T V ⟶ listObject T V) q).val
        ((F T M).map (prod.fst : listObject T V ⨯ listObject T V ⟶ listObject T V) q).val := by
  let r := (F T M).map (toRawProduct T (listObject T V) (listObject T V)) q
  let out := (F T M).map (representedArrow T (appendParameterMorphism T V)) r
  have h := (PredicateInterpretation.map_class_eq_iff T M (appendParameterMorphism T V) r out).mp rfl
  obtain ⟨right,left,he,_,_,ho⟩ := (appendParameterGraph_eval V r.val out.val).mp h
  have hr := toRawProduct_value T M (listObject T V) (listObject T V) q
  change r.val = _ at hr
  obtain ⟨h₀,h₁⟩ := (pair_eq_pair_iff _ _ _ _).mp (he.symm.trans hr)
  change ((F T M).map (toRawProduct T (listObject T V) (listObject T V) ≫
    representedArrow T (appendParameterMorphism T V)) q).val = _
  rw [Functor.map_comp_apply]
  exact ho.trans (congrArg₂ SyntacticSyntax.Words.append h₁ h₀)

theorem appendParameter_nil :
    (lists T V).parameterNil (listObject T V) ≫ appendParameterArrow T V = 𝟙 _ := by
  apply PredicateInterpretation.jointly_faithful T
  intro M _ _
  let : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 := models_of_subtheory (U := T) inferInstance
  apply ConcreteCategory.hom_ext
  intro q
  apply Subtype.ext
  rw [Functor.map_comp_apply, Functor.map_id_apply]
  erw [appendParameterArrow_value T V M]
  erw [model_lift_snd T M,model_lift_fst T M]
  rw [Functor.map_comp_apply]
  erw [nil_value T M _ V]
  simp only [Functor.map_id_apply,SyntacticSyntax.Words.append_nil]

theorem appendParameter_cons :
    (lists T V).parameterCons (listObject T V) ≫ appendParameterArrow T V =
      (lists T V).parameterRec (appendParameterArrow T V) ≫
        prod.snd ≫ (lists T V).algebra.cons := by
  apply PredicateInterpretation.jointly_faithful T
  intro M _ _
  let : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 := models_of_subtheory (U := T) inferInstance
  apply ConcreteCategory.hom_ext
  intro q
  apply Subtype.ext
  simp only [StableListAlgebra.parameterCons,StableListAlgebra.parameterRec,Functor.map_comp_apply]
  erw [appendParameterArrow_value T V M,cons_value T M V]
  erw [model_map_snd T M,model_map_fst T M]
  rw [Functor.map_id_apply]
  erw [cons_value T M V]
  erw [model_lift_snd T M,model_lift_snd T M]
  erw [model_lift_fst T M]
  simp only [Functor.map_comp_apply]
  erw [appendParameterArrow_value T V M,model_lift_snd T M,model_lift_fst T M]
  simp only [Functor.map_comp_apply,SyntacticSyntax.Words.append_adjoin]
  rfl

/-- Stable initiality identifies the numerical recursion with the specified categorical
concatenation fold. -/
theorem appendParameter_eq :
    appendParameterArrow T V = (lists T V).appendParameterValue := by
  rw [(lists T V).appendParameterValue_eq_parameterFold]
  exact (lists T V).parameterFold_unique (𝟙 _)
    (prod.snd ≫ (lists T V).algebra.cons) (appendParameterArrow T V)
    (appendParameter_nil T V) (appendParameter_cons T V)

theorem append_value (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T]
    [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] (q : Obj T M (listObject T V ⨯ listObject T V)) :
    ((F T M).map (lists T V).append q).val =
      SyntacticSyntax.Words.append
        ((F T M).map (prod.fst : listObject T V ⨯ listObject T V ⟶ listObject T V) q).val
        ((F T M).map (prod.snd : listObject T V ⨯ listObject T V ⟶ listObject T V) q).val := by
  change ((F T M).map (prod.lift prod.snd prod.fst ≫ (lists T V).appendParameterValue) q).val = _
  rw [← appendParameter_eq,Functor.map_comp_apply]
  erw [appendParameterArrow_value T V M,model_lift_snd T M,model_lift_fst T M]
  rfl

end CategoricalEssentialIncompleteness.V46.ConcreteNamedComparison
