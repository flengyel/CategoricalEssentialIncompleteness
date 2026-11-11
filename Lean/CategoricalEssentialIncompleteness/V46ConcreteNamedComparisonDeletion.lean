/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ConcreteNamedComparisonBooleans
public import CategoricalEssentialIncompleteness.V46ConcreteNamedComparisonLists
public import CategoricalEssentialIncompleteness.V46ConcreteNamedComparisonCoordinates

/-! # Numerical name deletion is the specified categorical list fold -/

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

def deletionGraph (V : Carrier) : Graph :=
  let L := SyntacticLists.listCarrier V
  let D := ConcreteNamedSubstitution.deleteValueGraph
  .mkSigma “input out. ∃ x list, !pairDef.val input x list ∧ !V.val x ∧
    !L.val list ∧ !D.val out x list”

section ArithmeticModels
variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

@[simp] theorem deleteValueGraph_eval (out x list : M) :
    ConcreteNamedSubstitution.deleteValueGraph.val.Evalb ![out,x,list] ↔
      out = ConcreteNamedSubstitution.delete x list := by
  simp [ConcreteNamedSubstitution.deleteValueGraph]

@[simp] theorem deletionGraph_eval (V : Carrier) (input out : M) :
    (deletionGraph V).val.Evalb ![input,out] ↔
      ∃ x list : M, input = Arithmetic.pair x list ∧ V.val.Evalb ![x] ∧
        (SyntacticLists.listCarrier V).val.Evalb ![list] ∧
        out = ConcreteNamedSubstitution.delete x list := by
  simp [deletionGraph]

end ArithmeticModels

variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] (V : PredicateCategory T)

def deletionMorphism : GraphMorphism T (productCarrier V (listObject T V)) (listObject T V) where
  graph := deletionGraph V
  support := by
    apply complete.{0} T
    intro M _ _
    let : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 := models_of_subtheory (U := T) inferInstance
    rw [models_iff,SyntacticPredicates.supportSentence_eval]
    intro input out h
    obtain ⟨x,list,hi,hx,hl,rfl⟩ := (deletionGraph_eval V input out).mp h
    exact ⟨(productCarrier_eval _ _ input).mpr ⟨x,list,hi,hx,hl⟩,
      ConcreteNamedSubstitution.delete_carrier V x list hl⟩
  total := by
    apply complete.{0} T
    intro M _ _
    let : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 := models_of_subtheory (U := T) inferInstance
    rw [models_iff,totalSentence_eval]
    intro input hi
    obtain ⟨x,list,rfl,hx,hl⟩ := (productCarrier_eval _ _ input).mp hi
    refine ⟨ConcreteNamedSubstitution.delete x list,
      (deletionGraph_eval V _ _).mpr ⟨x,list,rfl,hx,hl,rfl⟩,?_⟩
    intro out hout
    obtain ⟨x',list',he,_,_,ho⟩ := (deletionGraph_eval V _ out).mp hout
    obtain ⟨rfl,rfl⟩ := (pair_eq_pair_iff _ _ _ _).mp he
    exact ho

def deletionArrow : V ⨯ listObject T V ⟶ listObject T V :=
  toRawProduct T V (listObject T V) ≫ representedArrow T (deletionMorphism T V)

section Models
variable (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
local instance namedDeletionModelDecidableEq : DecidableEq M := Classical.decEq M

omit [𝗣𝗔 ⪯ T] [M↓[ℒₒᵣ] ⊧* T] in
private theorem deletion_adjoin_numeric (x y a : M) :
    ConcreteNamedSubstitution.delete x (adjoin y a) =
      (if x = y then ConcreteNamedSubstitution.delete x a else adjoin y (ConcreteNamedSubstitution.delete x a)) := by
  simpa only [eq_comm] using ConcreteNamedSubstitution.delete_adjoin x y a

theorem deletionArrow_value (q : Obj T M (V ⨯ listObject T V)) :
    ((F T M).map (deletionArrow T V) q).val = ConcreteNamedSubstitution.delete
      ((F T M).map (prod.fst : V ⨯ listObject T V ⟶ V) q).val
      ((F T M).map (prod.snd : V ⨯ listObject T V ⟶ listObject T V) q).val := by
  let r := (F T M).map (toRawProduct T V (listObject T V)) q
  let out := (F T M).map (representedArrow T (deletionMorphism T V)) r
  have h := (PredicateInterpretation.map_class_eq_iff T M (deletionMorphism T V) r out).mp rfl
  obtain ⟨x,list,he,_,_,ho⟩ := (deletionGraph_eval V r.val out.val).mp h
  have hr := toRawProduct_value T M V (listObject T V) q
  change r.val = _ at hr
  obtain ⟨h₀,h₁⟩ := (pair_eq_pair_iff _ _ _ _).mp (he.symm.trans hr)
  change ((F T M).map (toRawProduct T V (listObject T V) ≫
    representedArrow T (deletionMorphism T V)) q).val = _
  rw [Functor.map_comp_apply]
  exact ho.trans (congrArg₂ ConcreteNamedSubstitution.delete h₀ h₁)

theorem deletionStep_value (q : Obj T M (V ⨯ (V ⨯ listObject T V))) :
    ((F T M).map ((lists T V).deletionStep
      (SyntacticDecidableVariables.decidableVariables T V)) q).val =
        if ((F T M).map (prod.fst : V ⨯ (V ⨯ listObject T V) ⟶ V) q).val =
          ((F T M).map (prod.fst : V ⨯ listObject T V ⟶ V)
            ((F T M).map (prod.snd : V ⨯ (V ⨯ listObject T V) ⟶ V ⨯ listObject T V) q)).val
        then ((F T M).map (prod.snd : V ⨯ listObject T V ⟶ listObject T V)
          ((F T M).map (prod.snd : V ⨯ (V ⨯ listObject T V) ⟶ V ⨯ listObject T V) q)).val
        else adjoin
          ((F T M).map (prod.fst : V ⨯ listObject T V ⟶ V)
            ((F T M).map (prod.snd : V ⨯ (V ⨯ listObject T V) ⟶ V ⨯ listObject T V) q)).val
          ((F T M).map (prod.snd : V ⨯ listObject T V ⟶ listObject T V)
            ((F T M).map (prod.snd : V ⨯ (V ⨯ listObject T V) ⟶ V ⨯ listObject T V) q)).val := by
  let names : V ⨯ (V ⨯ listObject T V) ⟶ V ⨯ V :=
    prod.lift prod.fst (prod.snd ≫ prod.fst)
  let χ := names ≫ SyntacticDecidableVariables.test T V
  by_cases he : ((F T M).map (prod.fst : V ⨯ (V ⨯ listObject T V) ⟶ V) q).val =
      ((F T M).map (prod.fst : V ⨯ listObject T V ⟶ V)
        ((F T M).map (prod.snd : V ⨯ (V ⨯ listObject T V) ⟶ V ⨯ listObject T V) q)).val
  · have ht : (F T M).map χ q =
        (F T M).map (Two.constant (V ⨯ (V ⨯ listObject T V)) true) q := by
      apply equalityTest_comp_point T M V names q true
      erw [model_lift_fst T M,model_lift_snd T M]
      simp only [Functor.map_comp_apply]
      simpa only [iff_true] using he
    have hb := model_branch T M χ (prod.snd ≫ (lists T V).algebra.cons)
      (prod.snd ≫ prod.snd) q true ht
    simp only [↓reduceIte] at hb
    change ((F T M).map (Two.branch χ _ _) q).val = _
    erw [hb,ite_eq_left he]
    erw [Functor.map_comp_apply]
    rfl
  · have ht : (F T M).map χ q =
        (F T M).map (Two.constant (V ⨯ (V ⨯ listObject T V)) false) q := by
      apply equalityTest_comp_point T M V names q false
      erw [model_lift_fst T M,model_lift_snd T M]
      simp only [Functor.map_comp_apply]
      simpa using he
    have hb := model_branch T M χ (prod.snd ≫ (lists T V).algebra.cons)
      (prod.snd ≫ prod.snd) q false ht
    simp only at hb
    change ((F T M).map (Two.branch χ _ _) q).val = _
    erw [hb,ite_eq_right he]
    erw [Functor.map_comp_apply]
    erw [cons_value T M V]

end Models

theorem deletionArrow_nil : (lists T V).parameterNil V ≫ deletionArrow T V =
    terminal.from V ≫ (lists T V).algebra.nil := by
  apply PredicateInterpretation.jointly_faithful T
  intro M _ _
  let : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 := models_of_subtheory (U := T) inferInstance
  apply ConcreteCategory.hom_ext
  intro q
  apply Subtype.ext
  have hn : ((F T M).map (lists T V).algebra.nil ((F T M).map (terminal.from V) q)).val = 0 :=
    nil_value T M _ V _
  rw [Functor.map_comp_apply,Functor.map_comp_apply]
  refine Eq.trans ?_ hn.symm
  erw [deletionArrow_value T V M,model_lift_fst T M,model_lift_snd T M]
  rw [Functor.map_id_apply,Functor.map_comp_apply]
  erw [nil_value T M _ V]
  exact ConcreteNamedSubstitution.delete_nil _

theorem deletionArrow_cons : (lists T V).parameterCons V ≫ deletionArrow T V =
    (lists T V).parameterRec (deletionArrow T V) ≫
      (lists T V).deletionStep (SyntacticDecidableVariables.decidableVariables T V) := by
  classical
  apply PredicateInterpretation.jointly_faithful T
  intro M _ _
  let : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 := models_of_subtheory (U := T) inferInstance
  let : DecidableEq M := namedDeletionModelDecidableEq M
  apply ConcreteCategory.hom_ext
  intro q
  apply Subtype.ext
  let x := ((F T M).map (prod.fst : V ⨯ (V ⨯ listObject T V) ⟶ V) q).val
  let y := ((F T M).map (prod.fst : V ⨯ listObject T V ⟶ V)
    ((F T M).map (prod.snd : V ⨯ (V ⨯ listObject T V) ⟶ V ⨯ listObject T V) q)).val
  let a := ((F T M).map (prod.snd : V ⨯ listObject T V ⟶ listObject T V)
    ((F T M).map (prod.snd : V ⨯ (V ⨯ listObject T V) ⟶ V ⨯ listObject T V) q)).val
  let left := (F T M).map ((lists T V).parameterCons V) q
  let right := (F T M).map (recursionLift T (deletionArrow T V)) q
  let tail := (F T M).map (prod.lift prod.fst
    (prod.snd ≫ prod.snd) : V ⨯ (V ⨯ listObject T V) ⟶ V ⨯ listObject T V) q
  have hx : ((F T M).map (prod.fst : V ⨯ listObject T V ⟶ V) left).val = x := by
    have h := model_map_fst T M (𝟙 V) (lists T V).algebra.cons q
    exact (congrArg Subtype.val h).trans (by rw [Functor.map_id_apply]; rfl)
  have ha : ((F T M).map (prod.snd : V ⨯ listObject T V ⟶ listObject T V) left).val = adjoin y a :=
    (congrArg Subtype.val (model_map_snd T M (𝟙 V) (lists T V).algebra.cons q)).trans
      (cons_value T M V ((F T M).map (prod.snd : _ ⨯ (V ⨯ listObject T V) ⟶ _) q))
  have hleft := (deletionArrow_value T V M left).trans (congrArg₂ ConcreteNamedSubstitution.delete hx ha)
  have htx : ((F T M).map (prod.fst : V ⨯ listObject T V ⟶ V) tail).val = x :=
    congrArg Subtype.val (model_lift_fst T M prod.fst (prod.snd ≫ prod.snd) q)
  have hta : ((F T M).map (prod.snd : V ⨯ listObject T V ⟶ listObject T V) tail).val = a := by
    have h := model_lift_snd T M prod.fst (prod.snd ≫ prod.snd) q
    exact (congrArg Subtype.val h).trans (by rw [Functor.map_comp_apply]; rfl)
  have htail := (deletionArrow_value T V M tail).trans
    (congrArg₂ ConcreteNamedSubstitution.delete htx hta)
  have hrx : ((F T M).map (prod.fst : V ⨯ (V ⨯ listObject T V) ⟶ V) right).val = x :=
    congrArg Subtype.val (recursionLift_parameter T M (deletionArrow T V) q)
  have hry : ((F T M).map (prod.fst : V ⨯ listObject T V ⟶ V)
      ((F T M).map (prod.snd : V ⨯ (V ⨯ listObject T V) ⟶ V ⨯ listObject T V) right)).val = y :=
    congrArg Subtype.val (recursionLift_head T M (deletionArrow T V) q)
  have hra : ((F T M).map (prod.snd : V ⨯ listObject T V ⟶ listObject T V)
      ((F T M).map (prod.snd : V ⨯ (V ⨯ listObject T V) ⟶ V ⨯ listObject T V) right)).val =
        ConcreteNamedSubstitution.delete x a :=
    (congrArg Subtype.val (recursionLift_result T M (deletionArrow T V) q)).trans htail
  have hnumeric := deletion_adjoin_numeric M x y a
  have hright := deletionStep_value T V M right
  have hc := congrArg₂ (fun u v : M => fun w : M => if u = v then w else adjoin v w) hrx hry
  have hc' := (congrFun hc _).trans
    (congrArg (fun w : M => if x = y then w else adjoin y w) hra)
  rw [Functor.map_comp_apply,Functor.map_comp_apply]
  exact hleft.trans (hnumeric.trans (hright.trans hc').symm)

theorem deletionArrow_eq : deletionArrow T V =
    (lists T V).deletion (SyntacticDecidableVariables.decidableVariables T V) := by
  rw [(lists T V).deletion_eq_parameterFold]
  exact (lists T V).parameterFold_unique (terminal.from V ≫ (lists T V).algebra.nil)
    ((lists T V).deletionStep (SyntacticDecidableVariables.decidableVariables T V))
    (deletionArrow T V) (deletionArrow_nil T V) (deletionArrow_cons T V)

end CategoricalEssentialIncompleteness.V46.ConcreteNamedComparison
