/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46ConcreteNamedComparisonModels
import CategoricalEssentialIncompleteness.V46ConcreteNamedSubstitutionLists
import CategoricalEssentialIncompleteness.V46SyntacticDecidableVariables

/-! # Numerical list-membership values and the actual Boolean object -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.Limits
open FailureOfComposition.ProofSearch FailureOfComposition.CodedObjectMembership
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticLists

namespace CategoricalEssentialIncompleteness.V46.ConcreteNamedComparison

def membershipGraph (V : Carrier) : Graph :=
  let L := SyntacticLists.listCarrier V
  let B := ConcreteNamedSubstitution.memberValueGraph
  .mkSigma “input out. ∃ x list answer, !pairDef.val input x list ∧ !V.val x ∧
    !L.val list ∧ !B.val answer x list ∧ !pairDef.val out 0 answer”

section ArithmeticModels
variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

@[simp] theorem memberValueGraph_eval (out x list : M) :
    ConcreteNamedSubstitution.memberValueGraph.val.Evalb ![out,x,list] ↔
      out = ConcreteNamedSubstitution.member x list := by
  simp [ConcreteNamedSubstitution.memberValueGraph]

@[simp] theorem membershipGraph_eval (V : Carrier) (input out : M) :
    (membershipGraph V).val.Evalb ![input,out] ↔
      ∃ x list : M, input = Arithmetic.pair x list ∧ V.val.Evalb ![x] ∧
        (SyntacticLists.listCarrier V).val.Evalb ![list] ∧
        out = Arithmetic.pair 0 (ConcreteNamedSubstitution.member x list) := by
  simp [membershipGraph]

end ArithmeticModels

variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]

def rawBooleanConstant (X : PredicateCategory T) (b : Bool) :
    X ⟶ SyntacticDecidableVariables.RawBool T :=
  representedArrow T (terminalMap T X) ≫
    (if b then representedArrow T (PredicateInterpretation.sumInr T terminalCarrier terminalCarrier)
      else representedArrow T (PredicateInterpretation.sumInl T terminalCarrier terminalCarrier))

@[reassoc] theorem sumInl_booleanIso :
    representedArrow T (PredicateInterpretation.sumInl T terminalCarrier terminalCarrier) ≫
      (SyntacticDecidableVariables.booleanIso T).hom =
        (SyntacticDecidableVariables.terminalIso T).hom ≫ coprod.inl := by
  change representedArrow T (PredicateInterpretation.sumInl T terminalCarrier terminalCarrier) ≫
    ((PredicateInterpretation.sumIsColimit T terminalCarrier terminalCarrier).coconePointUniqueUpToIso
      (coprodIsCoprod (C := PredicateCategory T) terminalCarrier terminalCarrier)).hom ≫
      coprod.map (SyntacticDecidableVariables.terminalIso T).hom
        (SyntacticDecidableVariables.terminalIso T).hom = _
  have h := IsColimit.comp_coconePointUniqueUpToIso_hom
    (PredicateInterpretation.sumIsColimit T terminalCarrier terminalCarrier)
    (coprodIsCoprod (C := PredicateCategory T) terminalCarrier terminalCarrier) ⟨WalkingPair.left⟩
  erw [← Category.assoc,h,coprod.inl_map]

@[reassoc] theorem rawBooleanConstant_iso (X : PredicateCategory T) (b : Bool) :
    rawBooleanConstant T X b ≫ (SyntacticDecidableVariables.booleanIso T).hom =
      Two.constant X b := by
  cases b
  · change (representedArrow T (terminalMap T X) ≫
      representedArrow T (PredicateInterpretation.sumInl T terminalCarrier terminalCarrier)) ≫
        (SyntacticDecidableVariables.booleanIso T).hom = terminal.from X ≫ coprod.inl
    rw [Category.assoc,sumInl_booleanIso,← Category.assoc]
    congr 1
    exact (terminalIsTerminal (C := PredicateCategory T)).hom_ext _ _
  · change SyntacticDecidableVariables.rawTrue T X ≫
      (SyntacticDecidableVariables.booleanIso T).hom = terminal.from X ≫ coprod.inr
    exact SyntacticDecidableVariables.rawTrue_booleanIso T X

def membershipMorphism (V : PredicateCategory T) :
    GraphMorphism T (productCarrier V (listObject T V)) (SyntacticDecidableVariables.RawBool T) where
  graph := membershipGraph V
  support := by
    apply complete.{0} T
    intro M _ _
    let : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 := models_of_subtheory (U := T) inferInstance
    rw [models_iff,SyntacticPredicates.supportSentence_eval]
    intro input out h
    obtain ⟨x,list,hi,hx,hl,rfl⟩ := (membershipGraph_eval V input out).mp h
    refine ⟨(productCarrier_eval _ _ input).mpr ⟨x,list,hi,hx,hl⟩,?_⟩
    rcases ConcreteNamedSubstitution.member_boolean x list with hm | hm
    · rw [hm]
      exact (PredicateInterpretation.sumCarrier_eval M terminalCarrier terminalCarrier _).mpr
        (Or.inl ⟨0,rfl,(terminalCarrier_eval _).mpr rfl⟩)
    · rw [hm]
      exact (PredicateInterpretation.sumCarrier_eval M terminalCarrier terminalCarrier _).mpr
        (Or.inr ⟨0,rfl,(terminalCarrier_eval _).mpr rfl⟩)
  total := by
    apply complete.{0} T
    intro M _ _
    let : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 := models_of_subtheory (U := T) inferInstance
    rw [models_iff,totalSentence_eval]
    intro input hi
    obtain ⟨x,list,rfl,hx,hl⟩ := (productCarrier_eval _ _ input).mp hi
    refine ⟨Arithmetic.pair 0 (ConcreteNamedSubstitution.member x list),
      (membershipGraph_eval V _ _).mpr ⟨x,list,rfl,hx,hl,rfl⟩,?_⟩
    intro out hout
    obtain ⟨x',list',he,_,_,ho⟩ := (membershipGraph_eval V _ out).mp hout
    obtain ⟨rfl,rfl⟩ := (pair_eq_pair_iff _ _ _ _).mp he
    exact ho

def rawMembership (V : PredicateCategory T) :
    V ⨯ listObject T V ⟶ SyntacticDecidableVariables.RawBool T :=
  toRawProduct T V (listObject T V) ≫ representedArrow T (membershipMorphism T V)

def membershipArrow (V : PredicateCategory T) : V ⨯ listObject T V ⟶ Two (PredicateCategory T) :=
  rawMembership T V ≫ (SyntacticDecidableVariables.booleanIso T).hom

section Models
variable (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
local instance namedBooleanModelDecidableEq : DecidableEq M := Classical.decEq M

omit [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] in
theorem model_constant_comp {X Y : PredicateCategory T} (f : X ⟶ Y) (q : Obj T M X) (b : Bool) :
    (F T M).map (Two.constant Y b) ((F T M).map f q) =
      (F T M).map (Two.constant X b) q := by
  rw [← Functor.map_comp_apply,Two.comp_constant]

theorem rawBooleanConstant_value (X : PredicateCategory T) (b : Bool) (q : Obj T M X) :
    ((F T M).map (rawBooleanConstant T X b) q).val =
      Arithmetic.pair 0 (if b then 1 else 0) := by
  let z := (F T M).map (representedArrow T (terminalMap T X)) q
  have hz : z.val = 0 := (terminalCarrier_eval _).mp z.property
  cases b
  · change ((F T M).map (representedArrow T (terminalMap T X) ≫
      representedArrow T (PredicateInterpretation.sumInl T terminalCarrier terminalCarrier)) q).val = _
    rw [Functor.map_comp_apply,PredicateInterpretation.map_sumInl]
    change Arithmetic.pair z.val 0 = Arithmetic.pair 0 0
    rw [hz]
  · change ((F T M).map (representedArrow T (terminalMap T X) ≫
      representedArrow T (PredicateInterpretation.sumInr T terminalCarrier terminalCarrier)) q).val = _
    rw [Functor.map_comp_apply,PredicateInterpretation.map_sumInr]
    change Arithmetic.pair z.val 1 = Arithmetic.pair 0 1
    rw [hz]

theorem rawMembership_value (V : PredicateCategory T) (q : Obj T M (V ⨯ listObject T V)) :
    ((F T M).map (rawMembership T V) q).val = Arithmetic.pair 0
      (ConcreteNamedSubstitution.member
        ((F T M).map (prod.fst : V ⨯ listObject T V ⟶ V) q).val
        ((F T M).map (prod.snd : V ⨯ listObject T V ⟶ listObject T V) q).val) := by
  let r := (F T M).map (toRawProduct T V (listObject T V)) q
  let out := (F T M).map (representedArrow T (membershipMorphism T V)) r
  have h := (PredicateInterpretation.map_class_eq_iff T M (membershipMorphism T V) r out).mp rfl
  obtain ⟨x,list,he,_,_,ho⟩ := (membershipGraph_eval V r.val out.val).mp h
  have hr := toRawProduct_value T M V (listObject T V) q
  change r.val = _ at hr
  obtain ⟨h₀,h₁⟩ := (pair_eq_pair_iff _ _ _ _).mp (he.symm.trans hr)
  change ((F T M).map (toRawProduct T V (listObject T V) ≫
    representedArrow T (membershipMorphism T V)) q).val = _
  rw [Functor.map_comp_apply]
  exact ho.trans (congrArg (Arithmetic.pair 0) (congrArg₂ ConcreteNamedSubstitution.member h₀ h₁))

theorem membershipArrow_point (V : PredicateCategory T) (q : Obj T M (V ⨯ listObject T V))
    (b : Bool) (hb : ConcreteNamedSubstitution.member
      ((F T M).map (prod.fst : V ⨯ listObject T V ⟶ V) q).val
      ((F T M).map (prod.snd : V ⨯ listObject T V ⟶ listObject T V) q).val =
        if b then 1 else 0) :
    (F T M).map (membershipArrow T V) q =
      (F T M).map (Two.constant (V ⨯ listObject T V) b) q := by
  have hr : (F T M).map (rawMembership T V) q =
      (F T M).map (rawBooleanConstant T (V ⨯ listObject T V) b) q := by
    apply Subtype.ext
    rw [rawMembership_value,rawBooleanConstant_value,hb]
  change (F T M).map (rawMembership T V ≫ (SyntacticDecidableVariables.booleanIso T).hom) q = _
  rw [Functor.map_comp_apply,hr,← Functor.map_comp_apply,rawBooleanConstant_iso]

theorem rawEquality_value (V : PredicateCategory T) (q : Obj T M (V ⨯ V)) :
    ((F T M).map (toRawProduct T V V ≫
      representedArrow T (SyntacticDecidableVariables.equalityMorphism T V)) q).val =
        Arithmetic.pair 0 (if ((F T M).map (prod.fst : V ⨯ V ⟶ V) q).val =
          ((F T M).map (prod.snd : V ⨯ V ⟶ V) q).val then 1 else 0) := by
  let r := (F T M).map (toRawProduct T V V) q
  let out := (F T M).map (representedArrow T (SyntacticDecidableVariables.equalityMorphism T V)) r
  have h := (PredicateInterpretation.map_class_eq_iff T M
    (SyntacticDecidableVariables.equalityMorphism T V) r out).mp rfl
  change (SyntacticDecidableVariables.equalityGraph V).val.Evalb ![r.val,out.val] at h
  have hr := toRawProduct_value T M V V q
  change r.val = _ at hr
  rw [hr,SyntacticDecidableVariables.equalityGraph_pair] at h
  rw [Functor.map_comp_apply]
  change out.val = _
  by_cases he : ((F T M).map (prod.fst : V ⨯ V ⟶ V) q).val =
      ((F T M).map (prod.snd : V ⨯ V ⟶ V) q).val
  · rw [ite_eq_left he]
    rcases h.2.2 with ⟨_,ho⟩ | ⟨hne,_⟩
    · exact ho
    · exact (hne he).elim
  · rw [ite_eq_right he]
    rcases h.2.2 with ⟨heq,_⟩ | ⟨_,ho⟩
    · exact (he heq).elim
    · exact ho

theorem equalityTest_point (V : PredicateCategory T) (q : Obj T M (V ⨯ V)) (b : Bool)
    (hb : (((F T M).map (prod.fst : V ⨯ V ⟶ V) q).val =
      ((F T M).map (prod.snd : V ⨯ V ⟶ V) q).val) ↔ b = true) :
    (F T M).map (SyntacticDecidableVariables.test T V) q =
      (F T M).map (Two.constant (V ⨯ V) b) q := by
  have hi : (if ((F T M).map (prod.fst : V ⨯ V ⟶ V) q).val =
      ((F T M).map (prod.snd : V ⨯ V ⟶ V) q).val then (1 : M) else 0) =
        if b then 1 else 0 := by
    cases b <;> simp_all
  have hr : (F T M).map (toRawProduct T V V ≫
      representedArrow T (SyntacticDecidableVariables.equalityMorphism T V)) q =
      (F T M).map (rawBooleanConstant T (V ⨯ V) b) q := by
    apply Subtype.ext
    rw [rawEquality_value,rawBooleanConstant_value,hi]
  unfold SyntacticDecidableVariables.test
  rw [← Category.assoc]
  rw [Functor.map_comp_apply,hr,← Functor.map_comp_apply,rawBooleanConstant_iso]

theorem equalityTest_comp_point {X : PredicateCategory T} (V : PredicateCategory T)
    (f : X ⟶ V ⨯ V) (q : Obj T M X) (b : Bool)
    (hb : (((F T M).map (prod.fst : V ⨯ V ⟶ V) ((F T M).map f q)).val =
      ((F T M).map (prod.snd : V ⨯ V ⟶ V) ((F T M).map f q)).val) ↔ b = true) :
    (F T M).map (f ≫ SyntacticDecidableVariables.test T V) q =
      (F T M).map (Two.constant X b) q := by
  rw [Functor.map_comp_apply]
  exact (equalityTest_point T M V ((F T M).map f q) b hb).trans
    (model_constant_comp T M f q b)

end Models
end CategoricalEssentialIncompleteness.V46.ConcreteNamedComparison
