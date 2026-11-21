/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SyntacticListsDecode
public import CategoricalEssentialIncompleteness.V46SyntacticListEvaluationLaws

/-! # The fold into an arbitrary parameter-family algebra -/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.Limits
open FailureOfComposition.ProofSearch FailureOfComposition.CodedObjectMembership
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates

namespace CategoricalEssentialIncompleteness.V46.SyntacticLists

variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
variable {P V : PredicateCategory T} (B : ListAlgebra (D := Over P) (constantFamily P V))

def foldMap : P ⨯ listObject T V ⟶ B.carrier.left :=
  toRawProduct T P (listObject T V) ≫
    representedArrow T (decode T B).evaluationMorphism

section Models
variable (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T]

/-- Evaluation of the categorical fold is exactly the arithmetic record formula, read at
the two source product projections. -/
theorem foldMap_eval (q : Obj T M (P ⨯ listObject T V))
    (y : Obj T M B.carrier.left) :
    (F T M).map (foldMap T B) q = y ↔
      (decode T B).evaluationFormula.val.Evalb
        ![((F T M).map (prod.fst : P ⨯ listObject T V ⟶ P) q).val,
          ((F T M).map (prod.snd : P ⨯ listObject T V ⟶ listObject T V) q).val, y.val] := by
  let : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 := models_of_subtheory (U := T) inferInstance
  change (F T M).map (toRawProduct T P (listObject T V) ≫
    representedArrow T (decode T B).evaluationMorphism) q = y ↔ _
  rw [Functor.map_comp]
  change (F T M).map (representedArrow T (decode T B).evaluationMorphism)
    ((F T M).map (toRawProduct T P (listObject T V)) q) = y ↔ _
  refine (PredicateInterpretation.map_class_eq_iff T M (decode T B).evaluationMorphism
    ((F T M).map (toRawProduct T P (listObject T V)) q) y).trans ?_
  change (decode T B).evaluationGraph.val.Evalb
    ![((F T M).map (toRawProduct T P (listObject T V)) q).val, y.val] ↔ _
  rw [toRawProduct_value]
  simp [SyntacticListEvaluation.SliceAlgebra.evaluationGraph]

end Models

theorem foldMap_over : foldMap T B ≫ B.carrier.hom =
    (prod.fst : P ⨯ listObject T V ⟶ P) := by
  apply PredicateInterpretation.jointly_faithful T
  intro M _ _
  rw [Functor.map_comp]
  ext q
  have he := (foldMap_eval T B M q ((F T M).map (foldMap T B) q)).mp rfl
  have hf := ((decode T B).evaluation_fiber _ _ _ he).2
  exact (chosenGraph_map_iff T M B.carrier.hom
    ((F T M).map (foldMap T B) q) ((F T M).map prod.fst q)).mp hf

/-- This fold is a morphism in the slice, for arbitrary fibers and arbitrary projections
to the parameter object. -/
def fold : constantFamily P (listObject T V) ⟶ B.carrier :=
  Over.homMk (foldMap T B) (foldMap_over T B)

section Models
variable (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

omit [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] in
theorem fold_pairPoint (p : Obj T M P) (a : Obj T M (listObject T V))
    (y : Obj T M B.carrier.left) :
    (F T M).map (fold T B).left (pairPoint T M p a) = y ↔
      (decode T B).evaluationFormula.val.Evalb ![p.val, a.val, y.val] := by
  change (F T M).map (foldMap T B) (pairPoint T M p a) = y ↔ _
  have h := foldMap_eval T B M (pairPoint T M p a) y
  rw [pairPoint_fst, pairPoint_snd] at h
  exact h

end Models

/-- The decoded nil map agrees with the original slice constructor at
every point of the slice terminal object. -/
theorem terminal_nilMap : (⊤_ (Over P)).hom ≫ nilMap T B = B.nil.left := by
  rw [nilMap, ← terminalOverIso_hom, ← Category.assoc,
    (terminalOverIso T P).hom_inv_id, Category.id_comp]

section ConstructorValues
variable (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

omit [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] in
theorem parameter_nil_fst (t : Obj T M (⊤_ (Over P)).left) :
    (F T M).map (prod.fst : P ⨯ listObject T V ⟶ P)
      ((F T M).map ((algebra T V).withParameters P).nil.left t) =
        (F T M).map (⊤_ (Over P)).hom t := by
  have h : ((algebra T V).withParameters P).nil.left ≫
      (prod.fst : P ⨯ listObject T V ⟶ P) = (⊤_ (Over P)).hom := by
    exact prod.lift_fst _ _
  have hm := congrArg (F T M).map h
  rw [Functor.map_comp] at hm
  exact ConcreteCategory.congr_hom hm t

omit [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] in
theorem parameter_nil_snd (t : Obj T M (⊤_ (Over P)).left) :
    ((F T M).map (prod.snd : P ⨯ listObject T V ⟶ listObject T V)
      ((F T M).map ((algebra T V).withParameters P).nil.left t)).val = 0 := by
  have h : ((algebra T V).withParameters P).nil.left ≫
      (prod.snd : P ⨯ listObject T V ⟶ listObject T V) =
        terminal.from (⊤_ (Over P)).left ≫ (algebra T V).nil := by
    exact prod.lift_snd _ _
  have hm := congrArg (F T M).map h
  rw [Functor.map_comp, Functor.map_comp] at hm
  have he := ConcreteCategory.congr_hom hm t
  exact (congrArg Subtype.val he).trans
    (nil_value T M (⊤_ (PredicateCategory T)) V
      ((F T M).map (terminal.from (⊤_ (Over P)).left) t))


omit [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] in
theorem parameter_cons_fst
    (q : Obj T M (constantFamily P V ⨯ constantFamily P (listObject T V)).left) :
    (F T M).map (prod.fst : P ⨯ listObject T V ⟶ P)
      ((F T M).map ((algebra T V).withParameters P).cons.left q) =
        (F T M).map (constantFamily P V ⨯ constantFamily P (listObject T V)).hom q := by
  have h : ((algebra T V).withParameters P).cons.left ≫
      (prod.fst : P ⨯ listObject T V ⟶ P) =
        (constantFamily P V ⨯ constantFamily P (listObject T V)).hom := by
    exact prod.lift_fst _ _
  have hm := congrArg (F T M).map h
  rw [Functor.map_comp] at hm
  exact ConcreteCategory.congr_hom hm q

theorem parameter_cons_snd
    (q : Obj T M (constantFamily P V ⨯ constantFamily P (listObject T V)).left) :
    ((F T M).map (prod.snd : P ⨯ listObject T V ⟶ listObject T V)
      ((F T M).map ((algebra T V).withParameters P).cons.left q)).val =
        adjoin
          ((F T M).map (prod.snd : P ⨯ V ⟶ V)
            ((F T M).map (prod.fst : constantFamily P V ⨯
              constantFamily P (listObject T V) ⟶ constantFamily P V).left q)).val
          ((F T M).map (prod.snd : P ⨯ listObject T V ⟶ listObject T V)
            ((F T M).map (prod.snd : constantFamily P V ⨯
              constantFamily P (listObject T V) ⟶
                constantFamily P (listObject T V)).left q)).val := by
  let u : (constantFamily P V ⨯ constantFamily P (listObject T V)).left ⟶
      V ⨯ listObject T V := prod.lift
        ((prod.fst : constantFamily P V ⨯ constantFamily P (listObject T V) ⟶
          constantFamily P V).left ≫ prod.snd)
        ((prod.snd : constantFamily P V ⨯ constantFamily P (listObject T V) ⟶
          constantFamily P (listObject T V)).left ≫ prod.snd)
  have h : ((algebra T V).withParameters P).cons.left ≫
      (prod.snd : P ⨯ listObject T V ⟶ listObject T V) = u ≫ (algebra T V).cons := by
    exact prod.lift_snd _ _
  have hm := congrArg (F T M).map h
  rw [Functor.map_comp, Functor.map_comp] at hm
  rw [show (F T M).map (prod.snd : P ⨯ listObject T V ⟶ listObject T V)
      ((F T M).map ((algebra T V).withParameters P).cons.left q) =
        (F T M).map (algebra T V).cons ((F T M).map u q) from
      ConcreteCategory.congr_hom hm q, cons_value]
  have hf := congrArg (F T M).map (prod.lift_fst
    ((prod.fst : constantFamily P V ⨯ constantFamily P (listObject T V) ⟶
      constantFamily P V).left ≫ (prod.snd : P ⨯ V ⟶ V))
    ((prod.snd : constantFamily P V ⨯ constantFamily P (listObject T V) ⟶
      constantFamily P (listObject T V)).left ≫
        (prod.snd : P ⨯ listObject T V ⟶ listObject T V)))
  have hs := congrArg (F T M).map (prod.lift_snd
    ((prod.fst : constantFamily P V ⨯ constantFamily P (listObject T V) ⟶
      constantFamily P V).left ≫ (prod.snd : P ⨯ V ⟶ V))
    ((prod.snd : constantFamily P V ⨯ constantFamily P (listObject T V) ⟶
      constantFamily P (listObject T V)).left ≫
        (prod.snd : P ⨯ listObject T V ⟶ listObject T V)))
  simp only [Functor.map_comp] at hf hs
  exact congrArg₂ adjoin
    (congrArg Subtype.val (ConcreteCategory.congr_hom hf q))
    (congrArg Subtype.val (ConcreteCategory.congr_hom hs q))

end ConstructorValues

theorem fold_nil : ((algebra T V).withParameters P).nil ≫ fold T B = B.nil := by
  apply Over.OverMorphism.ext
  apply PredicateInterpretation.jointly_faithful T
  intro M _ _
  let : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 := models_of_subtheory (U := T) inferInstance
  change (F T M).map (((algebra T V).withParameters P).nil.left ≫ foldMap T B) = _
  rw [Functor.map_comp]
  apply ConcreteCategory.hom_ext
  intro t
  change (F T M).map (foldMap T B)
    ((F T M).map ((algebra T V).withParameters P).nil.left t) =
      (F T M).map B.nil.left t
  apply (foldMap_eval T B M _ _).mpr
  rw [parameter_nil_fst, parameter_nil_snd, (decode T B).evaluation_nil]
  apply (chosenGraph_map_iff T M (nilMap T B) _ _).mpr
  have hm := congrArg (F T M).map (terminal_nilMap T B)
  rw [Functor.map_comp] at hm
  exact ConcreteCategory.congr_hom hm t

theorem fold_cons : ((algebra T V).withParameters P).cons ≫ fold T B =
    prod.map (𝟙 (constantFamily P V)) (fold T B) ≫ B.cons := by
  apply Over.OverMorphism.ext
  apply PredicateInterpretation.jointly_faithful T
  intro M _ _
  let : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 := models_of_subtheory (U := T) inferInstance
  change (F T M).map (((algebra T V).withParameters P).cons.left ≫ foldMap T B) =
    (F T M).map ((prod.map (𝟙 (constantFamily P V)) (fold T B)).left ≫ B.cons.left)
  rw [Functor.map_comp, Functor.map_comp]
  apply ConcreteCategory.hom_ext
  intro q
  let u := (F T M).map (prod.fst : constantFamily P V ⨯
    constantFamily P (listObject T V) ⟶ constantFamily P V).left q
  let w := (F T M).map (prod.snd : constantFamily P V ⨯
    constantFamily P (listObject T V) ⟶ constantFamily P (listObject T V)).left q
  let p := (F T M).map (prod.fst : P ⨯ V ⟶ P) u
  let v := (F T M).map (prod.snd : P ⨯ V ⟶ V) u
  let a := (F T M).map (prod.snd : P ⨯ listObject T V ⟶ listObject T V) w
  let x := (F T M).map (fold T B).left w
  let r := (F T M).map (prod.map (𝟙 (constantFamily P V)) (fold T B)).left q
  let y := (F T M).map B.cons.left r
  have hbase : (F T M).map (constantFamily P V ⨯
      constantFamily P (listObject T V)).hom q = p :=
    (over_value T M (prod.fst : constantFamily P V ⨯
      constantFamily P (listObject T V) ⟶ constantFamily P V) q).symm
  have hwp : (F T M).map (prod.fst : P ⨯ listObject T V ⟶ P) w = p :=
    (over_value T M (prod.snd : constantFamily P V ⨯
      constantFamily P (listObject T V) ⟶ constantFamily P (listObject T V)) q).trans hbase
  have hx : (decode T B).evaluationFormula.val.Evalb ![p.val, a.val, x.val] := by
    have hh := (foldMap_eval T B M w x).mp rfl
    rw [hwp] at hh
    exact hh
  have hr₁ : (F T M).map (consFirst T B) r = u := by
    have hh := modelOverProduct_map_fst T M (𝟙 (constantFamily P V)) (fold T B) q
    have hi : (F T M).map (Over.Hom.left (𝟙 (constantFamily P V))) u = u :=
      ConcreteCategory.congr_hom ((F T M).map_id (P ⨯ V)) u
    exact hh.trans hi
  have hr₂ : (F T M).map (consSecond T B) r = x :=
    modelOverProduct_map_snd T M (𝟙 (constantFamily P V)) (fold T B) q
  have hc : (decodedCons T B).val.Evalb ![p.val, v.val, x.val, y.val] :=
    (decodedCons_model T B M p v x y).mpr
      ⟨r, (congrArg ((F T M).map (prod.fst : P ⨯ V ⟶ P)) hr₁),
        (congrArg ((F T M).map (prod.snd : P ⨯ V ⟶ V)) hr₁), hr₂, rfl⟩
  have he := (decode T B).evaluation_adjoin_intro p.val v.val a.val x.val y.val hx hc
  apply (foldMap_eval T B M _ y).mpr
  have hfst := (parameter_cons_fst T (P := P) (V := V) M q).trans hbase
  have hsnd := parameter_cons_snd T (P := P) (V := V) M q
  have hvec :
      ![((F T M).map (prod.fst : P ⨯ listObject T V ⟶ P)
        ((F T M).map ((algebra T V).withParameters P).cons.left q)).val,
        ((F T M).map (prod.snd : P ⨯ listObject T V ⟶ listObject T V)
          ((F T M).map ((algebra T V).withParameters P).cons.left q)).val, y.val] =
      ![p.val, adjoin v.val a.val, y.val] := by
    funext i
    fin_cases i
    · exact congrArg Subtype.val hfst
    · exact hsnd
    · rfl
  exact (congrArg (fun e => (decode T B).evaluationFormula.val.Evalb e) hvec).mpr he

end CategoricalEssentialIncompleteness.V46.SyntacticLists
