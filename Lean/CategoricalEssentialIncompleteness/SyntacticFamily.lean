/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.CountableArithmeticModels
public import CategoricalEssentialIncompleteness.PartialFunctionFamilies
public import CategoricalEssentialIncompleteness.SyntacticInseparability

/-! # The faithful family of arithmetic model interpretations -/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open CategoryTheory CategoryTheory.RestrictionCategory
open CategoryTheory.CoprodStruct CategoryTheory.HasCoproducts
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open FailureOfComposition.TypedProgramCategory FailureOfComposition.TypedTuringMorphism
open FailureOfComposition.TypedRecursionCategory

namespace CategoricalEssentialIncompleteness.LocalConnectedness.SyntacticModel

open PartialFunctions PartialFunctionFamilies

variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]

def familyFunctor : CodedProgramCategory T ⥤ Family (ModelIndex T) where
  obj Q s := letI := s.val; letI := s.property; (modelFunctor T ℕ).obj Q
  map f s := letI := s.val; letI := s.property; (modelFunctor T ℕ).map f
  map_id Q := funext fun s => by
    letI := s.val; letI := s.property
    exact (modelFunctor T ℕ).map_id Q
  map_comp f g := funext fun s => by
    letI := s.val; letI := s.property
    exact (modelFunctor T ℕ).map_comp f g

instance family_faithful : (familyFunctor T).Faithful where
  map_injective h := joint_faithful_recursive_nat T _ _ fun s hs => congrFun h ⟨s, hs⟩

theorem family_comparison_eq_id (Q R : CodedProgramCategory T) :
    coproductComparison (familyFunctor T) Q R =
      𝟙 (coprod ((familyFunctor T).obj Q) ((familyFunctor T).obj R)) := by
  funext s
  letI := s.val; letI := s.property
  exact model_comparison_eq_id T ℕ Q R

def familyRangeFunctor : RangeFunctor (CodedProgramCategory T) (Family (ModelIndex T)) where
  toFunctor := familyFunctor T
  map_restrict f := funext fun s => by
    letI := s.val; letI := s.property
    exact model_map_restriction T ℕ f
  map_range f := funext fun s => by
    letI := s.val; letI := s.property
    exact model_map_range T ℕ f
  map_zero Q R := funext fun s => by
    letI := s.val; letI := s.property
    exact model_map_zero T ℕ Q R
  comparison_isIso Q R := by rw [family_comparison_eq_id]; infer_instance

theorem family_map_product {Q R S V : CodedProgramCategory T} (f : Q ⟶ R) (g : S ⟶ V) :
    (familyFunctor T).map (PCategoryStruct.nearProd_map f g) =
      fun s => PFun.prodMap ((familyFunctor T).map f s) ((familyFunctor T).map g s) := by
  funext s
  letI := s.val; letI := s.property
  exact model_map_product T ℕ f g

theorem family_map_sup {Q : CodedProgramCategory T} (a b : Idem Q) :
    (familyRangeFunctor T).mapIdem (a ⊔ b) =
      (familyRangeFunctor T).mapIdem a ⊔ (familyRangeFunctor T).mapIdem b :=
  (familyRangeFunctor T).map_sup a b

theorem family_map_first_projection
    (Q R : FailureOfComposition.CodedObjectMembership.STObjectCode) :
    (familyFunctor T).map (PCategoryStruct.p0 (object T Q) (object T R)) =
      fun _ => PFun.lift (Prod.fst : interpretedType ℕ Q × interpretedType ℕ R → interpretedType ℕ Q) := by
  funext s
  letI := s.val; letI := s.property
  exact model_map_first_projection T ℕ Q R

theorem family_map_second_projection
    (Q R : FailureOfComposition.CodedObjectMembership.STObjectCode) :
    (familyFunctor T).map (PCategoryStruct.p1 (object T Q) (object T R)) =
      fun _ => PFun.lift (Prod.snd : interpretedType ℕ Q × interpretedType ℕ R → interpretedType ℕ R) := by
  funext s
  letI := s.val; letI := s.property
  exact model_map_second_projection T ℕ Q R

theorem family_nonzero (hT : Consistent T) :
    (familyFunctor T).map (𝟙 (omegaObject T)) ≠ 0 := by
  obtain ⟨s⟩ := modelIndex_nonempty T hT
  rw [(familyFunctor T).map_id]
  intro he
  have h := congrFun (congrFun he s) (0 : ℕ)
  change Part.some (0 : ℕ) = Part.none at h
  exact Part.notMem_none 0 (h ▸ Part.mem_some 0)

/-- The exact model family instantiates Theorem 6.3.  The finite two-test
construction of Lemma 6.5 is recorded separately from the source-choice
sufficient condition used here. -/
theorem family_categorical_inseparable (hT : Consistent T) :
    Inseparable (syntacticPair0 T) (syntacticPair1 T) :=
  range_functor_lifting (familyRangeFunctor T) (typedTau T) (typedTau_isTuringMorphism T)
    (omegaCoprodIso T).symm (family_nonzero T hT)
    (section_lifting_of_choice (familyRangeFunctor T) (omegaObject T))

end CategoricalEssentialIncompleteness.LocalConnectedness.SyntacticModel
