/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.SyntacticFamily
public import CategoricalEssentialIncompleteness.SyntacticExtension

/-! # Theory extension and the faithful model families -/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open CategoryTheory FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open FailureOfComposition.TypedProgramCategory

namespace CategoricalEssentialIncompleteness.LocalConnectedness.SyntacticModel

open PartialFunctionFamilies

variable (T T' : ArithmeticTheory) [𝗣𝗔 ⪯ T] [𝗣𝗔 ⪯ T'] [T ⪯ T']

def restrictModelIndex (s : ModelIndex T') : ModelIndex T := by
  letI := s.val
  letI := s.property
  exact ⟨s.val, models_of_subtheory (U := T') inferInstance⟩

def familyProjection : Family (ModelIndex T) ⥤ Family (ModelIndex T') :=
  CategoryTheory.Pi.comap (fun _ : ModelIndex T => PartialFunctions.Pfn) (restrictModelIndex T T')

theorem coding_value_extension {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T']
    (Q : FailureOfComposition.CodedObjectMembership.STObjectCode) (x : interpretedType M Q) :
    letI : M↓[ℒₒᵣ] ⊧* T := models_of_subtheory (U := T') inferInstance
    (codingEquiv T' M Q x).val = (codingEquiv T M Q x).val := by
  letI : M↓[ℒₒᵣ] ⊧* T := models_of_subtheory (U := T') inferInstance
  let : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 := models_of_subtheory (U := T') inferInstance
  let : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := models_of_subtheory (U := 𝗣𝗔) inferInstance
  let : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := models_of_subtheory (U := 𝗜𝚺₁) inferInstance
  induction Q with
  | omega => rfl
  | product Q R hQ hR =>
    change Arithmetic.pair (codingEquiv T' M Q x.1).val (codingEquiv T' M R x.2).val =
      Arithmetic.pair (codingEquiv T M Q x.1).val (codingEquiv T M R x.2).val
    rw [hQ, hR]
  | coproduct Q R hQ hR =>
    cases x with
    | inl x =>
      change Arithmetic.pair (codingEquiv T' M Q x).val 0 =
        Arithmetic.pair (codingEquiv T M Q x).val 0
      rw [hQ]
    | inr x =>
      change Arithmetic.pair (codingEquiv T' M R x).val 1 =
        Arithmetic.pair (codingEquiv T M R x).val 1
      rw [hR]

theorem model_extension_map {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T']
    {Q R : CodedProgramCategory T} (f : Q ⟶ R) :
    letI : M↓[ℒₒᵣ] ⊧* T := models_of_subtheory (U := T') inferInstance
    (modelFunctor T' M).map ((SyntacticExtension.functor T T').map f) =
      (modelFunctor T M).map f := by
  letI : M↓[ℒₒᵣ] ⊧* T := models_of_subtheory (U := T') inferInstance
  obtain ⟨q, rfl⟩ := exists_arrowOfIndex T (objectCode Q) (objectCode R) f
  rw [SyntacticExtension.map_index]
  apply PFun.ext
  intro x y
  rw [mem_model_index, mem_model_index]
  rw [coding_value_extension T T', coding_value_extension T T']

/-- The comparison square commutes as an equality of functors. -/
theorem family_extension_square :
    SyntacticExtension.functor T T' ⋙ familyFunctor T' = familyFunctor T ⋙ familyProjection T T' := by
  refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
  intro Q R f
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  funext s
  letI := s.val
  letI := s.property
  exact model_extension_map T T' f

end CategoricalEssentialIncompleteness.LocalConnectedness.SyntacticModel
