/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.ClassicalProgramCategory
public import FailureOfComposition.ConcreteAdequacy

/-! # Turing universality and categorical inseparability in `Rec` -/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open CategoryTheory CategoryTheory.RestrictionCategory
open CategoryTheory.CoprodStruct CategoryTheory.HasCoproducts
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FailureOfComposition.TypedProgramCategory FailureOfComposition.TypedTuringMorphism
open FailureOfComposition.TypedRecursionCategory
open PCategoryStruct

namespace CategoricalEssentialIncompleteness.LocalConnectedness.ClassicalPrograms

instance : RecursionCategory.Prodominical Rec where
  nearProd_zero_right {A B X Y} f := by
    obtain ⟨f, rfl⟩ := exists_source f
    simpa [Q_product, Q_zero] using congrArg (fun f => Q.map f)
      (RecursionCategory.Prodominical.nearProd_zero_right (X := X.base) (Y := Y.base) f)
  nearProd_zero_left {A B X Y} f := by
    obtain ⟨f, rfl⟩ := exists_source f
    simpa [Q_product, Q_zero] using congrArg (fun f => Q.map f)
      (RecursionCategory.Prodominical.nearProd_zero_left (X := X.base) (Y := Y.base) f)

instance : RecursionCategory.Isotype Rec where
  iso X Y := by
    obtain ⟨e⟩ := RecursionCategory.Isotype.iso X.base Y.base
    exact ⟨Q.mapIso e⟩

instance : HasChoice Rec where
  exists_isSection f := by
    obtain ⟨f, rfl⟩ := exists_source f
    obtain ⟨s, hs⟩ := HasChoice.exists_isSection f
    refine ⟨Q.map s, ?_, ?_⟩
    · simpa only [Q.map_comp, Q_product_restriction] using
        congrArg (fun f => Q.map f) hs.comp_eq_rst
    · simpa only [Q.map_comp] using congrArg (fun f => Q.map f) hs.comp_self

def U : Rec := Q.obj (omegaObject 𝗣𝗔)

def tau : nearProd U U ⟶ U := Q.map (typedTau 𝗣𝗔)

theorem tau_isTuring : RecursionCategory.IsTuringMorphism tau := by
  intro V f
  obtain ⟨f, hf⟩ := exists_source f
  obtain ⟨g, hg, he⟩ := typedTau_isTuringMorphism 𝗣𝗔 V.base f
  refine ⟨Q.map g, quotientRangeFunctor.map_total g hg, ?_⟩
  have hh := congrArg (fun f => Q.map f) he
  simpa [Q.map_comp, Q_product, Q.map_id, Q_obj_base, Q_product_obj, U, tau, hf] using hh

instance : RecursionCategory.PRecursionCategory Rec where
  W := U
  X := U
  Y := U
  tau := tau
  is_turing := tau_isTuring

def parityIso : U ≅ coprod U U := Q.mapIso (omegaCoprodIso 𝗣𝗔).symm

theorem inclusion_nonzero : J.map (𝟙 U) ≠ 0 := by
  intro h
  have he := congrFun h (0 : ℕ)
  change Part.some (0 : ℕ) = Part.none at he
  exact Part.notMem_none 0 (he ▸ Part.mem_some 0)

def evenDiagonal : Idem U := diagonal0 tau parityIso
def oddDiagonal : Idem U := diagonal1 tau parityIso

/-- The actual self-application pair is constructed by Theorem 6.3 in the
classical recursion category. -/
theorem diagonal_inseparable : Inseparable evenDiagonal oddDiagonal :=
  range_functor_lifting inclusionRangeFunctor tau tau_isTuring parityIso inclusion_nonzero
    (section_lifting_of_choice inclusionRangeFunctor U)

end CategoricalEssentialIncompleteness.LocalConnectedness.ClassicalPrograms
