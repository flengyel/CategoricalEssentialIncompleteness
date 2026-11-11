/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SyntacticComparison
public import CategoricalEssentialIncompleteness.SyntacticExtension

/-! # Arbitrary Turing diagonals under theory extension -/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open CategoryTheory CategoryTheory.RestrictionCategory
open CategoryTheory.CoprodStruct
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open FailureOfComposition.TypedProgramCategory
open PCategoryStruct (nearProd diag nearProd_map)

namespace CategoricalEssentialIncompleteness.LocalConnectedness.SyntacticExtension

variable (T T' : ArithmeticTheory) [𝗣𝗔 ⪯ T] [𝗣𝗔 ⪯ T'] [T ⪯ T']

/-- Every target morphism is the interpretation of the same external
program index in the weaker theory. -/
theorem map_surjective (X Y : CodedProgramCategory T) :
    Function.Surjective ((functor T T').map (X := X) (Y := Y)) := by
  intro f
  obtain ⟨q, hq⟩ := exists_arrowOfIndex T' (objectCode X) (objectCode Y) f
  exact ⟨arrowOfIndex T (objectCode X) (objectCode Y) q,
    (map_index T T' _ _ q).trans hq⟩

/-- Hom surjectivity and preservation of restriction products transport
any source Turing morphism, independently of the chosen universal program. -/
theorem map_isTuringMorphism {W X Y : CodedProgramCategory T}
    (τ : nearProd W X ⟶ Y) (hτ : RecursionCategory.IsTuringMorphism τ) :
    RecursionCategory.IsTuringMorphism ((functor T T').map τ) := by
  intro V φ
  let V₀ : CodedProgramCategory T := object T (objectCode V)
  obtain ⟨φ₀, hφ⟩ := map_surjective T T' (nearProd V₀ X) Y φ
  obtain ⟨g, hg, heq⟩ := hτ V₀ φ₀
  refine ⟨(functor T T').map g, (rangeFunctor T T').map_total g hg, ?_⟩
  have h := congrArg (fun k => (functor T T').map k) heq
  rw [(functor T T').map_comp, map_product, (functor T T').map_id, hφ] at h
  exact h

theorem diagonal0_image {U : CodedProgramCategory T}
    (τ : nearProd U U ⟶ U) (b : U ≅ coprod U U) :
    (rangeFunctor T T').mapIdem (diagonal0 τ b) =
      diagonal0 ((functor T T').map τ) ((functor T T').mapIso b) := by
  apply Idem.ext
  change (functor T T').map (rst
    ((diag U ≫ τ ≫ b.hom) ≫ (summand0 U U).hom)) = _
  rw [map_restriction, (functor T T').map_comp, (functor T T').map_comp,
    (functor T T').map_comp, map_diagonal, map_summand0]
  rfl

theorem diagonal1_image {U : CodedProgramCategory T}
    (τ : nearProd U U ⟶ U) (b : U ≅ coprod U U) :
    (rangeFunctor T T').mapIdem (diagonal1 τ b) =
      diagonal1 ((functor T T').map τ) ((functor T T').mapIso b) := by
  apply Idem.ext
  change (functor T T').map (rst
    ((diag U ≫ τ ≫ b.hom) ≫ (summand1 U U).hom)) = _
  rw [map_restriction, (functor T T').map_comp, (functor T T').map_comp,
    (functor T T').map_comp, map_diagonal, map_summand1]
  rfl

/-- Corollary D.2: the images of an arbitrary source Turing diagonal pair
are the identical diagonal pair and remain inseparable in every consistent
theory extension. -/
theorem extension_arbitrary_pair_inseparable_v46 (hT' : Consistent T')
    (τ : nearProd (omegaObject T) (omegaObject T) ⟶ omegaObject T)
    (hτ : RecursionCategory.IsTuringMorphism τ)
    (b : omegaObject T ≅ coprod (omegaObject T) (omegaObject T)) :
    Inseparable ((rangeFunctor T T').mapIdem (diagonal0 τ b))
      ((rangeFunctor T T').mapIdem (diagonal1 τ b)) := by
  rw [diagonal0_image, diagonal1_image]
  exact SyntacticModel.syntactic_pair_inseparable_v46 T' hT'
    ((functor T T').map τ) (map_isTuringMorphism T T' τ hτ) ((functor T T').mapIso b)

end CategoricalEssentialIncompleteness.LocalConnectedness.SyntacticExtension
