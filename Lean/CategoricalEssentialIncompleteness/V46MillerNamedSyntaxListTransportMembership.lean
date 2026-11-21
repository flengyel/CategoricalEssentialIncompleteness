/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerNamedSyntaxListTransportOperations


/-! # Membership in lists of variable names -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
namespace CategoricalEssentialIncompleteness.V46.Miller.NamedSyntaxComparison.ListTransport
open SyntacticLists.Transport
open Derivation
variable (P : Uniform.Family) (V : PredicateCategory 𝗣𝗔)
local notation "F" => Syntax.predicateFunctor P
local notation "L" => SyntacticLists.stableListAlgebra 𝗣𝗔 V
local notation "R" => NamedSyntaxComparison.mappedListStable P V
variable (S : DecidableVariables V)
theorem membershipOverMap_left {U : PredicateCategory 𝗣𝗔} {A B : Over U} (f : A ⟶ B) :
    ((sliceFunctor (F) U).map f).left=(F).map f.left := rfl
/-- The coefficient and carrier isomorphisms are family comparisons. The equality-test
square is derived from the diagonal. -/
def mappedMembershipAlgebraIso :
    (mappedList (sliceFunctor (F) V) (constantFamily V V) (constantFamily ((F).obj V) ((F).obj V))
      (coefficientComparison (F) V V ((F).obj V) (Iso.refl _)) (StableListAlgebra.membershipAlgebra S)).asAlgebra ≅
      (StableListAlgebra.membershipAlgebra (Derivation.mappedEquality (F) S)).asAlgebra := by
  let H := sliceFunctor (F) V
  let A := StableListAlgebra.membershipAlgebra S
  let B := StableListAlgebra.membershipAlgebra (Derivation.mappedEquality (F) S)
  let i := coefficientComparison (F) V (Two (PredicateCategory 𝗣𝗔)) (Two (Total.TotalCategory P)) (Derivation.booleanIso (F))
  let j := listStepComparison (F) V V (Two (PredicateCategory 𝗣𝗔)) ((F).obj V) (Two (Total.TotalCategory P)) (Iso.refl _) (Derivation.booleanIso (F))
  refine mappedConstructorsIso H (constantFamily V V) (constantFamily ((F).obj V) ((F).obj V))
    (coefficientComparison (F) V V ((F).obj V) (Iso.refl _)) A B i ?_ ?_
  · apply Over.OverMorphism.ext
    apply prod.hom_ext
    · exact (Over.w (H.map A.nil ≫ i.hom)).trans
        (Over.w (terminalComparison H ≫ B.nil)).symm
    · have h₀ : A.nil.left ≫ prod.snd = Two.constant (⊤_ (Over V)).left false :=
        prod.lift_snd _ _
      have h₁ : B.nil.left ≫ prod.snd = Two.constant (⊤_ (Over ((F).obj V))).left false :=
        prod.lift_snd _ _
      dsimp only [H]
      simp only [Over.comp_left,membershipOverMap_left,Category.assoc]
      rw [coefficientComparison_snd,← Category.assoc,← (F).map_comp,h₀,h₁,
        map_constant (F) (⊤_ (Over V)).left false,Two.comp_constant]
      rfl
  · dsimp only [H,A,i]
    rw [← Category.assoc]
    change H.map A.cons ≫ i.hom = j.hom ≫ B.cons
    apply Over.OverMorphism.ext
    apply prod.hom_ext
    · exact (Over.w (H.map A.cons ≫ i.hom)).trans (Over.w (j.hom ≫ B.cons)).symm
    · let U := constantFamily V V ⨯ constantFamily V (Two (PredicateCategory 𝗣𝗔))
      let Z := constantFamily ((F).obj V) ((F).obj V) ⨯ constantFamily ((F).obj V) (Two (Total.TotalCategory P))
      let χ := prod.lift U.hom (listStepHead V V (Two (PredicateCategory 𝗣𝗔))) ≫ S.test
      let χ' := prod.lift Z.hom (listStepHead ((F).obj V) ((F).obj V) (Two (Total.TotalCategory P))) ≫ (Derivation.mappedEquality (F) S).test
      have h₀ : A.cons.left ≫ prod.snd =
          Two.binary Bool.or χ (listStepValue V V (Two (PredicateCategory 𝗣𝗔))) := prod.lift_snd _ _
      have h₁ : B.cons.left ≫ prod.snd =
          Two.binary Bool.or χ' (listStepValue ((F).obj V) ((F).obj V) (Two (Total.TotalCategory P))) := prod.lift_snd _ _
      have heq := listStepComparison_test (F) (Derivation.booleanIso (F)) S
      have hval := listStepComparison_value (F) V V (Two (PredicateCategory 𝗣𝗔)) ((F).obj V) (Two (Total.TotalCategory P)) (Iso.refl _) (Derivation.booleanIso (F))
      dsimp only [H]
      simp only [Over.comp_left,membershipOverMap_left,Category.assoc]
      rw [coefficientComparison_snd,← Category.assoc,← (F).map_comp,h₀,h₁,
        map_boolean_binary (F) Bool.or,Two.comp_binary]
      rw [heq,hval]


/-- Membership equality, derived from the mapped equality classifier and the unique
parameterized fold. -/
theorem map_membership :
    (F).map ((L).membership S) ≫ (Derivation.booleanIso (F)).hom=
      prodComparison (F) V (L).algebra.carrier ≫ (R).membership (Derivation.mappedEquality (F) S) := by
  let H := sliceFunctor (F) V
  let a := familyComparison (F) V (L).algebra.carrier
  let i := coefficientComparison (F) V (Two (PredicateCategory 𝗣𝗔)) (Two (Total.TotalCategory P))
    (Derivation.booleanIso (F))
  have h := actualParameterFold P V V (StableListAlgebra.membershipAlgebra S)
    (StableListAlgebra.membershipAlgebra (Derivation.mappedEquality (F) S))
    (mappedMembershipAlgebraIso P V S)
  change a.inv ≫ H.map ((L).membershipFold S) ≫ i.hom=(R).membershipFold
    (Derivation.mappedEquality (F) S) at h
  have hf : H.map ((L).membershipFold S) ≫ i.hom=
      a.hom ≫ (R).membershipFold (Derivation.mappedEquality (F) S) := by
    apply (cancel_epi a.inv).mp
    simpa only [Category.assoc,Iso.inv_hom_id_assoc] using h
  have hh := congrArg (fun f => f.left ≫ prod.snd) hf
  dsimp only [H] at hh
  simp only [Over.comp_left,membershipOverMap_left,Category.assoc] at hh
  rw [coefficientComparison_snd,← Category.assoc,← (F).map_comp] at hh
  change (F).map ((L).membership S) ≫ (Derivation.booleanIso (F)).hom=
    a.hom.left ≫ (R).membership (Derivation.mappedEquality (F) S) at hh
  exact hh
end CategoricalEssentialIncompleteness.V46.Miller.NamedSyntaxComparison.ListTransport
