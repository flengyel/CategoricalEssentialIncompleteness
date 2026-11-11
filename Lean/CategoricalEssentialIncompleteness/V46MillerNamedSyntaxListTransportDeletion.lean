/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerNamedSyntaxListTransportMembership


/-! # Definitions and theorems in `V46MillerNamedSyntaxListTransportDeletion` -/

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
theorem deletionOverMap_left {U : PredicateCategory 𝗣𝗔} {A B : Over U} (f : A ⟶ B) :
    ((sliceFunctor (F) U).map f).left=(F).map f.left := rfl
/-- This is an isomorphism of complete list algebras. Its cons equation
uses the proved transport of the actual equality-classified branch. -/
def mappedDeletionAlgebraIso :
    (mappedList (sliceFunctor (F) V) (constantFamily V V) (constantFamily ((F).obj V) ((F).obj V))
      (coefficientComparison (F) V V ((F).obj V) (Iso.refl _)) ((L).deletionAlgebra S)).asAlgebra ≅
      ((R).deletionAlgebra (Derivation.mappedEquality (F) S)).asAlgebra := by
  let H := sliceFunctor (F) V
  let A := (L).deletionAlgebra S
  let B := (R).deletionAlgebra (Derivation.mappedEquality (F) S)
  let i := coefficientComparison (F) V (L).algebra.carrier ((F).obj (L).algebra.carrier) (Iso.refl _)
  let j := listStepComparison (F) V V (L).algebra.carrier ((F).obj V) ((F).obj (L).algebra.carrier)
    (Iso.refl _) (Iso.refl _)
  refine mappedConstructorsIso H (constantFamily V V) (constantFamily ((F).obj V) ((F).obj V))
    (coefficientComparison (F) V V ((F).obj V) (Iso.refl _)) A B i ?_ ?_
  · apply Over.OverMorphism.ext
    apply prod.hom_ext
    · exact (Over.w (H.map A.nil ≫ i.hom)).trans
        (Over.w (terminalComparison H ≫ B.nil)).symm
    · have h₀ : A.nil.left ≫ prod.snd =
          terminal.from (⊤_ (Over V)).left ≫ (L).algebra.nil := prod.lift_snd _ _
      have h₁ : B.nil.left ≫ prod.snd =
          terminal.from (⊤_ (Over ((F).obj V))).left ≫ (R).algebra.nil := prod.lift_snd _ _
      have ht : (F).map (terminal.from (⊤_ (Over V)).left) ≫
          terminalComparison (F) = terminal.from ((F).obj (⊤_ (Over V)).left) :=
        terminalIsTerminal.hom_ext _ _
      dsimp only [H]
      simp only [Over.comp_left,deletionOverMap_left,Category.assoc]
      erw [coefficientComparison_snd]
      simp only [Iso.refl_hom,Category.comp_id]
      erw [← (F).map_comp,h₀,h₁,(F).map_comp]
      have hterm : (terminalComparison H).left ≫ terminal.from (⊤_ (Over ((F).obj V))).left =
          terminal.from ((F).obj (⊤_ (Over V)).left) := terminalIsTerminal.hom_ext _ _
      calc
        _ = (F).map (terminal.from (⊤_ (Over V)).left) ≫
            (terminalComparison (F) ≫ (R).algebra.nil) :=
          congrArg (fun f => (F).map (terminal.from (⊤_ (Over V)).left) ≫ f) (map_nil P V)
        _ = ((F).map (terminal.from (⊤_ (Over V)).left) ≫ terminalComparison (F)) ≫
            (R).algebra.nil := (Category.assoc _ _ _).symm
        _ = terminal.from ((F).obj (⊤_ (Over V)).left) ≫ (R).algebra.nil :=
          congrArg (fun f => f ≫ (R).algebra.nil) ht
        _ = ((terminalComparison H).left ≫ terminal.from (⊤_ (Over ((F).obj V))).left) ≫
            (R).algebra.nil := congrArg (fun f => f ≫ (R).algebra.nil) hterm.symm
        _ = _ := Category.assoc _ _ _

  · rw [← Category.assoc]
    change H.map A.cons ≫ i.hom = j.hom ≫ B.cons
    apply Over.OverMorphism.ext
    apply prod.hom_ext
    · exact (Over.w (H.map A.cons ≫ i.hom)).trans (Over.w (j.hom ≫ B.cons)).symm
    · let U := constantFamily V V ⨯ constantFamily V (L).algebra.carrier
      let Z := constantFamily ((F).obj V) ((F).obj V) ⨯ constantFamily ((F).obj V) (R).algebra.carrier
      let χ := prod.lift U.hom (listStepHead V V (L).algebra.carrier) ≫ S.test
      let χ' := prod.lift Z.hom (listStepHead ((F).obj V) ((F).obj V) (R).algebra.carrier) ≫ (Derivation.mappedEquality (F) S).test
      let k := prod.lift (listStepHead V V (L).algebra.carrier)
        (listStepValue V V (L).algebra.carrier) ≫ (L).algebra.cons
      let k' := prod.lift (listStepHead ((F).obj V) ((F).obj V) (R).algebra.carrier)
        (listStepValue ((F).obj V) ((F).obj V) (R).algebra.carrier) ≫ (R).algebra.cons
      have h₀ : A.cons.left ≫ prod.snd =
          Two.branch χ k (listStepValue V V (L).algebra.carrier) := prod.lift_snd _ _
      have h₁ : B.cons.left ≫ prod.snd =
          Two.branch χ' k' (listStepValue ((F).obj V) ((F).obj V) (R).algebra.carrier) := prod.lift_snd _ _
      have heq : j.hom.left ≫ χ' = (F).map χ ≫ (Derivation.booleanIso (F)).hom :=
        listStepComparison_test (F) (Iso.refl _) S
      have hval : j.hom.left ≫ listStepValue ((F).obj V) ((F).obj V) (R).algebra.carrier =
          (F).map (listStepValue V V (L).algebra.carrier) := by
        change j.hom.left ≫ listStepValue ((F).obj V) ((F).obj V) ((F).obj (L).algebra.carrier) = _
        simpa only [Iso.refl_hom,Category.comp_id] using
          listStepComparison_value (F) V V (L).algebra.carrier ((F).obj V) ((F).obj (L).algebra.carrier)
            (Iso.refl _) (Iso.refl _)
      have hhead : j.hom.left ≫ listStepHead ((F).obj V) ((F).obj V) (R).algebra.carrier=
          (F).map (listStepHead V V (L).algebra.carrier) := by
        change j.hom.left ≫ listStepHead ((F).obj V) ((F).obj V) ((F).obj (L).algebra.carrier) = _
        simpa only [Iso.refl_hom,Category.comp_id] using
          listStepComparison_head (F) V V (L).algebra.carrier ((F).obj V) ((F).obj (L).algebra.carrier)
            (Iso.refl _) (Iso.refl _)
      have hpair : j.hom.left ≫ prod.lift
          (listStepHead ((F).obj V) ((F).obj V) (R).algebra.carrier)
          (listStepValue ((F).obj V) ((F).obj V) (R).algebra.carrier)=
          (F).map (prod.lift (listStepHead V V (L).algebra.carrier)
            (listStepValue V V (L).algebra.carrier)) ≫ prodComparison (F) V (L).algebra.carrier := by
        rw [prod.comp_lift,hhead,hval]
        exact (map_lift (F) _ _).symm
      have hpre : j.hom.left ≫ k'=(F).map k := by
        change j.hom.left ≫ (prod.lift _ _ ≫ (R).algebra.cons)=
          (F).map (prod.lift _ _ ≫ (L).algebra.cons)
        rw [(F).map_comp,map_cons P V,← Category.assoc,hpair,Category.assoc]
      dsimp only [H]
      simp only [Over.comp_left,deletionOverMap_left,Category.assoc]
      erw [coefficientComparison_snd]
      simp only [Iso.refl_hom,Category.comp_id]
      erw [← (F).map_comp,h₀,h₁,map_branch (F),SyntaxOperationsTransport.branch_precomp,heq,hpre,hval]


/-- Deletion uses the actual transported equality classifier and the
constructed conditional, with no supplied operation comparison. -/
theorem map_deletion : (F).map ((L).deletion S)=
    prodComparison (F) V (L).algebra.carrier ≫ (R).deletion (Derivation.mappedEquality (F) S) := by
  let H := sliceFunctor (F) V
  let a := familyComparison (F) V (L).algebra.carrier
  let i := coefficientComparison (F) V (L).algebra.carrier ((F).obj (L).algebra.carrier) (Iso.refl _)
  have h := actualParameterFold P V V ((L).deletionAlgebra S)
    ((R).deletionAlgebra (Derivation.mappedEquality (F) S)) (mappedDeletionAlgebraIso P V S)
  change a.inv ≫ H.map ((L).deletionFold S) ≫ i.hom=
    (R).deletionFold (Derivation.mappedEquality (F) S) at h
  have hf : H.map ((L).deletionFold S) ≫ i.hom=
      a.hom ≫ (R).deletionFold (Derivation.mappedEquality (F) S) := by
    apply (cancel_epi a.inv).mp
    simpa only [Category.assoc,Iso.inv_hom_id_assoc] using h
  have hh := congrArg (fun f => f.left ≫ prod.snd) hf
  dsimp only [H] at hh
  simp only [Over.comp_left,deletionOverMap_left,Category.assoc] at hh
  erw [coefficientComparison_snd] at hh
  simp only [Iso.refl_hom,Category.comp_id] at hh
  erw [← (F).map_comp] at hh
  exact hh
end CategoricalEssentialIncompleteness.V46.Miller.NamedSyntaxComparison.ListTransport
