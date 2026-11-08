/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46MillerNamedSyntaxListTransportCoordinates
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
namespace CategoricalEssentialIncompleteness.V46.Miller.NamedSyntaxComparison.ListTransport
open SyntacticLists.Transport
variable (P : Uniform.Family) (V : PredicateCategory 𝗣𝗔)
local notation "F" => Syntax.predicateFunctor P
local notation "L" => SyntacticLists.stableListAlgebra 𝗣𝗔 V
local notation "R" => NamedSyntaxComparison.mappedListStable P V

/-- The generic image constructors agree with the exact mapped list record
used by presentedSyntax, including its actual carrier. -/
def baseListIso :
    (mappedList (F) V ((F).obj V) (Iso.refl _) (L).algebra).asAlgebra ≅ (R).algebra.asAlgebra := by
  refine constructorsIso _ _ (Iso.refl _) ?_ ?_
  · simp only [mappedList,Iso.refl_hom,Category.comp_id]
    rfl
  · simp only [mappedList,Iso.refl_inv,Iso.refl_hom,prod.map_id_id,
      Category.id_comp,Category.comp_id]
    rfl

theorem baseListIso_hom : (baseListIso P V).hom.f=𝟙 ((F).obj (L).algebra.carrier) := rfl

/-- The parameterized source-to-target list algebra comparison is derived
from terminal/product charts and both actual constructor maps. -/
def actualParametersIso (U : PredicateCategory 𝗣𝗔) :
    (mappedList (sliceFunctor (F) U) (constantFamily U V)
      (constantFamily ((F).obj U) ((F).obj V)) (coefficientComparison (F) U V ((F).obj V) (Iso.refl _))
      ((L).algebra.withParameters U)).asAlgebra ≅
        ((R).algebra.withParameters ((F).obj U)).asAlgebra :=
  mappedParametersIso (F) U V ((F).obj V) (Iso.refl _) (L).algebra ≪≫
    parametersIso (mappedList (F) V ((F).obj V) (Iso.refl _) (L).algebra) (R).algebra
      ((Endofunctor.Algebra.forget _).mapIso (baseListIso P V))
      (SyntaxOperationsTransport.listHom_nil (baseListIso P V).hom)
      (SyntaxOperationsTransport.listHom_cons (baseListIso P V).hom) ((F).obj U)

theorem actualParametersIso_hom (U : PredicateCategory 𝗣𝗔) :
    (actualParametersIso P V U).hom.f=(familyComparison (F) U (L).algebra.carrier).hom := by
  change (familyComparison (F) U (L).algebra.carrier).hom ≫
    (constantFamilyFunctor ((F).obj U)).map (baseListIso P V).hom.f = _
  rw [baseListIso_hom]
  have hi := (constantFamilyFunctor ((F).obj U)).map_id ((F).obj (L).algebra.carrier)
  exact (congrArg (fun f => (familyComparison (F) U (L).algebra.carrier).hom ≫ f) hi).trans
    (Category.comp_id _)

/-- This uses the already proved all-parameter uniform list initiality. -/
theorem actualParameterFold (U : PredicateCategory 𝗣𝗔)
    (B₀ : ListAlgebra (constantFamily U V))
    (B₁ : ListAlgebra (constantFamily ((F).obj U) ((F).obj V)))
    (i : (mappedList (sliceFunctor (F) U) (constantFamily U V)
      (constantFamily ((F).obj U) ((F).obj V)) (coefficientComparison (F) U V ((F).obj V) (Iso.refl _)) B₀).asAlgebra ≅ B₁.asAlgebra) :
    (familyComparison (F) U (L).algebra.carrier).inv ≫
      (sliceFunctor (F) U).map ((L).foldWithParameters U B₀) ≫ i.hom.f=
        (R).foldWithParameters ((F).obj U) B₁ := by
  have h := parameterFold_comparison (F) U V ((F).obj V) (Iso.refl _) (L) (R)
    (baseListIso P V) B₀ B₁ i
  rw [baseListIso_hom] at h
  have hi := (constantFamilyFunctor ((F).obj U)).map_id ((F).obj (L).algebra.carrier)
  exact h.trans ((congrArg (fun f => f ≫ (R).foldWithParameters ((F).obj U) B₁) hi).trans
    (Category.id_comp _))

theorem map_nil : (F).map (L).algebra.nil=terminalComparison (F) ≫ (R).algebra.nil := by
  change (F).map (L).algebra.nil=terminalComparison (F) ≫
    (inv (terminalComparison (F)) ≫ (F).map (L).algebra.nil)
  simp only [IsIso.hom_inv_id_assoc]

theorem map_cons : (F).map (L).algebra.cons=
    prodComparison (F) V (L).algebra.carrier ≫ (R).algebra.cons := by
  change (F).map (L).algebra.cons=prodComparison (F) V (L).algebra.carrier ≫
    (inv (prodComparison (F) V (L).algebra.carrier) ≫ (F).map (L).algebra.cons)
  simp only [IsIso.hom_inv_id_assoc]

theorem map_singleton : (F).map (L).singleton=(R).singleton := by
  let s : V ⟶ V ⨯ (L).algebra.carrier := prod.lift (𝟙 V) (terminal.from V ≫ (L).algebra.nil)
  let t : (F).obj V ⟶ (F).obj V ⨯ (R).algebra.carrier := prod.lift (𝟙 ((F).obj V)) (terminal.from ((F).obj V) ≫ (R).algebra.nil)
  have ht : (F).map (terminal.from V) ≫ terminalComparison (F)=terminal.from ((F).obj V) :=
    terminalIsTerminal.hom_ext _ _
  have hp : (F).map s ≫ prodComparison (F) V (L).algebra.carrier=t := by
    rw [map_lift]
    apply prod.hom_ext
    · exact (prod.lift_fst ((F).map (𝟙 V))
        ((F).map (terminal.from V ≫ (L).algebra.nil))).trans
        (((F).map_id V).trans
          (prod.lift_fst (𝟙 ((F).obj V))
            (terminal.from ((F).obj V) ≫ (R).algebra.nil)).symm)
    · simp only [t,prod.lift_snd]
      rw [(F).map_comp,map_nil P V,← Category.assoc,ht]
  change (F).map (s ≫ (L).algebra.cons)=t ≫ (R).algebra.cons
  rw [(F).map_comp,map_cons P V,← Category.assoc,hp]

private abbrev appendMappedAlgebra :
    ListAlgebra (constantFamily ((F).obj (L).algebra.carrier) ((F).obj V)) :=
  mappedList (sliceFunctor (F) (L).algebra.carrier)
    (constantFamily (L).algebra.carrier V)
    (constantFamily ((F).obj (L).algebra.carrier) ((F).obj V))
    (coefficientComparison (F) (L).algebra.carrier V ((F).obj V) (Iso.refl _)) (L).appendAlgebra

private theorem mappedAppend_nil :
    (appendMappedAlgebra P V).nil ≫ (familyComparison (F) (L).algebra.carrier (L).algebra.carrier).hom =
      (R).appendAlgebra.nil := by
  let H := sliceFunctor (F) (L).algebra.carrier
  let A := mappedList H (constantFamily (L).algebra.carrier V)
    (constantFamily ((F).obj (L).algebra.carrier) ((F).obj V))
    (coefficientComparison (F) (L).algebra.carrier V ((F).obj V) (Iso.refl _)) (L).appendAlgebra
  let k := familyComparison (F) (L).algebra.carrier (L).algebra.carrier
  apply Over.OverMorphism.ext
  apply prod.hom_ext
  · exact (Over.w (A.nil ≫ k.hom)).trans (Over.w (R).appendAlgebra.nil).symm
  · erw [Over.comp_left,Category.assoc]
    change ((inv (terminalComparison H)).left ≫ (F).map (L).appendAlgebra.nil.left) ≫
      k.hom.left ≫ prod.snd=prod.lift (⊤_ (Over ((F).obj (L).algebra.carrier))).hom
        (⊤_ (Over ((F).obj (L).algebra.carrier))).hom ≫ prod.snd
    rw [Category.assoc,familyComparison_snd,← (F).map_comp]
    change (inv (terminalComparison H)).left ≫ (F).map
      (prod.lift (⊤_ (Over (L).algebra.carrier)).hom (⊤_ (Over (L).algebra.carrier)).hom ≫ prod.snd)=_
    rw [prod.lift_snd,prod.lift_snd]
    exact Over.w (inv (terminalComparison H))

private theorem mappedAppend_cons :
    (appendMappedAlgebra P V).cons ≫ (familyComparison (F) (L).algebra.carrier (L).algebra.carrier).hom =
      prod.map (𝟙 (constantFamily ((F).obj (L).algebra.carrier) ((F).obj V)))
        (familyComparison (F) (L).algebra.carrier (L).algebra.carrier).hom ≫ (R).appendAlgebra.cons := by
  have h := SyntaxOperationsTransport.listHom_cons
    (actualParametersIso P V (L).algebra.carrier).hom
  rw [actualParametersIso_hom] at h
  exact h

private def mappedAppendIso :
    (appendMappedAlgebra P V).asAlgebra ≅ (R).appendAlgebra.asAlgebra :=
  constructorsIso _ _ (familyComparison (F) (L).algebra.carrier (L).algebra.carrier)
    (mappedAppend_nil P V) (mappedAppend_cons P V)

private theorem map_swap (X : PredicateCategory 𝗣𝗔) :
    (F).map (prod.lift (prod.snd : X ⨯ X ⟶ X) prod.fst) ≫ prodComparison (F) X X=
      prodComparison (F) X X ≫ prod.lift (prod.snd : (F).obj X ⨯ (F).obj X ⟶ (F).obj X) prod.fst := by
  apply prod.hom_ext
  · simp only [Category.assoc,prodComparison_fst,prodComparison_snd,prod.lift_fst,← (F).map_comp]
  · simp only [Category.assoc,prodComparison_fst,prodComparison_snd,prod.lift_snd,← (F).map_comp]

/-- Ordered concatenation follows from actual parameter-list folds. -/
theorem map_append : (F).map (L).append=
    prodComparison (F) (L).algebra.carrier (L).algebra.carrier ≫ (R).append := by
  let H := sliceFunctor (F) (L).algebra.carrier
  let k := familyComparison (F) (L).algebra.carrier (L).algebra.carrier
  have h := actualParameterFold P V (L).algebra.carrier (L).appendAlgebra (R).appendAlgebra
    (mappedAppendIso P V)
  change k.inv ≫ H.map (L).appendWithParameter ≫ k.hom=(R).appendWithParameter at h
  have hf : H.map (L).appendWithParameter ≫ k.hom=k.hom ≫ (R).appendWithParameter := by
    apply (cancel_epi k.inv).mp
    simpa only [Category.assoc,Iso.inv_hom_id_assoc] using h
  have hh := congrArg (fun f => f.left ≫ prod.snd) hf
  simp only [Over.comp_left,Category.assoc] at hh
  change (F).map (L).appendWithParameter.left ≫ (k.hom.left ≫ prod.snd)=
    k.hom.left ≫ (R).appendWithParameter.left ≫ prod.snd at hh
  rw [familyComparison_snd,← (F).map_comp] at hh
  have hv : (F).map ((L).appendWithParameter.left ≫ prod.snd)=
      prodComparison (F) (L).algebra.carrier (L).algebra.carrier ≫
        (R).appendWithParameter.left ≫ prod.snd := hh
  change (F).map (prod.lift prod.snd prod.fst ≫ ((L).appendWithParameter.left ≫ prod.snd))=
    prodComparison (F) (L).algebra.carrier (L).algebra.carrier ≫
      (prod.lift prod.snd prod.fst ≫ ((R).appendWithParameter.left ≫ prod.snd))
  rw [(F).map_comp,hv,← Category.assoc,map_swap P (L).algebra.carrier,Category.assoc]
end CategoricalEssentialIncompleteness.V46.Miller.NamedSyntaxComparison.ListTransport
