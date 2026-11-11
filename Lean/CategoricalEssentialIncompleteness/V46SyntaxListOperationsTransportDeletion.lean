/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SyntaxListOperationsTransportCoordinates
public import CategoricalEssentialIncompleteness.V46SyntaxListOperationsTransportAlgebras

/-! Deletion transport is derived from the actual parameterized
initial algebra, the equality classifier and the nil/cons diagrams. -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v₁ v₂ u₁ u₂
open CategoryTheory CategoryTheory.Limits

namespace CategoricalEssentialIncompleteness.V46.SyntaxOperationsTransport
open SyntacticLists.Transport DecidableVariables.Transport
variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
variable [Regular C] [FinitaryExtensive C] [Regular D] [FinitaryExtensive D]
variable (E : C ≌ D)

omit [Regular C] [FinitaryExtensive C] [Regular D] [FinitaryExtensive D] in
theorem deletionOverMap_left {P : C} {Q : D} (b : E.functor.obj P ≅ Q)
    {A B : Over P} (f : A ⟶ B) :
    ((sliceEquivalence E b).functor.map f).left = E.functor.map f.left := rfl

variable (V : C) (W : D) (e : E.functor.obj V ≅ W)
variable (L : StableListAlgebra V) (S : DecidableVariables V) (T : DecidableVariables W)

/-- This is an isomorphism of complete list algebras. Its cons equation
uses the proved transport of the actual equality-classified branch. -/
def mappedDeletionAlgebraIso :
    (mappedListAlgebra (sliceEquivalence E e) (constantFamily V V) (constantFamily W W)
      (coefficientComparison E e V W e) (L.deletionAlgebra S)).asAlgebra ≅
      ((mappedStableListAlgebra E V W e L).deletionAlgebra T).asAlgebra := by
  let R := mappedStableListAlgebra E V W e L
  let H := sliceEquivalence E e
  let A := L.deletionAlgebra S
  let B := R.deletionAlgebra T
  let i := coefficientComparison E e L.algebra.carrier (E.functor.obj L.algebra.carrier) (Iso.refl _)
  let j := listStepComparison E e V L.algebra.carrier W (E.functor.obj L.algebra.carrier)
    e (Iso.refl _)
  refine mappedListConstructorsIso H (constantFamily V V) (constantFamily W W)
    (coefficientComparison E e V W e) A B i ?_ ?_
  · apply Over.OverMorphism.ext
    apply prod.hom_ext
    · exact (Over.w (H.functor.map A.nil ≫ i.hom)).trans
        (Over.w (terminalComparison H.functor ≫ B.nil)).symm
    · have h₀ : A.nil.left ≫ prod.snd =
          terminal.from (⊤_ (Over V)).left ≫ L.algebra.nil := prod.lift_snd _ _
      have h₁ : B.nil.left ≫ prod.snd =
          terminal.from (⊤_ (Over W)).left ≫ R.algebra.nil := prod.lift_snd _ _
      have ht : E.functor.map (terminal.from (⊤_ (Over V)).left) ≫
          terminalComparison E.functor = terminal.from (E.functor.obj (⊤_ (Over V)).left) :=
        terminalIsTerminal.hom_ext _ _
      dsimp only [H]
      simp only [Over.comp_left,deletionOverMap_left,Category.assoc]
      erw [coefficientComparison_snd]
      simp only [Iso.refl_hom,Category.comp_id]
      erw [← E.functor.map_comp,h₀,h₁,E.functor.map_comp,
        map_list_nil E V W e L,← Category.assoc,ht]
      change terminal.from (E.functor.obj (⊤_ (Over V)).left) ≫ R.algebra.nil =
        (terminalComparison H.functor).left ≫
          (terminal.from (⊤_ (Over W)).left ≫ R.algebra.nil)
      have hterm : (terminalComparison H.functor).left ≫ terminal.from (⊤_ (Over W)).left =
          terminal.from (E.functor.obj (⊤_ (Over V)).left) := terminalIsTerminal.hom_ext _ _
      calc
        _ = ((terminalComparison H.functor).left ≫ terminal.from (⊤_ (Over W)).left) ≫
            R.algebra.nil := congrArg (fun f => f ≫ R.algebra.nil) hterm.symm
        _ = _ := Category.assoc _ _ _
  · rw [← Category.assoc]
    change H.functor.map A.cons ≫ i.hom = j.hom ≫ B.cons
    apply Over.OverMorphism.ext
    apply prod.hom_ext
    · exact (Over.w (H.functor.map A.cons ≫ i.hom)).trans (Over.w (j.hom ≫ B.cons)).symm
    · let U := constantFamily V V ⨯ constantFamily V L.algebra.carrier
      let Z := constantFamily W W ⨯ constantFamily W R.algebra.carrier
      let χ := prod.lift U.hom (listStepHead V V L.algebra.carrier) ≫ S.test
      let χ' := prod.lift Z.hom (listStepHead W W R.algebra.carrier) ≫ T.test
      let k := prod.lift (listStepHead V V L.algebra.carrier)
        (listStepValue V V L.algebra.carrier) ≫ L.algebra.cons
      let k' := prod.lift (listStepHead W W R.algebra.carrier)
        (listStepValue W W R.algebra.carrier) ≫ R.algebra.cons
      have h₀ : A.cons.left ≫ prod.snd =
          Two.branch χ k (listStepValue V V L.algebra.carrier) := prod.lift_snd _ _
      have h₁ : B.cons.left ≫ prod.snd =
          Two.branch χ' k' (listStepValue W W R.algebra.carrier) := prod.lift_snd _ _
      have heq : j.hom.left ≫ χ' = E.functor.map χ ≫ (booleanIso E).hom :=
        listStepComparison_test E V W e (Iso.refl _) S T
      have hval : j.hom.left ≫ listStepValue W W R.algebra.carrier =
          E.functor.map (listStepValue V V L.algebra.carrier) := by
        change j.hom.left ≫ listStepValue W W (E.functor.obj L.algebra.carrier) = _
        simpa only [Iso.refl_hom,Category.comp_id] using
          listStepComparison_value E e V L.algebra.carrier W (E.functor.obj L.algebra.carrier)
            e (Iso.refl _)
      have hpre : j.hom.left ≫ k' = E.functor.map k := by
        change j.hom.left ≫ (prod.lift (listStepHead W W R.algebra.carrier)
          (listStepValue W W R.algebra.carrier) ≫ R.algebra.cons) =
            E.functor.map (prod.lift (listStepHead V V L.algebra.carrier)
              (listStepValue V V L.algebra.carrier) ≫ L.algebra.cons)
        rw [E.functor.map_comp,map_list_cons E V W e L]
        erw [← Category.assoc,prod.comp_lift,
          listStepComparison_head E e V L.algebra.carrier W R.algebra.carrier e (Iso.refl _),hval]
        rw [← Category.assoc,list_map_lift,← Category.assoc,prod.lift_map]
        simp only [Category.comp_id]
        rfl
      dsimp only [H]
      simp only [Over.comp_left,deletionOverMap_left,Category.assoc]
      erw [coefficientComparison_snd]
      simp only [Iso.refl_hom,Category.comp_id]
      erw [← E.functor.map_comp,h₀,h₁,map_branch E,branch_precomp,heq,hpre,hval]

/-- No identity of chosen list codes is used. The output carrier of the
transported list is literally the image of the source carrier. -/
theorem map_list_deletion :
    E.functor.map (L.deletion S) =
      prodComparison E.functor V L.algebra.carrier ≫ prod.map e.hom (𝟙 _) ≫
        (mappedStableListAlgebra E V W e L).deletion T := by
  let R := mappedStableListAlgebra E V W e L
  let H := sliceEquivalence E e
  let a := familyComparison E e L.algebra.carrier
  let i := coefficientComparison E e L.algebra.carrier (E.functor.obj L.algebra.carrier) (Iso.refl _)
  have h := listParameterFold_comparison E e V W e L (L.deletionAlgebra S)
    (R.deletionAlgebra T) (mappedDeletionAlgebraIso E V W e L S T)
  change a.inv ≫ H.functor.map (L.deletionFold S) ≫ i.hom = R.deletionFold T at h
  have hf : H.functor.map (L.deletionFold S) ≫ i.hom = a.hom ≫ R.deletionFold T := by
    apply (cancel_epi a.inv).mp
    simpa only [Category.assoc,Iso.inv_hom_id_assoc] using h
  have hh := congrArg (fun f => f.left ≫ prod.snd) hf
  dsimp only [H] at hh
  simp only [Over.comp_left,deletionOverMap_left,Category.assoc] at hh
  erw [coefficientComparison_snd] at hh
  simp only [Iso.refl_hom,Category.comp_id] at hh
  erw [← E.functor.map_comp] at hh
  change E.functor.map (L.deletion S) = a.hom.left ≫ R.deletion T at hh
  simpa [a,familyComparison,Category.assoc] using hh

end CategoricalEssentialIncompleteness.V46.SyntaxOperationsTransport
