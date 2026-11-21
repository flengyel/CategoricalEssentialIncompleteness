/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SyntaxListOperationsTransportCoordinates
public import CategoricalEssentialIncompleteness.V46SyntaxListOperationsTransportAlgebras

/-!
Membership is transported by its parameter algebra and its proved Boolean constructor
diagrams, rather than by an assumed fold law.
-/

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
theorem membershipOverMap_left {P : C} {Q : D} (b : E.functor.obj P ≅ Q)
    {A B : Over P} (f : A ⟶ B) :
    ((sliceEquivalence E b).functor.map f).left = E.functor.map f.left := rfl

variable (V : C) (W : D) (e : E.functor.obj V ≅ W)
variable (S : DecidableVariables V) (T : DecidableVariables W)

/-- The coefficient and carrier isomorphisms are family comparisons. The equality-test
square is derived from the diagonal. -/
def mappedMembershipAlgebraIso :
    (mappedListAlgebra (sliceEquivalence E e) (constantFamily V V) (constantFamily W W)
      (coefficientComparison E e V W e) (StableListAlgebra.membershipAlgebra S)).asAlgebra ≅
      (StableListAlgebra.membershipAlgebra T).asAlgebra := by
  let H := sliceEquivalence E e
  let A := StableListAlgebra.membershipAlgebra S
  let B := StableListAlgebra.membershipAlgebra T
  let i := coefficientComparison E e (Two C) (Two D) (booleanIso E)
  let j := listStepComparison E e V (Two C) W (Two D) e (booleanIso E)
  refine mappedListConstructorsIso H (constantFamily V V) (constantFamily W W)
    (coefficientComparison E e V W e) A B i ?_ ?_
  · apply Over.OverMorphism.ext
    apply prod.hom_ext
    · exact (Over.w (H.functor.map A.nil ≫ i.hom)).trans
        (Over.w (terminalComparison H.functor ≫ B.nil)).symm
    · have h₀ : A.nil.left ≫ prod.snd = Two.constant (⊤_ (Over V)).left false :=
        prod.lift_snd _ _
      have h₁ : B.nil.left ≫ prod.snd = Two.constant (⊤_ (Over W)).left false :=
        prod.lift_snd _ _
      dsimp only [H]
      simp only [Over.comp_left,membershipOverMap_left,Category.assoc]
      rw [coefficientComparison_snd,← Category.assoc,← E.functor.map_comp,h₀,h₁,
        map_constant E (⊤_ (Over V)).left false,Two.comp_constant]
      rfl
  · dsimp only [H,A,i]
    rw [← Category.assoc]
    change H.functor.map A.cons ≫ i.hom = j.hom ≫ B.cons
    apply Over.OverMorphism.ext
    apply prod.hom_ext
    · exact (Over.w (H.functor.map A.cons ≫ i.hom)).trans (Over.w (j.hom ≫ B.cons)).symm
    · let U := constantFamily V V ⨯ constantFamily V (Two C)
      let Z := constantFamily W W ⨯ constantFamily W (Two D)
      let χ := prod.lift U.hom (listStepHead V V (Two C)) ≫ S.test
      let χ' := prod.lift Z.hom (listStepHead W W (Two D)) ≫ T.test
      have h₀ : A.cons.left ≫ prod.snd =
          Two.binary Bool.or χ (listStepValue V V (Two C)) := prod.lift_snd _ _
      have h₁ : B.cons.left ≫ prod.snd =
          Two.binary Bool.or χ' (listStepValue W W (Two D)) := prod.lift_snd _ _
      have heq := listStepComparison_test E V W e (booleanIso E) S T
      have hval := listStepComparison_value E e V (Two C) W (Two D) e (booleanIso E)
      dsimp only [H]
      simp only [Over.comp_left,membershipOverMap_left,Category.assoc]
      rw [coefficientComparison_snd,← Category.assoc,← E.functor.map_comp,h₀,h₁,
        map_boolean_binary E Bool.or,Two.comp_binary]
      rw [heq,hval]

variable (L : StableListAlgebra V)

/-- Membership in the transported list is the image of source membership, under the real
variable, product and Boolean comparisons. -/
theorem map_list_membership :
    E.functor.map (L.membership S) ≫ (booleanIso E).hom =
      prodComparison E.functor V L.algebra.carrier ≫ prod.map e.hom (𝟙 _) ≫
        (mappedStableListAlgebra E V W e L).membership T := by
  let R := mappedStableListAlgebra E V W e L
  let H := sliceEquivalence E e
  let a := familyComparison E e L.algebra.carrier
  let i := coefficientComparison E e (Two C) (Two D) (booleanIso E)
  have h := listParameterFold_comparison E e V W e L
    (StableListAlgebra.membershipAlgebra S) (StableListAlgebra.membershipAlgebra T)
    (mappedMembershipAlgebraIso E V W e S T)
  change a.inv ≫ H.functor.map (L.membershipFold S) ≫ i.hom = R.membershipFold T at h
  have hf : H.functor.map (L.membershipFold S) ≫ i.hom = a.hom ≫ R.membershipFold T := by
    apply (cancel_epi a.inv).mp
    simpa only [Category.assoc,Iso.inv_hom_id_assoc] using h
  have hh := congrArg (fun f => f.left ≫ prod.snd) hf
  dsimp only [H] at hh
  simp only [Over.comp_left,membershipOverMap_left,Category.assoc] at hh
  rw [coefficientComparison_snd,← Category.assoc,← E.functor.map_comp] at hh
  change E.functor.map (L.membership S) ≫ (booleanIso E).hom =
    a.hom.left ≫ R.membership T at hh
  simpa [a,familyComparison,Category.assoc] using hh

end CategoricalEssentialIncompleteness.V46.SyntaxOperationsTransport
