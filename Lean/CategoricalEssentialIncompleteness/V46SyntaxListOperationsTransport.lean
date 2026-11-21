/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SyntaxOperationsTransport
public import CategoricalEssentialIncompleteness.V46SyntacticListsEquivalence
public import CategoricalEssentialIncompleteness.V46CategoricalListLaws

/-!
List folds and concatenation under equivalence, parameter, and coefficient
comparisons. No code of a chosen product is identified with a literal pair.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v₁ v₂ u₁ u₂ v₃ u₃
open CategoryTheory CategoryTheory.Limits

namespace CategoricalEssentialIncompleteness.V46.SyntaxOperationsTransport
open SyntacticLists.Transport

section Constructors
variable {K : Type u₃} [Category.{v₃} K] [HasFiniteProducts K] [HasFiniteCoproducts K]
variable {A : K} {L R : ListAlgebra A}

theorem listHom_nil (f : L.asAlgebra ⟶ R.asAlgebra) : L.nil ≫ f.f = R.nil := by
  have h := congrArg (fun k => coprod.inl ≫ k) f.h
  change coprod.inl ≫ (coprod.map (𝟙 _) (prod.map (𝟙 A) f.f) ≫
    coprod.desc R.nil R.cons) = coprod.inl ≫ (coprod.desc L.nil L.cons ≫ f.f) at h
  simpa only [← Category.assoc,coprod.inl_map,Category.id_comp,coprod.inl_desc] using h.symm

theorem listHom_cons (f : L.asAlgebra ⟶ R.asAlgebra) :
    L.cons ≫ f.f = prod.map (𝟙 A) f.f ≫ R.cons := by
  have h := congrArg (fun k => coprod.inr ≫ k) f.h
  change coprod.inr ≫ (coprod.map (𝟙 _) (prod.map (𝟙 A) f.f) ≫
    coprod.desc R.nil R.cons) = coprod.inr ≫ (coprod.desc L.nil L.cons ≫ f.f) at h
  rw [← Category.assoc,coprod.inr_map,Category.assoc,coprod.inr_desc,
    ← Category.assoc,coprod.inr_desc] at h
  exact h.symm
end Constructors

section Transport
variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
variable [Regular C] [FinitaryExtensive C] [Regular D] [FinitaryExtensive D]
variable (E : C ≌ D) {P : C} {Q : D} (b : E.functor.obj P ≅ Q)
variable (V : C) (W : D) (e : E.functor.obj V ≅ W) (L : StableListAlgebra V)

/-- This compares complete list algebras. The carrier comparison is the
canonical image of the family, rather than a numerical coordinate claim. -/
def listMappedParameterIso :
    AlgebraTransport.mappedAlgebra (sliceEquivalence E b)
      (polynomialIso (sliceEquivalence E b) (constantFamily P V) (constantFamily Q W)
        (coefficientComparison E b V W e)) (L.algebra.withParameters P).asAlgebra ≅
      ((mappedStableListAlgebra E V W e L).algebra.withParameters Q).asAlgebra :=
  mappedListIso (sliceEquivalence E b) (constantFamily P V) (constantFamily Q W)
    (coefficientComparison E b V W e) (L.algebra.withParameters P) ≪≫
      mappedParametersIso E b V W e L.algebra

/-- Target-algebra constructor comparisons transport the source fold. The target parameter
may be related to the source by any isomorphism, including a counit; no inverse object
is collapsed. -/
theorem listParameterFold_comparison
    (B₀ : ListAlgebra (constantFamily P V)) (B₁ : ListAlgebra (constantFamily Q W))
    (i : (mappedListAlgebra (sliceEquivalence E b) (constantFamily P V)
      (constantFamily Q W) (coefficientComparison E b V W e) B₀).asAlgebra ≅ B₁.asAlgebra) :
    (familyComparison E b L.algebra.carrier).inv ≫
      (sliceEquivalence E b).functor.map (L.foldWithParameters P B₀) ≫ i.hom.f =
        (mappedStableListAlgebra E V W e L).foldWithParameters Q B₁ := by
  let H := sliceEquivalence E b
  let α := polynomialIso H (constantFamily P V) (constantFamily Q W)
    (coefficientComparison E b V W e)
  let a := listMappedParameterIso E b V W e L
  let z := mappedListIso H (constantFamily P V) (constantFamily Q W)
    (coefficientComparison E b V W e) B₀ ≪≫ i
  let h : ((mappedStableListAlgebra E V W e L).algebra.withParameters Q).asAlgebra ⟶
      B₁.asAlgebra :=
    a.inv ≫ (AlgebraTransport.functor H α).map ((L.stable P).to B₀.asAlgebra) ≫ z.hom
  let he := (mappedStableListAlgebra E V W e L).stable Q
  have hh := congrArg Endofunctor.Algebra.Hom.f (he.hom_ext h (he.to B₁.asAlgebra))
  have ha : a.inv.f = (familyComparison E b L.algebra.carrier).inv := by
    change (familyComparison E b L.algebra.carrier).inv ≫ 𝟙 _ = _
    exact Category.comp_id _
  have hz : z.hom.f = i.hom.f := by
    change (𝟙 _) ≫ i.hom.f = _
    exact Category.id_comp _
  change a.inv.f ≫ H.functor.map ((L.stable P).to B₀.asAlgebra).f ≫ z.hom.f =
    (he.to B₁.asAlgebra).f at hh
  rw [ha,hz] at hh
  simpa only [StableListAlgebra.foldWithParameters,ListAlgebra.fold,H,he] using hh

private def mappedAppendAlgebraIso :
    (mappedListAlgebra (sliceEquivalence E (Iso.refl (E.functor.obj L.algebra.carrier)))
      (constantFamily L.algebra.carrier V) (constantFamily (E.functor.obj L.algebra.carrier) W)
      (coefficientComparison E (Iso.refl _) V W e) L.appendAlgebra).asAlgebra ≅
      (mappedStableListAlgebra E V W e L).appendAlgebra.asAlgebra := by
  let b : E.functor.obj L.algebra.carrier ≅ E.functor.obj L.algebra.carrier := Iso.refl _
  let H := sliceEquivalence E b
  let A := mappedListAlgebra H (constantFamily L.algebra.carrier V)
    (constantFamily (E.functor.obj L.algebra.carrier) W) (coefficientComparison E b V W e) L.appendAlgebra
  let R := mappedStableListAlgebra E V W e L
  let k := familyComparison E b L.algebra.carrier
  refine constructorsIso A R.appendAlgebra k ?_ ?_
  · apply Over.OverMorphism.ext
    apply prod.hom_ext
    · exact (Over.w (A.nil ≫ k.hom)).trans (Over.w R.appendAlgebra.nil).symm
    · erw [Over.comp_left,Category.assoc]
      change ((inv (terminalComparison H.functor)).left ≫
        E.functor.map L.appendAlgebra.nil.left) ≫ k.hom.left ≫ prod.snd =
          prod.lift (⊤_ (Over (E.functor.obj L.algebra.carrier))).hom
            (⊤_ (Over (E.functor.obj L.algebra.carrier))).hom ≫ prod.snd
      rw [Category.assoc,familyComparison_snd,← E.functor.map_comp]
      change (inv (terminalComparison H.functor)).left ≫
        E.functor.map (prod.lift (⊤_ (Over L.algebra.carrier)).hom
          (⊤_ (Over L.algebra.carrier)).hom ≫ prod.snd) = _
      rw [prod.lift_snd,prod.lift_snd]
      have h := Over.w (inv (terminalComparison H.functor))
      change (inv (terminalComparison H.functor)).left ≫
        (E.functor.map (⊤_ (Over L.algebra.carrier)).hom ≫ 𝟙 _) =
          (⊤_ (Over (E.functor.obj L.algebra.carrier))).hom at h
      simpa only [Category.comp_id] using h
  · have h := listHom_cons (mappedParametersIso E b V W e L.algebra).hom
    have hk : (mappedParametersIso E b V W e L.algebra).hom.f = k.hom := rfl
    rw [hk] at h
    exact h

omit [FinitaryExtensive C] [FinitaryExtensive D] in
/-- A canonical product comparison respects the swapping map. -/
theorem list_map_swap (X : C) :
    E.functor.map (prod.lift (prod.snd : X ⨯ X ⟶ X) prod.fst) ≫
      prodComparison E.functor X X =
    prodComparison E.functor X X ≫
      prod.lift (prod.snd : E.functor.obj X ⨯ E.functor.obj X ⟶ E.functor.obj X) prod.fst := by
  apply prod.hom_ext
  · simp only [Category.assoc,prodComparison_fst,prodComparison_snd,
      prod.lift_fst,← E.functor.map_comp]
  · simp only [Category.assoc,prodComparison_fst,prodComparison_snd,
      prod.lift_snd,← E.functor.map_comp]

/-- Concatenation is transported in manuscript order. Its parameter is the second list,
and that swap is included explicitly. -/
theorem map_list_append :
    E.functor.map L.append = prodComparison E.functor L.algebra.carrier L.algebra.carrier ≫
      (mappedStableListAlgebra E V W e L).append := by
  let R := mappedStableListAlgebra E V W e L
  let b : E.functor.obj L.algebra.carrier ≅ E.functor.obj L.algebra.carrier := Iso.refl _
  let H := sliceEquivalence E b
  let k := familyComparison E b L.algebra.carrier
  have h := listParameterFold_comparison E b V W e L L.appendAlgebra R.appendAlgebra
    (mappedAppendAlgebraIso E V W e L)
  change k.inv ≫ H.functor.map L.appendWithParameter ≫ k.hom = R.appendWithParameter at h
  have hf : H.functor.map L.appendWithParameter ≫ k.hom = k.hom ≫ R.appendWithParameter := by
    apply (cancel_epi k.inv).mp
    simpa only [Category.assoc,Iso.inv_hom_id_assoc] using h
  have hh := congrArg (fun f => f.left ≫ prod.snd) hf
  erw [Over.comp_left,Over.comp_left] at hh
  simp only [Category.assoc] at hh
  change E.functor.map L.appendWithParameter.left ≫ (k.hom.left ≫ prod.snd) =
    k.hom.left ≫ R.appendWithParameter.left ≫ prod.snd at hh
  rw [familyComparison_snd,← E.functor.map_comp] at hh
  have hv : E.functor.map (L.appendWithParameter.left ≫ prod.snd) =
      prodComparison E.functor L.algebra.carrier L.algebra.carrier ≫
        R.appendWithParameter.left ≫ prod.snd := by
    simpa [k,b,familyComparison,Category.assoc] using hh
  change E.functor.map (prod.lift prod.snd prod.fst ≫
      (L.appendWithParameter.left ≫ prod.snd)) =
    prodComparison E.functor L.algebra.carrier L.algebra.carrier ≫
      (prod.lift prod.snd prod.fst ≫ (R.appendWithParameter.left ≫ prod.snd))
  rw [E.functor.map_comp,hv,← Category.assoc,list_map_swap E L.algebra.carrier,Category.assoc]

end Transport
end CategoricalEssentialIncompleteness.V46.SyntaxOperationsTransport
