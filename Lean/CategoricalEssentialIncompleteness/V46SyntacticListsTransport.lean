/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46AlgebraTransport
public import CategoricalEssentialIncompleteness.V46CategoricalLists
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts

/-! # List-polynomial comparison across equivalences -/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v₁ v₂ u₁ u₂
open CategoryTheory CategoryTheory.Limits

namespace CategoricalEssentialIncompleteness.V46.SyntacticLists
namespace Transport
variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
variable [HasFiniteProducts C] [HasFiniteCoproducts C]
variable [HasFiniteProducts D] [HasFiniteCoproducts D]

/-- An isomorphism commuting with both constructors is an isomorphism
of the corresponding complete list algebras. -/
def constructorsIso {V₀ : D} (L R : ListAlgebra V₀) (i : L.carrier ≅ R.carrier)
    (hn : L.nil ≫ i.hom = R.nil)
    (hc : L.cons ≫ i.hom = prod.map (𝟙 V₀) i.hom ≫ R.cons) :
    L.asAlgebra ≅ R.asAlgebra := by
  refine Endofunctor.Algebra.isoMk i ?_
  change coprod.map (𝟙 (⊤_ D)) (prod.map (𝟙 V₀) i.hom) ≫
    coprod.desc R.nil R.cons = coprod.desc L.nil L.cons ≫ i.hom
  apply coprod.hom_ext
  · simp only [← Category.assoc, coprod.inl_map, Category.id_comp, coprod.inl_desc]
    exact hn.symm
  · simp only [← Category.assoc, coprod.inr_map, coprod.inr_desc]
    rw [Category.assoc, coprod.inr_desc]
    exact hc.symm

variable (E : C ≌ D) (V : C) (W : D) (e : E.functor.obj V ≅ W)

/-- Every component uses only the canonical preserved terminal, product,
and coproduct comparisons, together with the given coefficient isomorphism. -/
def polynomialComponent (X : C) :
    E.functor.obj ((⊤_ C) ⨿ (V ⨯ X)) ≅ (⊤_ D) ⨿ (W ⨯ E.functor.obj X) :=
  (asIso (coprodComparison E.functor (⊤_ C) (V ⨯ X))).symm ≪≫
    coprod.mapIso (asIso (terminalComparison E.functor))
      ((asIso (prodComparison E.functor V X)) ≪≫ prod.mapIso e (Iso.refl _))

@[reassoc] theorem polynomialComponent_inl (X : C) :
    E.functor.map (coprod.inl : ⊤_ C ⟶ (⊤_ C) ⨿ (V ⨯ X)) ≫
      (polynomialComponent E V W e X).hom =
        terminalComparison E.functor ≫ coprod.inl := by
  change E.functor.map coprod.inl ≫
    (inv (coprodComparison E.functor (⊤_ C) (V ⨯ X)) ≫
      coprod.map (terminalComparison E.functor)
        (prodComparison E.functor V X ≫ prod.map e.hom (𝟙 _))) = _
  rw [← Category.assoc, map_inl_inv_coprodComparison, coprod.inl_map]

@[reassoc] theorem polynomialComponent_inr (X : C) :
    E.functor.map (coprod.inr : V ⨯ X ⟶ (⊤_ C) ⨿ (V ⨯ X)) ≫
      (polynomialComponent E V W e X).hom =
        prodComparison E.functor V X ≫ prod.map e.hom (𝟙 _) ≫ coprod.inr := by
  change E.functor.map coprod.inr ≫
    (inv (coprodComparison E.functor (⊤_ C) (V ⨯ X)) ≫
      coprod.map (terminalComparison E.functor)
        (prodComparison E.functor V X ≫ prod.map e.hom (𝟙 _))) = _
  rw [← Category.assoc, map_inr_inv_coprodComparison, coprod.inr_map, Category.assoc]

/-- The actual natural comparison of the two list endofunctors. -/
def polynomialIso : listFunctor V ⋙ E.functor ≅ E.functor ⋙ listFunctor W := by
  refine NatIso.ofComponents (polynomialComponent E V W e) ?_
  intro X Y f
  change E.functor.map (coprod.map (𝟙 (⊤_ C)) (prod.map (𝟙 V) f)) ≫
    (polynomialComponent E V W e Y).hom =
      (polynomialComponent E V W e X).hom ≫
        coprod.map (𝟙 (⊤_ D)) (prod.map (𝟙 W) (E.functor.map f))
  apply (cancel_epi (coprodComparison E.functor (⊤_ C) (V ⨯ X))).mp
  apply coprod.hom_ext
  · simp only [← Category.assoc, coprodComparison_inl]
    rw [← E.functor.map_comp, coprod.inl_map, Category.id_comp,
      polynomialComponent_inl E V W e Y, polynomialComponent_inl E V W e X]
    simp only [Category.assoc, coprod.inl_map, Category.id_comp]
  · simp only [← Category.assoc, coprodComparison_inr]
    rw [← E.functor.map_comp, coprod.inr_map,
      E.functor.map_comp, Category.assoc, polynomialComponent_inr]
    rw [← Category.assoc, prodComparison_natural, polynomialComponent_inr]
    simp only [E.functor.map_id, Category.assoc, coprod.inr_map,
      prod.map_map_assoc, Category.id_comp, Category.comp_id]

/-- The transported list algebra uses the actual image of its two
constructors and the canonical comparison isomorphisms. -/
def mappedListAlgebra (L : ListAlgebra V) : ListAlgebra W where
  carrier := E.functor.obj L.carrier
  nil := inv (terminalComparison E.functor) ≫ E.functor.map L.nil
  cons := prod.map e.inv (𝟙 _) ≫ inv (prodComparison E.functor V L.carrier) ≫
    E.functor.map L.cons

theorem mappedList_structure (L : ListAlgebra V) :
    (polynomialIso E V W e).hom.app L.carrier ≫
      (mappedListAlgebra E V W e L).asAlgebra.str = E.functor.map L.asAlgebra.str := by
  change (polynomialComponent E V W e L.carrier).hom ≫
    coprod.desc (inv (terminalComparison E.functor) ≫ E.functor.map L.nil)
      (prod.map e.inv (𝟙 _) ≫ inv (prodComparison E.functor V L.carrier) ≫
        E.functor.map L.cons) = E.functor.map (coprod.desc L.nil L.cons)
  apply (cancel_epi (coprodComparison E.functor (⊤_ C) (V ⨯ L.carrier))).mp
  apply coprod.hom_ext
  · simp only [← Category.assoc, coprodComparison_inl]
    rw [Category.assoc, polynomialComponent_inl_assoc]
    simp only [Category.assoc, coprod.inl_desc]
    simp only [← Category.assoc, IsIso.hom_inv_id, Category.id_comp,
      ← E.functor.map_comp, coprod.inl_desc]
  · simp only [← Category.assoc, coprodComparison_inr]
    rw [Category.assoc, polynomialComponent_inr_assoc]
    simp only [Category.assoc, coprod.inr_desc,
      prod.map_map_assoc, e.hom_inv_id, Category.comp_id,
      prod.map_id_id, IsIso.hom_inv_id_assoc,
      Category.id_comp, ← E.functor.map_comp]

/-- The constructor presentation agrees with the complete algebra
transport, via an identity map on its actual carrier. -/
def mappedListIso (L : ListAlgebra V) :
    AlgebraTransport.mappedAlgebra E (polynomialIso E V W e) L.asAlgebra ≅
      (mappedListAlgebra E V W e L).asAlgebra := by
  refine Endofunctor.Algebra.isoMk (Iso.refl _) ?_
  change (listFunctor W).map (𝟙 _) ≫ (mappedListAlgebra E V W e L).asAlgebra.str =
    ((polynomialIso E V W e).inv.app L.carrier ≫ E.functor.map L.asAlgebra.str) ≫ 𝟙 _
  rw [(listFunctor W).map_id, Category.id_comp, Category.comp_id]
  apply (cancel_epi ((polynomialIso E V W e).hom.app L.carrier)).mp
  rw [← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]
  exact mappedList_structure E V W e L

def mappedListInitial (L : ListAlgebra V) (hL : IsInitial L.asAlgebra) :
    IsInitial (mappedListAlgebra E V W e L).asAlgebra :=
  (AlgebraTransport.initial E (polynomialIso E V W e) L.asAlgebra hL).ofIso
    (mappedListIso E V W e L)

section TerminalSlice
variable [HasFiniteLimits C]

/-- Forgetting the parameter over the terminal object is the canonical
slice equivalence, with no choice of an arithmetic presentation. -/
def terminalSliceEquivalence : Over (⊤_ C) ≌ C :=
  Over.equivalenceOfIsTerminal (Limits.terminalIsTerminal (C := C))

/-- The transported parameter constructors agree with the original
constructors under the canonical left unitor on the carrier. -/
def terminalMappedIso {V : C} (L : ListAlgebra V) :
    (mappedListAlgebra (terminalSliceEquivalence (C := C)) (constantFamily (⊤_ C) V) V
      (prod.leftUnitor V) (L.withParameters (⊤_ C))).asAlgebra ≅ L.asAlgebra := by
  let E := terminalSliceEquivalence (C := C)
  let P := ⊤_ C
  let S := L.withParameters P
  have hn : inv (terminalComparison E.functor) ≫ S.nil.left ≫
      (prod.leftUnitor L.carrier).hom = L.nil := by
    change inv (terminalComparison E.functor) ≫
      prod.lift (⊤_ (Over P)).hom
        (terminal.from (⊤_ (Over P)).left ≫ L.nil) ≫ prod.snd = L.nil
    rw [prod.lift_snd, ← Category.assoc]
    have ht : terminal.from (⊤_ (Over P)).left = terminalComparison E.functor :=
      (Limits.terminalIsTerminal (C := C)).hom_ext _ _
    rw [ht, IsIso.inv_hom_id, Category.id_comp]
  have hc : (prod.map (prod.leftUnitor V).inv (𝟙 _) ≫
      inv (prodComparison E.functor (constantFamily P V) S.carrier) ≫
        S.cons.left) ≫ (prod.leftUnitor L.carrier).hom =
      prod.map (𝟙 V) (prod.leftUnitor L.carrier).hom ≫ L.cons := by
    let r : (constantFamily P V ⨯ constantFamily P L.carrier).left ⟶ V ⨯ L.carrier :=
      prod.lift
        ((prod.fst : constantFamily P V ⨯ constantFamily P L.carrier ⟶
          constantFamily P V).left ≫ prod.snd)
        ((prod.snd : constantFamily P V ⨯ constantFamily P L.carrier ⟶
          constantFamily P L.carrier).left ≫ prod.snd)
    change (prod.map (prod.leftUnitor V).inv (𝟙 _) ≫
      inv (prodComparison E.functor (constantFamily P V) S.carrier) ≫
        prod.lift (constantFamily P V ⨯ constantFamily P L.carrier).hom
          (r ≫ L.cons)) ≫ prod.snd = _
    simp only [Category.assoc, prod.lift_snd]
    have hr : prod.map (prod.leftUnitor V).inv (𝟙 _) ≫
        inv (prodComparison E.functor (constantFamily P V) S.carrier) ≫ r =
          prod.map (𝟙 V) (prod.leftUnitor L.carrier).hom := by
      apply prod.hom_ext
      · simp only [r, Category.assoc, prod.lift_fst, prod.map_fst]
        change prod.map (prod.leftUnitor V).inv (𝟙 _) ≫
          inv (prodComparison E.functor (constantFamily P V) S.carrier) ≫
            E.functor.map (prod.fst : constantFamily P V ⨯ S.carrier ⟶
              constantFamily P V) ≫ prod.snd = _
        rw [inv_prodComparison_map_fst_assoc]
        simp only [prod.leftUnitor_inv, Category.comp_id]
        rw [← Category.assoc, prod.map_fst, Category.assoc, prod.lift_snd,
          Category.comp_id]
        rfl
      · simp only [r, Category.assoc, prod.lift_snd, prod.map_snd]
        change prod.map (prod.leftUnitor V).inv (𝟙 _) ≫
          inv (prodComparison E.functor (constantFamily P V) S.carrier) ≫
            E.functor.map (prod.snd : constantFamily P V ⨯ S.carrier ⟶
              S.carrier) ≫ prod.snd = _
        rw [inv_prodComparison_map_snd_assoc]
        simp only [prod.leftUnitor_inv, prod.leftUnitor_hom]
        erw [prod.map_snd_assoc, Category.id_comp]
        rfl
    simpa only [Category.assoc] using congrArg (fun f => f ≫ L.cons) hr
  exact constructorsIso
    (mappedListAlgebra E (constantFamily P V) V (prod.leftUnitor V) S) L
    (prod.leftUnitor L.carrier)
    (by
      change (inv (terminalComparison E.functor) ≫ S.nil.left) ≫
        (prod.leftUnitor L.carrier).hom = L.nil
      rw [Category.assoc]
      exact hn) hc

/-- Actual initiality in the terminal parameter slice implies actual
base initiality; this does not assume the desired base universal property. -/
def initialOfTerminalParameters {V : C} (L : ListAlgebra V)
    (hL : IsInitial (L.withParameters (⊤_ C)).asAlgebra) : IsInitial L.asAlgebra :=
  (mappedListInitial (terminalSliceEquivalence (C := C)) (constantFamily (⊤_ C) V) V
    (prod.leftUnitor V) (L.withParameters (⊤_ C)) hL).ofIso (terminalMappedIso L)

end TerminalSlice

end Transport
end CategoricalEssentialIncompleteness.V46.SyntacticLists
