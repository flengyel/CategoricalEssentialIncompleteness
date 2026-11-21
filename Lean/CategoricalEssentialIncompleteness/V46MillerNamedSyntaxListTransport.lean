/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerNamedSyntaxComparisonLists
public import CategoricalEssentialIncompleteness.V46SyntaxListOperationsTransport
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Over

/-! # Parameter-list folds under the PA interpretation functor

The functor need only preserve finite geometry. Initiality of the target
list algebra is supplied by the constructed uniform list folds, rather
than inferred from preservation by the PA predicate functor.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v₁ v₂ u₁ u₂
open CategoryTheory CategoryTheory.Limits
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
namespace CategoricalEssentialIncompleteness.V46.Miller.NamedSyntaxComparison.ListTransport
open SyntacticLists.Transport

section Generic
variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
variable [HasFiniteLimits C] [HasFiniteCoproducts C]
variable [HasFiniteLimits D] [HasFiniteCoproducts D]
variable (F : C ⥤ D) [PreservesFiniteLimits F]

/-- Image constructors; no preservation of list initiality is used. -/
def mappedList (V : C) (W : D) (e : F.obj V ≅ W) (L : ListAlgebra V) : ListAlgebra W where
  carrier := F.obj L.carrier
  nil := inv (terminalComparison F) ≫ F.map L.nil
  cons := prod.map e.inv (𝟙 _) ≫ inv (prodComparison F V L.carrier) ≫ F.map L.cons

def constructorsHom {V : D} (L B : ListAlgebra V) (f : L.carrier ⟶ B.carrier)
    (hn : L.nil ≫ f=B.nil) (hc : L.cons ≫ f=prod.map (𝟙 V) f ≫ B.cons) :
    L.asAlgebra ⟶ B.asAlgebra where
  f := f
  h := by
    change coprod.map (𝟙 (⊤_ D)) (prod.map (𝟙 V) f) ≫ coprod.desc B.nil B.cons =
      coprod.desc L.nil L.cons ≫ f
    apply coprod.hom_ext
    · simp only [← Category.assoc,coprod.inl_map,Category.id_comp,coprod.inl_desc]
      exact hn.symm
    · rw [← Category.assoc,coprod.inr_map,Category.assoc,coprod.inr_desc,
        ← Category.assoc,coprod.inr_desc]
      exact hc.symm

/-- Each existing source algebra morphism is mapped by its proved
nil/cons equations, without reflection or fullness of F. -/
def mappedHom (V : C) (W : D) (e : F.obj V ≅ W) {L B : ListAlgebra V}
    (f : L.asAlgebra ⟶ B.asAlgebra) :
    (mappedList F V W e L).asAlgebra ⟶ (mappedList F V W e B).asAlgebra := by
  refine constructorsHom _ _ (F.map f.f) ?_ ?_
  · change (inv (terminalComparison F) ≫ F.map L.nil) ≫ F.map f.f =
      inv (terminalComparison F) ≫ F.map B.nil
    rw [Category.assoc,← F.map_comp,SyntaxOperationsTransport.listHom_nil f]
  · have hp : inv (prodComparison F V L.carrier) ≫ F.map (prod.map (𝟙 V) f.f) =
        prod.map (𝟙 (F.obj V)) (F.map f.f) ≫ inv (prodComparison F V B.carrier) := by
      apply (cancel_epi (prodComparison F V L.carrier)).mp
      apply (cancel_mono (prodComparison F V B.carrier)).mp
      simp only [Category.assoc,IsIso.hom_inv_id_assoc,
        IsIso.inv_hom_id,Category.comp_id]
      simpa only [F.map_id,ListAlgebra.asAlgebra] using
        prodComparison_natural F (𝟙 V) (f.f : L.carrier ⟶ B.carrier)
    calc
      (mappedList F V W e L).cons ≫ F.map f.f =
          prod.map e.inv (𝟙 _) ≫ inv (prodComparison F V L.carrier) ≫
            F.map (L.cons ≫ f.f) := by simp only [mappedList,F.map_comp,Category.assoc]
      _ = prod.map e.inv (𝟙 _) ≫ inv (prodComparison F V L.carrier) ≫
            F.map (prod.map (𝟙 V) f.f ≫ B.cons) :=
          congrArg (fun k => prod.map e.inv (𝟙 _) ≫ inv (prodComparison F V L.carrier) ≫ F.map k)
            (SyntaxOperationsTransport.listHom_cons f)
      _ = prod.map e.inv (𝟙 _) ≫
            (inv (prodComparison F V L.carrier) ≫ F.map (prod.map (𝟙 V) f.f)) ≫ F.map B.cons := by
          simp only [F.map_comp,Category.assoc]
      _ = prod.map e.inv (𝟙 _) ≫
            (prod.map (𝟙 (F.obj V)) (F.map f.f) ≫ inv (prodComparison F V B.carrier)) ≫
              F.map B.cons := by rw [hp]; rfl
      _ = prod.map (𝟙 W) (F.map f.f) ≫ (mappedList F V W e B).cons := by
          simp only [mappedList,Category.assoc,prod.map_map_assoc,Category.id_comp,Category.comp_id]
          exact congrArg (fun h => prod.map e.inv h ≫ inv (prodComparison F V B.carrier) ≫ F.map B.cons)
            (Category.comp_id (F.map f.f)).symm

/-- The postcomposition functor on parameter slices. -/
abbrev sliceFunctor (U : C) : Over U ⥤ Over (F.obj U) := Over.post F

/-- Product comparison identifies the image of a constant family. -/
def familyComparison (U X : C) :
    (sliceFunctor F U).obj (constantFamily U X) ≅ constantFamily (F.obj U) (F.obj X) :=
  Over.isoMk (asIso (prodComparison F U X)) (by
    change prodComparison F U X ≫ prod.fst=F.map prod.fst
    exact prodComparison_fst F U X)

omit [HasFiniteCoproducts C] [HasFiniteCoproducts D] in
theorem familyComparison_snd (U X : C) :
    (familyComparison F U X).hom.left ≫ prod.snd=F.map (prod.snd : U ⨯ X ⟶ X) :=
  prodComparison_snd F U X

omit [HasFiniteCoproducts C] [HasFiniteCoproducts D] in
theorem familyComparison_inv_snd (U X : C) :
    (familyComparison F U X).inv.left ≫ F.map (prod.snd : U ⨯ X ⟶ X)=prod.snd := by
  change inv (prodComparison F U X) ≫ F.map prod.snd=prod.snd
  exact inv_prodComparison_map_snd F

def coefficientComparison (U V : C) (W : D) (e : F.obj V ≅ W) :
    (sliceFunctor F U).obj (constantFamily U V) ≅ constantFamily (F.obj U) W :=
  familyComparison F U V ≪≫ (constantFamilyFunctor (F.obj U)).mapIso e

omit [HasFiniteCoproducts C] [HasFiniteCoproducts D] in
theorem coefficientComparison_snd (U V : C) (W : D) (e : F.obj V ≅ W) :
    (coefficientComparison F U V W e).hom.left ≫ prod.snd=
      F.map (prod.snd : U ⨯ V ⟶ V) ≫ e.hom := by
  change (prodComparison F U V ≫ prod.map (𝟙 _) e.hom) ≫ prod.snd = _
  rw [Category.assoc,prod.map_snd,← Category.assoc,prodComparison_snd]

omit [HasFiniteCoproducts C] [HasFiniteCoproducts D] in
theorem coefficientComparison_inv_snd (U V : C) (W : D) (e : F.obj V ≅ W) :
    (coefficientComparison F U V W e).inv.left ≫ F.map (prod.snd : U ⨯ V ⟶ V)=
      prod.snd ≫ e.inv := by
  change (prod.map (𝟙 _) e.inv ≫ inv (prodComparison F U V)) ≫ F.map prod.snd=_
  rw [Category.assoc,inv_prodComparison_map_snd,prod.map_snd]

variable (U V : C) (W : D) (e : F.obj V ≅ W)
def mappedParametersIso (L : ListAlgebra V) :
    (mappedList (sliceFunctor F U) (constantFamily U V) (constantFamily (F.obj U) W)
      (coefficientComparison F U V W e) (L.withParameters U)).asAlgebra ≅
        ((mappedList F V W e L).withParameters (F.obj U)).asAlgebra := by
  let H := sliceFunctor F U
  let S := L.withParameters U
  let A := mappedList H (constantFamily U V) (constantFamily (F.obj U) W)
    (coefficientComparison F U V W e) S
  let B := (mappedList F V W e L).withParameters (F.obj U)
  let k := familyComparison F U L.carrier
  have hn : A.nil ≫ k.hom = B.nil := by
    apply Over.OverMorphism.ext
    apply prod.hom_ext
    · exact (Over.w (A.nil ≫ k.hom)).trans (Over.w B.nil).symm
    · erw [Over.comp_left, Category.assoc]
      change (Over.Hom.left (inv (terminalComparison H)) ≫
        F.map S.nil.left) ≫ k.hom.left ≫ prod.snd =
          prod.lift (⊤_ (Over (F.obj U))).hom
            (terminal.from (⊤_ (Over (F.obj U))).left ≫
              (inv (terminalComparison F) ≫ F.map L.nil)) ≫ prod.snd
      erw [prod.lift_snd, Category.assoc, ← F.map_comp]
      change Over.Hom.left (inv (terminalComparison H)) ≫
        F.map (prod.lift (⊤_ (Over U)).hom
          (terminal.from (⊤_ (Over U)).left ≫ L.nil) ≫ prod.snd) = _
      erw [prod.lift_snd, F.map_comp, ← Category.assoc]
      have ht : Over.Hom.left (inv (terminalComparison H)) ≫
          F.map (terminal.from (⊤_ (Over U)).left) =
            terminal.from (⊤_ (Over (F.obj U))).left ≫ inv (terminalComparison F) :=
        (IsTerminal.isTerminalObj F (⊤_ C)
          (Limits.terminalIsTerminal (C := C))).hom_ext _ _
      erw [ht, Category.assoc]
      exact (prod.lift_snd _ _).symm
  have hc : A.cons ≫ k.hom = prod.map (𝟙 (constantFamily (F.obj U) W)) k.hom ≫ B.cons := by
    let Input := constantFamily U V ⨯ S.carrier
    let Z := constantFamily (F.obj U) W ⨯ H.obj S.carrier
    let rS : Input.left ⟶ V ⨯ L.carrier := prod.lift
      ((prod.fst : Input ⟶ constantFamily U V).left ≫ prod.snd)
      ((prod.snd : Input ⟶ S.carrier).left ≫ prod.snd)
    let rR : Z.left ⟶ W ⨯ F.obj L.carrier := prod.lift
      ((prod.fst : Z ⟶ constantFamily (F.obj U) W).left ≫ prod.snd)
      ((prod.snd : Z ⟶ H.obj S.carrier).left ≫ k.hom.left ≫ prod.snd)
    let c := coefficientComparison F U V W e
    let u := prod.map c.inv (𝟙 (H.obj S.carrier))
    let d : Z.left ⟶ F.obj (V ⨯ L.carrier) :=
      u.left ≫ Over.Hom.left (inv (prodComparison H
        (constantFamily U V) S.carrier)) ≫ F.map rS
    have hf : Over.Hom.left (inv (prodComparison H
        (constantFamily U V) S.carrier)) ≫
          F.map (prod.fst : Input ⟶ constantFamily U V).left =
            (prod.fst : H.obj (constantFamily U V) ⨯
              H.obj S.carrier ⟶ H.obj (constantFamily U V)).left :=
      congrArg Over.Hom.left (inv_prodComparison_map_fst H
        (A := constantFamily U V) (B := S.carrier))
    have hs : Over.Hom.left (inv (prodComparison H
        (constantFamily U V) S.carrier)) ≫
          F.map (prod.snd : Input ⟶ S.carrier).left =
            (prod.snd : H.obj (constantFamily U V) ⨯
              H.obj S.carrier ⟶ H.obj S.carrier).left :=
      congrArg Over.Hom.left (inv_prodComparison_map_snd H
        (A := constantFamily U V) (B := S.carrier))
    have hu₁ : u.left ≫
        (prod.fst : H.obj (constantFamily U V) ⨯
          H.obj S.carrier ⟶ H.obj (constantFamily U V)).left =
        (prod.fst : Z ⟶ constantFamily (F.obj U) W).left ≫ c.inv.left :=
      congrArg Over.Hom.left (prod.map_fst c.inv (𝟙 (H.obj S.carrier)))
    have hu₂ : u.left ≫
        (prod.snd : H.obj (constantFamily U V) ⨯
          H.obj S.carrier ⟶ H.obj S.carrier).left =
        (prod.snd : Z ⟶ H.obj S.carrier).left := by
      have h := congrArg Over.Hom.left
        (prod.map_snd c.inv (𝟙 (H.obj S.carrier)))
      simpa only [Over.comp_left, Over.id_left, Category.comp_id] using h
    have hd : d = rR ≫ prod.map e.inv (𝟙 _) ≫
        inv (prodComparison F V L.carrier) := by
      apply (cancel_mono (prodComparison F V L.carrier)).mp
      apply prod.hom_ext
      · simp only [d, Category.assoc, prodComparison_fst,
          inv_prodComparison_map_fst, prod.map_fst, rR, prod.lift_fst_assoc]
        erw [← F.map_comp]
        change u.left ≫ Over.Hom.left (inv (prodComparison H
          (constantFamily U V) S.carrier)) ≫ F.map (rS ≫ prod.fst) = _
        erw [show rS ≫ prod.fst =
          (prod.fst : Input ⟶ constantFamily U V).left ≫ prod.snd from prod.lift_fst _ _,
          F.map_comp,
          ← Category.assoc _ _ (F.map (prod.snd : U ⨯ V ⟶ V)), hf,
          ← Category.assoc _ _ (F.map (prod.snd : U ⨯ V ⟶ V)),
          hu₁, Category.assoc, coefficientComparison_inv_snd]
      · simp only [d, Category.assoc, prodComparison_snd,
          inv_prodComparison_map_snd, prod.map_snd, Category.comp_id, rR, prod.lift_snd]
        erw [← F.map_comp]
        change u.left ≫ Over.Hom.left (inv (prodComparison H
          (constantFamily U V) S.carrier)) ≫ F.map (rS ≫ prod.snd) = _
        erw [show rS ≫ prod.snd = (prod.snd : Input ⟶ S.carrier).left ≫ prod.snd from
          prod.lift_snd _ _, F.map_comp,
          ← Category.assoc _ _ (F.map (prod.snd : U ⨯ L.carrier ⟶ L.carrier)), hs,
          ← Category.assoc _ _ (F.map (prod.snd : U ⨯ L.carrier ⟶ L.carrier)), hu₂,
          familyComparison_snd]
    apply Over.OverMorphism.ext
    apply prod.hom_ext
    · exact (Over.w (A.cons ≫ k.hom)).trans
        (Over.w (prod.map (𝟙 (constantFamily (F.obj U) W)) k.hom ≫ B.cons)).symm
    · have hl : A.cons.left ≫ k.hom.left ≫ prod.snd = d ≫ F.map L.cons := by
        change (u.left ≫ Over.Hom.left (inv (prodComparison H
          (constantFamily U V) S.carrier)) ≫ F.map S.cons.left) ≫
          k.hom.left ≫ prod.snd = _
        erw [Category.assoc, Category.assoc, familyComparison_snd,
          ← F.map_comp]
        change u.left ≫ Over.Hom.left (inv (prodComparison H
          (constantFamily U V) S.carrier)) ≫ F.map
            (prod.lift Input.hom (rS ≫ L.cons) ≫ prod.snd) = _
        erw [prod.lift_snd, F.map_comp]
        simp only [d, Category.assoc]
      erw [Over.comp_left, Over.comp_left, Category.assoc, hl, hd]
      change _ = ((prod.map (𝟙 (constantFamily (F.obj U) W)) k.hom).left ≫
        prod.lift (constantFamily (F.obj U) W ⨯ constantFamily (F.obj U) (F.obj L.carrier)).hom
          (prod.lift
            ((prod.fst : constantFamily (F.obj U) W ⨯ constantFamily (F.obj U) (F.obj L.carrier) ⟶
              constantFamily (F.obj U) W).left ≫ prod.snd)
            ((prod.snd : constantFamily (F.obj U) W ⨯ constantFamily (F.obj U) (F.obj L.carrier) ⟶
              constantFamily (F.obj U) (F.obj L.carrier)).left ≫ prod.snd) ≫
                (mappedList F V W e L).cons)) ≫ prod.snd
      simp only [Category.assoc, prod.lift_snd]
      change _ = (prod.map (𝟙 (constantFamily (F.obj U) W)) k.hom).left ≫ _ ≫
        prod.map e.inv (𝟙 _) ≫ inv (prodComparison F V L.carrier) ≫
          F.map L.cons
      have hr : (prod.map (𝟙 (constantFamily (F.obj U) W)) k.hom).left ≫
          prod.lift
            ((prod.fst : constantFamily (F.obj U) W ⨯ constantFamily (F.obj U) (F.obj L.carrier) ⟶
              constantFamily (F.obj U) W).left ≫ prod.snd)
            ((prod.snd : constantFamily (F.obj U) W ⨯ constantFamily (F.obj U) (F.obj L.carrier) ⟶
              constantFamily (F.obj U) (F.obj L.carrier)).left ≫ prod.snd) = rR := by
        apply prod.hom_ext
        · erw [Category.assoc, prod.lift_fst,
            show rR ≫ prod.fst =
              (prod.fst : Z ⟶ constantFamily (F.obj U) W).left ≫ prod.snd from prod.lift_fst _ _]
          have h₀ := congrArg Over.Hom.left
            (prod.map_fst (𝟙 (constantFamily (F.obj U) W)) k.hom)
          have h : (prod.map (𝟙 (constantFamily (F.obj U) W)) k.hom).left ≫
              (prod.fst : constantFamily (F.obj U) W ⨯ constantFamily (F.obj U) (F.obj L.carrier) ⟶
                constantFamily (F.obj U) W).left =
                  (prod.fst : Z ⟶ constantFamily (F.obj U) W).left :=
            h₀.trans (Category.comp_id _)
          exact (Category.assoc _ _ _).symm.trans
            (congrArg (fun f => f ≫ (prod.snd : F.obj U ⨯ W ⟶ W)) h)
        · erw [Category.assoc, prod.lift_snd,
            show rR ≫ prod.snd =
              (prod.snd : Z ⟶ H.obj S.carrier).left ≫ k.hom.left ≫ prod.snd from
                prod.lift_snd _ _]
          have h : (prod.map (𝟙 (constantFamily (F.obj U) W)) k.hom).left ≫
              (prod.snd : constantFamily (F.obj U) W ⨯ constantFamily (F.obj U) (F.obj L.carrier) ⟶
                constantFamily (F.obj U) (F.obj L.carrier)).left =
              (prod.snd : Z ⟶ H.obj S.carrier).left ≫ k.hom.left :=
            congrArg Over.Hom.left (prod.map_snd (𝟙 (constantFamily (F.obj U) W)) k.hom)
          exact (Category.assoc _ _ _).symm.trans
            ((congrArg (fun f => f ≫ (prod.snd : F.obj U ⨯ F.obj L.carrier ⟶
              F.obj L.carrier)) h).trans (Category.assoc _ _ _))
      erw [← Category.assoc, ← Category.assoc, ← Category.assoc, hr]
      simp only [Category.assoc]
  exact constructorsIso A B k hn hc


/-- A constructor comparison maps source algebra morphisms. It does not
assert preservation of initial algebras by the interpretation functor. -/
def mappedConstructorsIso (A : ListAlgebra V) (B : ListAlgebra W)
    (i : F.obj A.carrier ≅ B.carrier)
    (hn : F.map A.nil ≫ i.hom=terminalComparison F ≫ B.nil)
    (hc : F.map A.cons ≫ i.hom=
      prodComparison F V A.carrier ≫ prod.map e.hom i.hom ≫ B.cons) :
    (mappedList F V W e A).asAlgebra ≅ B.asAlgebra := by
  refine constructorsIso _ _ i ?_ ?_
  · change (inv (terminalComparison F) ≫ F.map A.nil) ≫ i.hom=B.nil
    rw [Category.assoc,hn,← Category.assoc,IsIso.inv_hom_id,Category.id_comp]
  · change (prod.map e.inv (𝟙 _) ≫ inv (prodComparison F V A.carrier) ≫
      F.map A.cons) ≫ i.hom=prod.map (𝟙 W) i.hom ≫ B.cons
    simp only [Category.assoc]
    rw [hc]
    simp only [IsIso.inv_hom_id_assoc,prod.map_map_assoc,e.inv_hom_id,Category.id_comp]

/-- Extend a constructor-preserving list isomorphism to every parameter slice. This
argument uses no preservation of initiality. -/
def parametersIso {W : D} (L B : ListAlgebra W) (i : L.carrier ≅ B.carrier)
    (hn : L.nil ≫ i.hom=B.nil)
    (hc : L.cons ≫ i.hom=prod.map (𝟙 W) i.hom ≫ B.cons)
    (R : D) : (L.withParameters R).asAlgebra ≅ (B.withParameters R).asAlgebra := by
  let k : constantFamily R L.carrier ⟶ constantFamily R B.carrier :=
    ((constantFamilyFunctor R).mapIso i).hom
  apply constructorsIso _ _ ((constantFamilyFunctor R).mapIso i)
  · apply Over.OverMorphism.ext
    apply prod.hom_ext
    · exact (Over.w ((L.withParameters R).nil ≫ k)).trans (Over.w (B.withParameters R).nil).symm
    · change (prod.lift (⊤_ (Over R)).hom (terminal.from (⊤_ (Over R)).left ≫ L.nil) ≫
        prod.map (𝟙 R) i.hom) ≫ prod.snd =
          prod.lift (⊤_ (Over R)).hom (terminal.from (⊤_ (Over R)).left ≫ B.nil) ≫ prod.snd
      rw [Category.assoc,prod.map_snd,← Category.assoc,prod.lift_snd,prod.lift_snd,Category.assoc,hn]
  · apply Over.OverMorphism.ext
    apply prod.hom_ext
    · exact (Over.w ((L.withParameters R).cons ≫ k)).trans
        (Over.w (prod.map (𝟙 (constantFamily R W)) k ≫ (B.withParameters R).cons)).symm
    · let A₀ := constantFamily R W
      let LA := constantFamily R L.carrier
      let B₀ := constantFamily R B.carrier
      let m : A₀ ⨯ LA ⟶ A₀ ⨯ B₀ := prod.map (𝟙 A₀) k
      let hL : (A₀ ⨯ LA).left ⟶ W ⨯ L.carrier := prod.lift
        ((prod.fst : A₀ ⨯ LA ⟶ A₀).left ≫ prod.snd)
        ((prod.snd : A₀ ⨯ LA ⟶ LA).left ≫ prod.snd)
      let hB : (A₀ ⨯ B₀).left ⟶ W ⨯ B.carrier := prod.lift
        ((prod.fst : A₀ ⨯ B₀ ⟶ A₀).left ≫ prod.snd)
        ((prod.snd : A₀ ⨯ B₀ ⟶ B₀).left ≫ prod.snd)
      change (prod.lift (A₀ ⨯ LA).hom (hL ≫ L.cons) ≫ prod.map (𝟙 R) i.hom) ≫ prod.snd =
        (m.left ≫ prod.lift (A₀ ⨯ B₀).hom (hB ≫ B.cons)) ≫ prod.snd
      rw [Category.assoc,prod.map_snd,← Category.assoc,prod.lift_snd,
        Category.assoc,hc,Category.assoc,prod.lift_snd]
      rw [← Category.assoc hL (prod.map (𝟙 W) i.hom) B.cons,
        ← Category.assoc m.left hB B.cons]
      apply congrArg (fun f => f ≫ B.cons)
      apply prod.hom_ext
      · have hf : m.left ≫ (prod.fst : A₀ ⨯ B₀ ⟶ A₀).left =
            (prod.fst : A₀ ⨯ LA ⟶ A₀).left := by
          simpa only [Over.comp_left,Over.id_left,Category.comp_id] using
            congrArg Over.Hom.left (prod.map_fst (W := A₀) (X := LA) (Y := A₀) (Z := B₀) (𝟙 A₀) k)
        calc
          _ = (prod.fst : A₀ ⨯ LA ⟶ A₀).left ≫ prod.snd := by
            simp only [hL,Category.assoc,prod.map_fst,Category.comp_id,prod.lift_fst]
          _ = m.left ≫ (prod.fst : A₀ ⨯ B₀ ⟶ A₀).left ≫ prod.snd := by
            simpa only [Category.assoc] using congrArg (fun f => f ≫ (prod.snd : R ⨯ W ⟶ W)) hf.symm
          _ = _ := by simp only [hB,Category.assoc,prod.lift_fst]
      · have hs : m.left ≫ (prod.snd : A₀ ⨯ B₀ ⟶ B₀).left =
            (prod.snd : A₀ ⨯ LA ⟶ LA).left ≫ k.left := by
          exact congrArg Over.Hom.left (prod.map_snd (W := A₀) (X := LA) (Y := A₀) (Z := B₀) (𝟙 A₀) k)
        calc
          _ = (prod.snd : A₀ ⨯ LA ⟶ LA).left ≫ prod.snd ≫ i.hom := by
            have hp : hL ≫ prod.snd = (prod.snd : A₀ ⨯ LA ⟶ LA).left ≫ prod.snd :=
              prod.lift_snd _ _
            rw [Category.assoc,prod.map_snd,← Category.assoc]
            simpa only [Category.assoc] using congrArg (fun f => f ≫ i.hom) hp
          _ = (prod.snd : A₀ ⨯ LA ⟶ LA).left ≫ k.left ≫ prod.snd := by
            simp only [k,Functor.mapIso_hom,constantFamilyFunctor,Over.homMk_left,prod.map_snd]
          _ = m.left ≫ (prod.snd : A₀ ⨯ B₀ ⟶ B₀).left ≫ prod.snd := by
            simpa only [Category.assoc] using
              congrArg (fun f => f ≫ (prod.snd : R ⨯ B.carrier ⟶ B.carrier)) hs.symm
          _ = _ := by simp only [hB,Category.assoc,prod.lift_snd]

/-- Target slice initiality makes the mapped source fold the unique target
fold. The target initiality is independently constructed, and its carrier
comparison is retained explicitly. -/
theorem parameterFold_comparison (L : StableListAlgebra V)
    (R : StableListAlgebra W)
    (a : (mappedList F V W e L.algebra).asAlgebra ≅ R.algebra.asAlgebra)
    (B₀ : ListAlgebra (constantFamily U V))
    (B₁ : ListAlgebra (constantFamily (F.obj U) W))
    (i : (mappedList (sliceFunctor F U) (constantFamily U V)
      (constantFamily (F.obj U) W) (coefficientComparison F U V W e) B₀).asAlgebra ≅ B₁.asAlgebra) :
    (familyComparison F U L.algebra.carrier).inv ≫
      (sliceFunctor F U).map (L.foldWithParameters U B₀) ≫ i.hom.f =
        (constantFamilyFunctor (F.obj U)).map a.hom.f ≫
          R.foldWithParameters (F.obj U) B₁ := by
  let k := familyComparison F U L.algebra.carrier
  let ar := (constantFamilyFunctor (F.obj U)).mapIso
    ((Endofunctor.Algebra.forget (listFunctor W)).mapIso a)
  let param := mappedParametersIso F U V W e L.algebra ≪≫
    parametersIso _ _ ((Endofunctor.Algebra.forget (listFunctor W)).mapIso a)
      (SyntaxOperationsTransport.listHom_nil a.hom) (SyntaxOperationsTransport.listHom_cons a.hom)
      (F.obj U)
  let mapped := mappedHom (sliceFunctor F U) (constantFamily U V)
    (constantFamily (F.obj U) W) (coefficientComparison F U V W e)
    ((L.stable U).to B₀.asAlgebra)
  let candidate := param.inv ≫ mapped ≫ i.hom
  have hh := congrArg (fun f => ar.hom ≫ f)
    (congrArg Endofunctor.Algebra.Hom.f
      ((R.stable (F.obj U)).hom_ext candidate ((R.stable (F.obj U)).to B₁.asAlgebra)))
  have hparam : param.inv.f=ar.inv ≫ k.inv := rfl
  change ar.hom ≫ (param.inv.f ≫ (sliceFunctor F U).map ((L.stable U).to B₀.asAlgebra).f ≫ i.hom.f)=
    ar.hom ≫ ((R.stable (F.obj U)).to B₁.asAlgebra).f at hh
  rw [hparam] at hh
  have h := hh
  simp only [Category.assoc,Iso.hom_inv_id_assoc] at h
  exact h
end Generic
end CategoricalEssentialIncompleteness.V46.Miller.NamedSyntaxComparison.ListTransport
