/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46SyntacticListsTransport

/-! # Canonical family comparisons for transporting stable lists -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v₁ v₂ u₁ u₂
open CategoryTheory CategoryTheory.Limits

namespace CategoricalEssentialIncompleteness.V46.SyntacticLists.Transport
variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
variable [HasFiniteLimits C]
variable [HasFiniteLimits D]
variable (E : C ≌ D) {P : C} {Q : D} (b : E.functor.obj P ≅ Q)

/-- Apply the equivalence to a family, then compose its projection with
the actual parameter isomorphism. -/
def sliceEquivalence : Over P ≌ Over Q :=
  ((Over.post (X := P) E.functor) ⋙ Over.map b.hom).asEquivalence

/-- A constant family is preserved under the canonical product comparison.
Both its carrier and its projection are compared explicitly. -/
def familyComparison (X : C) :
    (sliceEquivalence E b).functor.obj (constantFamily P X) ≅
      constantFamily Q (E.functor.obj X) :=
  Over.isoMk ((asIso (prodComparison E.functor P X)) ≪≫
    prod.mapIso b (Iso.refl _)) (by
      change (prodComparison E.functor P X ≫ prod.map b.hom (𝟙 _)) ≫
        prod.fst = E.functor.map prod.fst ≫ b.hom
      simp [Category.assoc])

@[reassoc] theorem familyComparison_snd (X : C) :
    (familyComparison E b X).hom.left ≫
      (prod.snd : Q ⨯ E.functor.obj X ⟶ E.functor.obj X) =
        E.functor.map (prod.snd : P ⨯ X ⟶ X) := by
  simp [familyComparison, Category.assoc]

@[reassoc] theorem familyComparison_inv_snd (X : C) :
    (familyComparison E b X).inv.left ≫ E.functor.map (prod.snd : P ⨯ X ⟶ X) =
      (prod.snd : Q ⨯ E.functor.obj X ⟶ E.functor.obj X) := by
  erw [← familyComparison_snd E b X, ← Category.assoc]
  have h := congrArg Over.Hom.left (familyComparison E b X).inv_hom_id
  change (familyComparison E b X).inv.left ≫ (familyComparison E b X).hom.left = 𝟙 _ at h
  erw [h, Category.id_comp]

/-- In addition to the parameter, the coefficient may be replaced by any
isomorphic object, including the counit at an arbitrary target object. -/
def coefficientComparison (V : C) (W : D) (e : E.functor.obj V ≅ W) :
    (sliceEquivalence E b).functor.obj (constantFamily P V) ≅ constantFamily Q W :=
  familyComparison E b V ≪≫ (constantFamilyFunctor Q).mapIso e

@[reassoc] theorem coefficientComparison_snd (V : C) (W : D)
    (e : E.functor.obj V ≅ W) :
    (coefficientComparison E b V W e).hom.left ≫ (prod.snd : Q ⨯ W ⟶ W) =
      E.functor.map (prod.snd : P ⨯ V ⟶ V) ≫ e.hom := by
  simp [coefficientComparison, constantFamilyFunctor, Category.assoc,
    familyComparison_snd_assoc]

@[reassoc] theorem coefficientComparison_inv_snd (V : C) (W : D)
    (e : E.functor.obj V ≅ W) :
    (coefficientComparison E b V W e).inv.left ≫
      E.functor.map (prod.snd : P ⨯ V ⟶ V) = (prod.snd : Q ⨯ W ⟶ W) ≫ e.inv := by
  apply (cancel_mono e.hom).mp
  erw [Category.assoc, ← coefficientComparison_snd E b V W e, ← Category.assoc]
  have h := congrArg Over.Hom.left (coefficientComparison E b V W e).inv_hom_id
  change (coefficientComparison E b V W e).inv.left ≫
    (coefficientComparison E b V W e).hom.left = 𝟙 _ at h
  erw [h, Category.id_comp]
  simp

section Parameters
variable [HasFiniteCoproducts C] [HasFiniteCoproducts D]
variable (V : C) (W : D) (e : E.functor.obj V ≅ W) (L : ListAlgebra V)

/-- Compare the complete transported parameter algebra with the parameter
algebra of the transported constructors. The comparison is the canonical
product comparison on the actual carriers. -/
def mappedParametersIso :
    (mappedListAlgebra (sliceEquivalence E b) (constantFamily P V) (constantFamily Q W)
      (coefficientComparison E b V W e) (L.withParameters P)).asAlgebra ≅
        ((mappedListAlgebra E V W e L).withParameters Q).asAlgebra := by
  let H := sliceEquivalence E b
  let S := L.withParameters P
  let A := mappedListAlgebra H (constantFamily P V) (constantFamily Q W)
    (coefficientComparison E b V W e) S
  let B := (mappedListAlgebra E V W e L).withParameters Q
  let k := familyComparison E b L.carrier
  have hn : A.nil ≫ k.hom = B.nil := by
    apply Over.OverMorphism.ext
    apply prod.hom_ext
    · exact (Over.w (A.nil ≫ k.hom)).trans (Over.w B.nil).symm
    · erw [Over.comp_left, Category.assoc]
      change (Over.Hom.left (inv (terminalComparison H.functor)) ≫
        E.functor.map S.nil.left) ≫ k.hom.left ≫ prod.snd =
          prod.lift (⊤_ (Over Q)).hom
            (terminal.from (⊤_ (Over Q)).left ≫
              (inv (terminalComparison E.functor) ≫ E.functor.map L.nil)) ≫ prod.snd
      erw [prod.lift_snd, Category.assoc, familyComparison_snd,
        ← E.functor.map_comp]
      change Over.Hom.left (inv (terminalComparison H.functor)) ≫
        E.functor.map (prod.lift (⊤_ (Over P)).hom
          (terminal.from (⊤_ (Over P)).left ≫ L.nil) ≫ prod.snd) = _
      erw [prod.lift_snd, E.functor.map_comp, ← Category.assoc]
      have ht : Over.Hom.left (inv (terminalComparison H.functor)) ≫
          E.functor.map (terminal.from (⊤_ (Over P)).left) =
            terminal.from (⊤_ (Over Q)).left ≫ inv (terminalComparison E.functor) :=
        (IsTerminal.isTerminalObj E.functor (⊤_ C)
          (Limits.terminalIsTerminal (C := C))).hom_ext _ _
      erw [ht, Category.assoc]
  have hc : A.cons ≫ k.hom = prod.map (𝟙 (constantFamily Q W)) k.hom ≫ B.cons := by
    let U := constantFamily P V ⨯ S.carrier
    let Z := constantFamily Q W ⨯ H.functor.obj S.carrier
    let rS : U.left ⟶ V ⨯ L.carrier := prod.lift
      ((prod.fst : U ⟶ constantFamily P V).left ≫ prod.snd)
      ((prod.snd : U ⟶ S.carrier).left ≫ prod.snd)
    let rR : Z.left ⟶ W ⨯ E.functor.obj L.carrier := prod.lift
      ((prod.fst : Z ⟶ constantFamily Q W).left ≫ prod.snd)
      ((prod.snd : Z ⟶ H.functor.obj S.carrier).left ≫ k.hom.left ≫ prod.snd)
    let c := coefficientComparison E b V W e
    let u := prod.map c.inv (𝟙 (H.functor.obj S.carrier))
    let d : Z.left ⟶ E.functor.obj (V ⨯ L.carrier) :=
      u.left ≫ Over.Hom.left (inv (prodComparison H.functor
        (constantFamily P V) S.carrier)) ≫ E.functor.map rS
    have hf : Over.Hom.left (inv (prodComparison H.functor
        (constantFamily P V) S.carrier)) ≫
          E.functor.map (prod.fst : U ⟶ constantFamily P V).left =
            (prod.fst : H.functor.obj (constantFamily P V) ⨯
              H.functor.obj S.carrier ⟶ H.functor.obj (constantFamily P V)).left :=
      congrArg Over.Hom.left (inv_prodComparison_map_fst H.functor
        (A := constantFamily P V) (B := S.carrier))
    have hs : Over.Hom.left (inv (prodComparison H.functor
        (constantFamily P V) S.carrier)) ≫
          E.functor.map (prod.snd : U ⟶ S.carrier).left =
            (prod.snd : H.functor.obj (constantFamily P V) ⨯
              H.functor.obj S.carrier ⟶ H.functor.obj S.carrier).left :=
      congrArg Over.Hom.left (inv_prodComparison_map_snd H.functor
        (A := constantFamily P V) (B := S.carrier))
    have hu₁ : u.left ≫
        (prod.fst : H.functor.obj (constantFamily P V) ⨯
          H.functor.obj S.carrier ⟶ H.functor.obj (constantFamily P V)).left =
        (prod.fst : Z ⟶ constantFamily Q W).left ≫ c.inv.left :=
      congrArg Over.Hom.left (prod.map_fst c.inv (𝟙 (H.functor.obj S.carrier)))
    have hu₂ : u.left ≫
        (prod.snd : H.functor.obj (constantFamily P V) ⨯
          H.functor.obj S.carrier ⟶ H.functor.obj S.carrier).left =
        (prod.snd : Z ⟶ H.functor.obj S.carrier).left := by
      have h := congrArg Over.Hom.left
        (prod.map_snd c.inv (𝟙 (H.functor.obj S.carrier)))
      simpa only [Over.comp_left, Over.id_left, Category.comp_id] using h
    have hd : d = rR ≫ prod.map e.inv (𝟙 _) ≫
        inv (prodComparison E.functor V L.carrier) := by
      apply (cancel_mono (prodComparison E.functor V L.carrier)).mp
      apply prod.hom_ext
      · simp only [d, Category.assoc, prodComparison_fst,
          inv_prodComparison_map_fst, prod.map_fst, rR, prod.lift_fst_assoc]
        erw [← E.functor.map_comp]
        change u.left ≫ Over.Hom.left (inv (prodComparison H.functor
          (constantFamily P V) S.carrier)) ≫ E.functor.map (rS ≫ prod.fst) = _
        erw [show rS ≫ prod.fst =
          (prod.fst : U ⟶ constantFamily P V).left ≫ prod.snd from prod.lift_fst _ _,
          E.functor.map_comp,
          ← Category.assoc _ _ (E.functor.map (prod.snd : P ⨯ V ⟶ V)), hf,
          ← Category.assoc _ _ (E.functor.map (prod.snd : P ⨯ V ⟶ V)),
          hu₁, Category.assoc, coefficientComparison_inv_snd]
      · simp only [d, Category.assoc, prodComparison_snd,
          inv_prodComparison_map_snd, prod.map_snd, Category.comp_id, rR, prod.lift_snd]
        erw [← E.functor.map_comp]
        change u.left ≫ Over.Hom.left (inv (prodComparison H.functor
          (constantFamily P V) S.carrier)) ≫ E.functor.map (rS ≫ prod.snd) = _
        erw [show rS ≫ prod.snd = (prod.snd : U ⟶ S.carrier).left ≫ prod.snd from
          prod.lift_snd _ _, E.functor.map_comp,
          ← Category.assoc _ _ (E.functor.map (prod.snd : P ⨯ L.carrier ⟶ L.carrier)), hs,
          ← Category.assoc _ _ (E.functor.map (prod.snd : P ⨯ L.carrier ⟶ L.carrier)), hu₂,
          familyComparison_snd]
    apply Over.OverMorphism.ext
    apply prod.hom_ext
    · exact (Over.w (A.cons ≫ k.hom)).trans
        (Over.w (prod.map (𝟙 (constantFamily Q W)) k.hom ≫ B.cons)).symm
    · have hl : A.cons.left ≫ k.hom.left ≫ prod.snd = d ≫ E.functor.map L.cons := by
        change (u.left ≫ Over.Hom.left (inv (prodComparison H.functor
          (constantFamily P V) S.carrier)) ≫ E.functor.map S.cons.left) ≫
          k.hom.left ≫ prod.snd = _
        erw [Category.assoc, Category.assoc, familyComparison_snd,
          ← E.functor.map_comp]
        change u.left ≫ Over.Hom.left (inv (prodComparison H.functor
          (constantFamily P V) S.carrier)) ≫ E.functor.map
            (prod.lift U.hom (rS ≫ L.cons) ≫ prod.snd) = _
        erw [prod.lift_snd, E.functor.map_comp]
        simp only [d, Category.assoc]
      erw [Over.comp_left, Over.comp_left, Category.assoc, hl, hd]
      change _ = ((prod.map (𝟙 (constantFamily Q W)) k.hom).left ≫
        prod.lift (constantFamily Q W ⨯ constantFamily Q (E.functor.obj L.carrier)).hom
          (prod.lift
            ((prod.fst : constantFamily Q W ⨯ constantFamily Q (E.functor.obj L.carrier) ⟶
              constantFamily Q W).left ≫ prod.snd)
            ((prod.snd : constantFamily Q W ⨯ constantFamily Q (E.functor.obj L.carrier) ⟶
              constantFamily Q (E.functor.obj L.carrier)).left ≫ prod.snd) ≫
                (mappedListAlgebra E V W e L).cons)) ≫ prod.snd
      simp only [Category.assoc, prod.lift_snd]
      change _ = (prod.map (𝟙 (constantFamily Q W)) k.hom).left ≫ _ ≫
        prod.map e.inv (𝟙 _) ≫ inv (prodComparison E.functor V L.carrier) ≫
          E.functor.map L.cons
      have hr : (prod.map (𝟙 (constantFamily Q W)) k.hom).left ≫
          prod.lift
            ((prod.fst : constantFamily Q W ⨯ constantFamily Q (E.functor.obj L.carrier) ⟶
              constantFamily Q W).left ≫ prod.snd)
            ((prod.snd : constantFamily Q W ⨯ constantFamily Q (E.functor.obj L.carrier) ⟶
              constantFamily Q (E.functor.obj L.carrier)).left ≫ prod.snd) = rR := by
        apply prod.hom_ext
        · erw [Category.assoc, prod.lift_fst,
            show rR ≫ prod.fst =
              (prod.fst : Z ⟶ constantFamily Q W).left ≫ prod.snd from prod.lift_fst _ _]
          have h₀ := congrArg Over.Hom.left
            (prod.map_fst (𝟙 (constantFamily Q W)) k.hom)
          have h : (prod.map (𝟙 (constantFamily Q W)) k.hom).left ≫
              (prod.fst : constantFamily Q W ⨯ constantFamily Q (E.functor.obj L.carrier) ⟶
                constantFamily Q W).left =
                  (prod.fst : Z ⟶ constantFamily Q W).left :=
            h₀.trans (Category.comp_id _)
          exact (Category.assoc _ _ _).symm.trans
            (congrArg (fun f => f ≫ (prod.snd : Q ⨯ W ⟶ W)) h)
        · erw [Category.assoc, prod.lift_snd,
            show rR ≫ prod.snd =
              (prod.snd : Z ⟶ H.functor.obj S.carrier).left ≫ k.hom.left ≫ prod.snd from
                prod.lift_snd _ _]
          have h : (prod.map (𝟙 (constantFamily Q W)) k.hom).left ≫
              (prod.snd : constantFamily Q W ⨯ constantFamily Q (E.functor.obj L.carrier) ⟶
                constantFamily Q (E.functor.obj L.carrier)).left =
              (prod.snd : Z ⟶ H.functor.obj S.carrier).left ≫ k.hom.left :=
            congrArg Over.Hom.left (prod.map_snd (𝟙 (constantFamily Q W)) k.hom)
          exact (Category.assoc _ _ _).symm.trans
            ((congrArg (fun f => f ≫ (prod.snd : Q ⨯ E.functor.obj L.carrier ⟶
              E.functor.obj L.carrier)) h).trans (Category.assoc _ _ _))
      erw [← Category.assoc, ← Category.assoc, ← Category.assoc, hr]
      simp only [Category.assoc]
  exact constructorsIso A B k hn hc

/-- Slice initiality is transported with its actual parameter and
coefficient comparisons; no initiality is inserted into the data. -/
def mappedParametersInitial (hL : IsInitial (L.withParameters P).asAlgebra) :
    IsInitial ((mappedListAlgebra E V W e L).withParameters Q).asAlgebra :=
  (mappedListInitial (sliceEquivalence E b) (constantFamily P V) (constantFamily Q W)
    (coefficientComparison E b V W e) (L.withParameters P) hL).ofIso
      (mappedParametersIso E b V W e L)

/-- Every stable list algebra is carried to a stable list algebra under
an equivalence, for every target coefficient object in its essential image. -/
def mappedStableListAlgebra (L : StableListAlgebra V) : StableListAlgebra W where
  algebra := mappedListAlgebra E V W e L.algebra
  initial := mappedListInitial E V W e L.algebra L.initial
  stable Q := mappedParametersInitial E (E.counitIso.app Q) V W e L.algebra
    (L.stable (E.inverse.obj Q))

end Parameters

end CategoricalEssentialIncompleteness.V46.SyntacticLists.Transport
