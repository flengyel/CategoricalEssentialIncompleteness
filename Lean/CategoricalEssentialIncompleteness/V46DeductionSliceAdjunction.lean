/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46DeductionComparison
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.Adjunction.Limits

/-! # The pullback right adjoint for change of the ambient category

For G ⊣ H, postcomposition with σ after G has right adjoint given by
pullback of H along η ≫ Hσ. The comparison with the composed slice
adjunction preserves both pullback coordinates.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v₁ v₂ u₁ u₂

open CategoryTheory CategoryTheory.Limits

namespace CategoricalEssentialIncompleteness.V46.DeductionSliceAdjunction

variable {D₁ : Type u₁} {D₂ : Type u₂}
variable [Category.{v₁} D₁] [Category.{v₂} D₂] [Regular D₁] [Regular D₂]
variable {G : D₁ ⥤ D₂} {H : D₂ ⥤ D₁} (adj : G ⊣ H)
variable {S₁ : D₁} {S₂ : D₂} (σ : G.obj S₁ ⟶ S₂)

def frame : S₁ ⟶ H.obj S₂ := adj.unit.app S₁ ≫ H.map σ

@[implicit_reducible]
def rightFunctor : Over S₂ ⥤ Over S₁ := Over.post H ⋙ Over.pullback (frame adj σ)

@[implicit_reducible]
def iteratedRight : Over S₂ ⥤ Over S₁ :=
  Over.pullback σ ⋙ Over.post H ⋙ Over.pullback (adj.unit.app S₁)

theorem right_square (b : Over S₂) :
    IsPullback
      (pullback.fst (H.map (pullback.snd b.hom σ)) (adj.unit.app S₁) ≫
        H.map (pullback.fst b.hom σ))
      (pullback.snd (H.map (pullback.snd b.hom σ)) (adj.unit.app S₁))
      (H.map b.hom) (frame adj σ) := by
  have : H.IsRightAdjoint := adj.isRightAdjoint
  exact (IsPullback.of_hasPullback (H.map (pullback.snd b.hom σ)) (adj.unit.app S₁)).paste_horiz
    (H.map_isPullback (IsPullback.of_hasPullback b.hom σ))

def rightObjectIso (b : Over S₂) :
    ((iteratedRight adj σ).obj b).left ≅ ((rightFunctor adj σ).obj b).left :=
  (right_square adj σ b).isoPullback

@[reassoc (attr := simp)] theorem rightObjectIso_fst (b : Over S₂) :
    (rightObjectIso adj σ b).hom ≫ pullback.fst (H.map b.hom) (frame adj σ) =
      pullback.fst (H.map (pullback.snd b.hom σ)) (adj.unit.app S₁) ≫
        H.map (pullback.fst b.hom σ) :=
  (right_square adj σ b).isoPullback_hom_fst

@[reassoc (attr := simp)] theorem rightObjectIso_snd (b : Over S₂) :
    (rightObjectIso adj σ b).hom ≫ ((rightFunctor adj σ).obj b).hom =
      ((iteratedRight adj σ).obj b).hom :=
  (right_square adj σ b).isoPullback_hom_snd

omit [Regular D₂] in
theorem right_map_fst {b c : Over S₂} (f : b ⟶ c) :
    ((rightFunctor adj σ).map f).left ≫ pullback.fst (H.map c.hom) (frame adj σ) =
      pullback.fst (H.map b.hom) (frame adj σ) ≫ H.map f.left := by
  change pullback.lift _ _ _ ≫ pullback.fst _ _ = _
  exact pullback.lift_fst _ _ _

theorem iterated_map_fst {b c : Over S₂} (f : b ⟶ c) :
    ((iteratedRight adj σ).map f).left ≫
        pullback.fst (H.map (pullback.snd c.hom σ)) (adj.unit.app S₁) =
      pullback.fst (H.map (pullback.snd b.hom σ)) (adj.unit.app S₁) ≫
        H.map ((Over.pullback σ).map f).left := by
  change pullback.lift _ _ _ ≫ pullback.fst _ _ = _
  exact pullback.lift_fst _ _ _

def rightIso : iteratedRight adj σ ≅ rightFunctor adj σ :=
  NatIso.ofComponents (fun b => Over.isoMk (rightObjectIso adj σ b) (rightObjectIso_snd adj σ b))
    (by
      intro b c f
      apply Over.OverMorphism.ext
      apply pullback.hom_ext
      · have hf : ((Over.pullback σ).map f).left ≫ pullback.fst c.hom σ =
            pullback.fst b.hom σ ≫ f.left := pullback.lift_fst _ _ _
        change (((iteratedRight adj σ).map f).left ≫ (rightObjectIso adj σ c).hom) ≫
            pullback.fst (H.map c.hom) (frame adj σ) =
          ((rightObjectIso adj σ b).hom ≫ ((rightFunctor adj σ).map f).left) ≫
            pullback.fst (H.map c.hom) (frame adj σ)
        simp only [Category.assoc]
        calc
          _ = ((iteratedRight adj σ).map f).left ≫
              pullback.fst (H.map (pullback.snd c.hom σ)) (adj.unit.app S₁) ≫
                H.map (pullback.fst c.hom σ) := by rw [rightObjectIso_fst]
          _ = pullback.fst (H.map (pullback.snd b.hom σ)) (adj.unit.app S₁) ≫
              H.map ((Over.pullback σ).map f).left ≫ H.map (pullback.fst c.hom σ) := by
            rw [← Category.assoc, iterated_map_fst, Category.assoc]
          _ = pullback.fst (H.map (pullback.snd b.hom σ)) (adj.unit.app S₁) ≫
              H.map (pullback.fst b.hom σ) ≫ H.map f.left := by
            rw [← H.map_comp, hf, H.map_comp]
          _ = (rightObjectIso adj σ b).hom ≫
              pullback.fst (H.map b.hom) (frame adj σ) ≫ H.map f.left := by
            simpa only [Category.assoc] using congrArg (fun h => h ≫ H.map f.left)
              (rightObjectIso_fst adj σ b).symm
          _ = _ := by rw [right_map_fst]
      · change (((iteratedRight adj σ).map f).left ≫ (rightObjectIso adj σ c).hom) ≫
            ((rightFunctor adj σ).obj c).hom =
          ((rightObjectIso adj σ b).hom ≫ ((rightFunctor adj σ).map f).left) ≫
            ((rightFunctor adj σ).obj c).hom
        rw [Category.assoc, rightObjectIso_snd, Over.w,
          Category.assoc, Over.w, rightObjectIso_snd])

omit [Regular D₁] [Regular D₂] in
theorem presentationFunctor_eq_post :
    DeductionComparison.presentationFunctor G σ = Over.post G ⋙ Over.map σ := by
  exact CategoryTheory.Functor.ext (fun _ => rfl) (fun _ _ _ => by
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    apply Over.OverMorphism.ext
    rfl)

def adjunction : DeductionComparison.presentationFunctor G σ ⊣ rightFunctor adj σ := by
  rw [presentationFunctor_eq_post]
  exact ((Over.postAdjunctionLeft adj).comp (Over.mapPullbackAdj σ)).ofNatIsoRight
    (rightIso adj σ)

include adj in
omit [Regular D₁] [Regular D₂] in
theorem right_map_mono {X Y : D₂} (f : X ⟶ Y) [Mono f] : Mono (H.map f) := by
  constructor
  intro Z u v h
  apply (adj.homEquiv Z X).symm.injective
  apply (cancel_mono f).mp
  rw [← adj.homEquiv_naturality_right_symm,
    ← adj.homEquiv_naturality_right_symm, h]

/-- The subobject in the displayed formula for the restricted right
adjoint, with its projection to the source sentence object. -/
def rightObject (B : Subobject S₂) : Subobject S₁ := by
  letI : Mono (H.map B.arrow) := right_map_mono adj B.arrow
  exact Subobject.mk (pullback.snd (H.map B.arrow) (frame adj σ))

omit [Regular D₂] in
theorem right_monotone : Monotone (rightObject adj σ) := by
  intro B C h
  have : Mono (H.map B.arrow) := right_map_mono adj B.arrow
  have : Mono (H.map C.arrow) := right_map_mono adj C.arrow
  let f : Over.mk B.arrow ⟶ Over.mk C.arrow :=
    Over.homMk (Subobject.ofLE B C h) (Subobject.ofLE_arrow h)
  let g := (rightFunctor adj σ).map f
  exact Subobject.mk_le_mk_of_comm g.left (Over.w g)

def rightOrder : Subobject S₂ ⥤ Subobject S₁ where
  obj := rightObject adj σ
  map f := homOfLE (right_monotone adj σ (leOfHom f))

theorem order_galois :
    GaloisConnection (DeductionComparison.imageObject G σ) (rightObject adj σ) := by
  intro A B
  have : Mono (H.map B.arrow) := right_map_mono adj B.arrow
  constructor
  · intro h
    let f : (DeductionComparison.presentationFunctor G σ).obj (Over.mk A.arrow) ⟶
        Over.mk B.arrow := Over.homMk
      (factorThruImageSubobject (G.map A.arrow ≫ σ) ≫
        Subobject.ofLE (DeductionComparison.imageObject G σ A) B h) (by
          change (_ ≫ Subobject.ofLE _ _ h) ≫ B.arrow = G.map A.arrow ≫ σ
          rw [Category.assoc, Subobject.ofLE_arrow]
          exact imageSubobject_arrow_comp (G.map A.arrow ≫ σ))
    let g := (adjunction adj σ).homEquiv (Over.mk A.arrow) (Over.mk B.arrow) f
    exact Subobject.le_mk_of_comm g.left (Over.w g)
  · intro h
    have : Mono (Over.mk A.arrow).hom := inferInstanceAs (Mono A.arrow)
    have : Mono ((rightFunctor adj σ).obj (Over.mk B.arrow)).hom := by
      change Mono (pullback.snd (H.map B.arrow) (frame adj σ))
      infer_instance
    have h' : Subobject.mk (Over.mk A.arrow).hom ≤
        Subobject.mk ((rightFunctor adj σ).obj (Over.mk B.arrow)).hom := by
      change Subobject.mk A.arrow ≤ rightObject adj σ B
      simpa only [Subobject.mk_arrow] using h
    let g : Over.mk A.arrow ⟶ (rightFunctor adj σ).obj (Over.mk B.arrow) :=
      Over.homMk (Subobject.ofMkLEMk _ _ h') (Subobject.ofMkLEMk_comp h')
    let f := ((adjunction adj σ).homEquiv (Over.mk A.arrow) (Over.mk B.arrow)).symm g
    change imageSubobject (G.map A.arrow ≫ σ) ≤ B
    simpa only [Subobject.mk_arrow] using
      imageSubobject_le_mk B.arrow (G.map A.arrow ≫ σ) f.left (Over.w f)

def orderAdjunction : DeductionComparison.imageFunctor G σ ⊣ rightOrder adj σ :=
  Adjunction.mkOfHomEquiv {
    homEquiv := fun A B => {
      toFun := fun f => homOfLE ((order_galois adj σ A B).mp (leOfHom f))
      invFun := fun f => homOfLE ((order_galois adj σ A B).mpr (leOfHom f))
      left_inv := fun _ => Subsingleton.elim _ _
      right_inv := fun _ => Subsingleton.elim _ _ }
    homEquiv_naturality_left_symm := fun _ _ => Subsingleton.elim _ _
    homEquiv_naturality_right := fun _ _ => Subsingleton.elim _ _ }

end CategoricalEssentialIncompleteness.V46.DeductionSliceAdjunction
