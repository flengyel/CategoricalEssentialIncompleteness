/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SentenceTheoryClosure
public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Category.Preorder

/-! # Generation and closed sentence theories

A family of initial finite-derivation algebras determines a closure on
sentence subobjects. Generation is left adjoint to inclusion of the closed
subobjects, regarded as categories with their inclusion morphisms.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u

open CategoryTheory CategoryTheory.Limits

namespace CategoricalEssentialIncompleteness.V46.FirstOrderGeneration

variable {D : Type u} [Category.{v} D] [Regular D] [HasFiniteCoproducts D]
variable {V F L S : D}
variable {logical : L ⟶ F} {sentence : S ⟶ F}
variable {all : V ⨯ F ⟶ F} {imp : F ⨯ F ⟶ F}
variable (proofs : {A : D} → (a : A ⟶ S) →
  Endofunctor.Algebra (firstOrderRules logical sentence a all imp).inference)
variable (proofInitial : ∀ {A : D} (a : A ⟶ S), IsInitial (proofs a))

/-- The conclusion morphism restricted to sentence conclusions. -/
def conclusion {A : D} (a : A ⟶ S) :
    pullback (proofs a).a.hom sentence ⟶ S :=
  pullback.snd (proofs a).a.hom sentence

def theory {A : D} (a : A ⟶ S) : Subobject S :=
  imageSubobject (conclusion proofs a)

/-- A sentence subobject is closed if every finite derivation from its
sentences has its sentence conclusion in that subobject. -/
def IsClosed (B : Subobject S) : Prop :=
  ∃ w : pullback (proofs B.arrow).a.hom sentence ⟶ Subobject.underlying.obj B,
    w ≫ B.arrow = conclusion proofs B.arrow

def axiomProof {A : D} (a : A ⟶ S) : A ⟶ (proofs a).a.left :=
  coprod.inr ≫
    (firstOrderRules logical sentence a all imp).nullaryToProof (proofs a)

@[reassoc] theorem axiomProof_conclusion {A : D} (a : A ⟶ S) :
    axiomProof proofs a ≫ (proofs a).a.hom = a ≫ sentence := by
  rw [axiomProof, Category.assoc, RulePresentation.nullaryToProof_conclusion]
  exact coprod.inr_desc _ _

def axiomImage {A : D} (a : A ⟶ S) : A ⟶ image (conclusion proofs a) :=
  pullback.lift (axiomProof proofs a) a (axiomProof_conclusion proofs a) ≫
    factorThruImage (conclusion proofs a)

@[reassoc] theorem axiomImage_over {A : D} (a : A ⟶ S) :
    axiomImage proofs a ≫ image.ι (conclusion proofs a) = a := by
  unfold axiomImage
  rw [Category.assoc, image.fac]
  exact pullback.lift_snd _ _ _

theorem axioms_factor {A : D} (a : A ⟶ S) :
    ∃ k : A ⟶ image (conclusion proofs a),
      k ≫ image.ι (conclusion proofs a) = a :=
  ⟨axiomImage proofs a, axiomImage_over proofs a⟩

include proofInitial in
theorem theory_monotone {A B : D} (a : A ⟶ S) (b : B ⟶ S)
    (k : A ⟶ B) (hk : k ≫ b = a) : theory proofs a ≤ theory proofs b :=
  firstOrder_sentence_image_monotone logical sentence a b all imp k hk
    (proofs a) (proofInitial a) (proofs b)

include proofInitial in
theorem theory_idempotent {A : D} (a : A ⟶ S) :
    theory proofs (image.ι (conclusion proofs a)) = theory proofs a := by
  let m := image.ι (conclusion proofs a)
  obtain ⟨w, hw⟩ := firstOrder_generated_sentence_closed logical sentence a all imp
    (proofs a) (proofInitial a) (proofs m) (proofInitial m)
  obtain ⟨k, hk⟩ := axioms_factor proofs m
  apply le_antisymm
  · exact imageSubobject_le_mk m (conclusion proofs m) w hw
  · exact Subobject.mk_le_mk_of_comm k hk

def generated (A : Subobject S) : Subobject S := theory proofs A.arrow

theorem axioms_le_generated (A : Subobject S) : A ≤ generated proofs A := by
  obtain ⟨k, hk⟩ := axioms_factor proofs A.arrow
  simpa only [Subobject.mk_arrow, generated, theory] using
    Subobject.mk_le_mk_of_comm k hk

include proofInitial in
theorem theory_closed {A : D} (a : A ⟶ S) : IsClosed proofs (theory proofs a) := by
  let c := conclusion proofs a
  let m := (theory proofs a).arrow
  have hi : (imageSubobjectIso c).hom ≫ image.ι c = m := imageSubobject_arrow c
  have hle := theory_monotone proofs proofInitial m (image.ι c) (imageSubobjectIso c).hom hi
  rw [theory_idempotent proofs proofInitial] at hle
  have hm : theory proofs m ≤ Subobject.mk m := by
    simpa only [m, Subobject.mk_arrow] using hle
  let c' := conclusion proofs m
  let e := Subobject.ofMkLEMk (image.ι c') m hm
  refine ⟨factorThruImage c' ≫ e, ?_⟩
  rw [Category.assoc, Subobject.ofMkLEMk_comp, image.fac]

include proofInitial in
theorem generated_closed (A : Subobject S) : IsClosed proofs (generated proofs A) :=
  theory_closed proofs proofInitial A.arrow

include proofInitial in
theorem theory_least {A : D} (a : A ⟶ S) (B : Subobject S)
    (hB : IsClosed proofs B) (k : A ⟶ Subobject.underlying.obj B)
    (hk : k ≫ B.arrow = a) : theory proofs a ≤ B := by
  obtain ⟨w, hw⟩ := hB
  have h := firstOrder_generated_sentence_least logical sentence a all imp
    (proofs a) (proofInitial a) B.arrow (proofs B.arrow) k hk w hw
  simpa only [theory, conclusion, Subobject.mk_arrow] using h

include proofInitial in
theorem generated_least (A B : Subobject S) (hB : IsClosed proofs B) (hAB : A ≤ B) :
    generated proofs A ≤ B :=
  theory_least proofs proofInitial A.arrow B hB
    (Subobject.ofLE A B hAB) (Subobject.ofLE_arrow hAB)

include proofInitial in
theorem generated_monotone : Monotone (generated proofs) := by
  intro A B hAB
  exact theory_monotone proofs proofInitial A.arrow B.arrow
    (Subobject.ofLE A B hAB) (Subobject.ofLE_arrow hAB)

include proofInitial in
theorem generated_idempotent (A : Subobject S) :
    generated proofs (generated proofs A) = generated proofs A :=
  le_antisymm
    (generated_least proofs proofInitial _ _ (generated_closed proofs proofInitial A) le_rfl)
    (axioms_le_generated proofs (generated proofs A))

include proofInitial in
theorem generated_le_iff (A B : Subobject S) (hB : IsClosed proofs B) :
    generated proofs A ≤ B ↔ A ≤ B :=
  ⟨fun h => (axioms_le_generated proofs A).trans h,
    generated_least proofs proofInitial A B hB⟩

abbrev ClosedTheory := {B : Subobject S // IsClosed proofs B}

def inclusion : ClosedTheory proofs ⥤ Subobject S where
  obj B := B.val
  map h := homOfLE (leOfHom h)

def generation : Subobject S ⥤ ClosedTheory proofs where
  obj A := ⟨generated proofs A, generated_closed proofs proofInitial A⟩
  map h := homOfLE (generated_monotone proofs proofInitial (leOfHom h))

include proofInitial in
/-- The order adjunction for the closure obtained from finite derivations. -/
theorem generation_galois :
    GaloisConnection (fun A => (generation proofs proofInitial).obj A)
      (fun B => (inclusion proofs).obj B) := by
  intro A B
  exact generated_le_iff proofs proofInitial A B.val B.property

def homEquiv (A : Subobject S) (B : ClosedTheory proofs) :
    ((generation proofs proofInitial).obj A ⟶ B) ≃
      (A ⟶ (inclusion proofs).obj B) where
  toFun h := homOfLE ((generation_galois proofs proofInitial A B).mp (leOfHom h))
  invFun h := homOfLE ((generation_galois proofs proofInitial A B).mpr (leOfHom h))
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _

/-- Generation is left adjoint to inclusion of the closed sentence theories. -/
def adjunction : generation proofs proofInitial ⊣ inclusion proofs :=
  Adjunction.mkOfHomEquiv {
    homEquiv := homEquiv proofs proofInitial
    homEquiv_naturality_left_symm := fun _ _ => Subsingleton.elim _ _
    homEquiv_naturality_right := fun _ _ => Subsingleton.elim _ _ }

/-- A morphism to a monic sentence presentation is determined by its
composite with the inclusion in the sentence object. -/
theorem presentation_hom_ext {A : Over S} {B : ClosedTheory proofs}
    (f g : A ⟶ Over.mk B.val.arrow) : f = g := by
  apply Over.OverMorphism.ext
  apply (cancel_mono B.val.arrow).mp
  exact (Over.w f).trans (Over.w g).symm

def presentationInclusion : ClosedTheory proofs ⥤ Over S where
  obj B := Over.mk B.val.arrow
  map {B C} h := Over.homMk (Subobject.ofLE B.val C.val (leOfHom h))
    (Subobject.ofLE_arrow (leOfHom h))
  map_id _ := presentation_hom_ext proofs _ _
  map_comp _ _ := presentation_hom_ext proofs _ _

def presentationGeneration : Over S ⥤ ClosedTheory proofs where
  obj A := ⟨theory proofs A.hom, theory_closed proofs proofInitial A.hom⟩
  map h := homOfLE (theory_monotone proofs proofInitial _ _ h.left (Over.w h))

def presentationHomEquiv (A : Over S) (B : ClosedTheory proofs) :
    ((presentationGeneration proofs proofInitial).obj A ⟶ B) ≃
      (A ⟶ (presentationInclusion proofs).obj B) where
  toFun h := by
    let c := conclusion proofs A.hom
    have hle : Subobject.mk (image.ι c) ≤ Subobject.mk B.val.arrow := by
      rw [Subobject.mk_arrow]
      change theory proofs A.hom ≤ B.val
      exact leOfHom h
    let k := Subobject.ofMkLEMk (image.ι c) B.val.arrow hle
    refine Over.homMk (axiomImage proofs A.hom ≫ k) ?_
    change (axiomImage proofs A.hom ≫ k) ≫ B.val.arrow = A.hom
    dsimp only [k]
    rw [Category.assoc, Subobject.ofMkLEMk_comp, axiomImage_over]
  invFun h := homOfLE (theory_least proofs proofInitial A.hom B.val B.property
    h.left (Over.w h))
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := presentation_hom_ext proofs _ _

/-- Generation also reflects arbitrary total axiom presentations into
the closed sentence subobjects, with a natural hom-set bijection. -/
def presentationAdjunction :
    presentationGeneration proofs proofInitial ⊣ presentationInclusion proofs :=
  Adjunction.mkOfHomEquiv {
    homEquiv := presentationHomEquiv proofs proofInitial
    homEquiv_naturality_left_symm := fun _ _ => Subsingleton.elim _ _
    homEquiv_naturality_right := fun _ _ => presentation_hom_ext proofs _ _ }

end CategoricalEssentialIncompleteness.V46.FirstOrderGeneration
