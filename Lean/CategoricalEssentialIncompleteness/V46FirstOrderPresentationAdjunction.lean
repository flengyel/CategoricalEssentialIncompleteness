/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46FirstOrderGeneration
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-! # Generation into closed monic sentence presentations

The target retains every monic presentation, including its carrier, rather
than choosing a representative of its sentence subobject.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u

open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.FirstOrderGeneration

namespace CategoricalEssentialIncompleteness.V46.FirstOrderPresentations

variable {D : Type u} [Category.{v} D] [Regular D] [HasFiniteCoproducts D]
variable {V F L S : D}
variable {logical : L ⟶ F} {sentence : S ⟶ F}
variable {all : V ⨯ F ⟶ F} {imp : F ⨯ F ⟶ F}
variable (proofs : {A : D} → (a : A ⟶ S) →
  Endofunctor.Algebra (firstOrderRules logical sentence a all imp).inference)
variable (proofInitial : ∀ {A : D} (a : A ⟶ S), IsInitial (proofs a))

def Closed : ObjectProperty (Over S) := fun B =>
  Mono B.hom ∧ ∃ w : pullback (proofs B.hom).a.hom sentence ⟶ B.left,
    w ≫ B.hom = conclusion proofs B.hom

abbrev TheoryCategory := (Closed proofs).FullSubcategory

theorem mono (B : TheoryCategory proofs) : Mono B.obj.hom := B.property.1

@[implicit_reducible]
def inclusion : TheoryCategory proofs ⥤ Over S := (Closed proofs).ι

instance inclusion_full : (inclusion proofs).Full :=
  inferInstanceAs ((Closed proofs).ι.Full)

instance inclusion_faithful : (inclusion proofs).Faithful :=
  inferInstanceAs ((Closed proofs).ι.Faithful)

omit [Regular D] [HasFiniteCoproducts D] in
theorem over_hom_ext {A B : Over S} [Mono B.hom] (f g : A ⟶ B) : f = g := by
  apply Over.OverMorphism.ext
  apply (cancel_mono B.hom).mp
  exact (Over.w f).trans (Over.w g).symm

theorem hom_ext {A B : TheoryCategory proofs} (f g : A ⟶ B) : f = g := by
  let _ : Mono B.obj.hom := B.property.1
  apply ObjectProperty.hom_ext
  exact over_hom_ext f.hom g.hom

theorem target_hom_ext {A : Over S} {B : TheoryCategory proofs}
    (f g : A ⟶ B.obj) : f = g := by
  let _ : Mono B.obj.hom := B.property.1
  exact over_hom_ext f g

def generatedObject (A : Over S) : TheoryCategory proofs :=
  ⟨Over.mk (image.ι (conclusion proofs A.hom)),
    by change Mono (image.ι (conclusion proofs A.hom)); infer_instance,
    firstOrder_generated_sentence_closed logical sentence A.hom all imp
      (proofs A.hom) (proofInitial A.hom)
      (proofs (image.ι (conclusion proofs A.hom)))
      (proofInitial (image.ι (conclusion proofs A.hom)))⟩

def imageMap {A B : Over S} (f : A ⟶ B) :
    image (conclusion proofs A.hom) ⟶ image (conclusion proofs B.hom) :=
  Subobject.ofMkLEMk (image.ι (conclusion proofs A.hom))
    (image.ι (conclusion proofs B.hom))
    (theory_monotone proofs proofInitial A.hom B.hom f.left (Over.w f))

@[reassoc] theorem imageMap_over {A B : Over S} (f : A ⟶ B) :
    imageMap proofs proofInitial f ≫ image.ι (conclusion proofs B.hom) =
      image.ι (conclusion proofs A.hom) :=
  Subobject.ofMkLEMk_comp _

def generation : Over S ⥤ TheoryCategory proofs where
  obj := generatedObject proofs proofInitial
  map f := ObjectProperty.homMk
    (Over.homMk (imageMap proofs proofInitial f) (imageMap_over proofs proofInitial f))
  map_id _ := hom_ext proofs _ _
  map_comp _ _ := hom_ext proofs _ _

def homEquiv (A : Over S) (B : TheoryCategory proofs) :
    ((generation proofs proofInitial).obj A ⟶ B) ≃
      (A ⟶ (inclusion proofs).obj B) where
  toFun h := by
    refine Over.homMk (axiomImage proofs A.hom ≫ h.hom.left) ?_
    change (axiomImage proofs A.hom ≫ h.hom.left) ≫ B.obj.hom = A.hom
    rw [Category.assoc, Over.w h.hom]
    exact axiomImage_over proofs A.hom
  invFun h := by
    letI : Mono B.obj.hom := B.property.1
    have hle : imageSubobject (conclusion proofs A.hom) ≤ Subobject.mk B.obj.hom := by
      obtain ⟨w, hw⟩ := B.property.2
      exact firstOrder_generated_sentence_least logical sentence A.hom all imp
        (proofs A.hom) (proofInitial A.hom) B.obj.hom (proofs B.obj.hom)
        h.left (Over.w h) w hw
    exact ObjectProperty.homMk (Over.homMk
      (Subobject.ofMkLEMk (image.ι (conclusion proofs A.hom)) B.obj.hom hle)
      (Subobject.ofMkLEMk_comp hle))
  left_inv _ := hom_ext proofs _ _
  right_inv _ := target_hom_ext proofs _ _

/-- Generation reflects arbitrary axiom presentations into the full
subcategory of closed monic sentence presentations. -/
def adjunction : generation proofs proofInitial ⊣ inclusion proofs :=
  Adjunction.mkOfHomEquiv {
    homEquiv := homEquiv proofs proofInitial
    homEquiv_naturality_left_symm := fun _ _ => hom_ext proofs _ _
    homEquiv_naturality_right := fun _ _ => target_hom_ext proofs _ _ }

end CategoricalEssentialIncompleteness.V46.FirstOrderPresentations
