/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46FirstOrderPresentationAdjunction

/-! # Reflection into sentence theories

Only axiom subobjects require initial derivation algebras. An arbitrary
total presentation is first replaced by its regular image.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u

open CategoryTheory CategoryTheory.Limits

namespace CategoricalEssentialIncompleteness.V46.FirstOrderReflection

variable {D : Type u} [Category.{v} D] [Regular D] [HasFiniteCoproducts D]
variable {V F L S : D}
variable {logical : L ⟶ F} {sentence : S ⟶ F}
variable {all : V ⨯ F ⟶ F} {imp : F ⨯ F ⟶ F}
variable (proofs : (A : Subobject S) →
  Endofunctor.Algebra (firstOrderRules logical sentence A.arrow all imp).inference)
variable (proofInitial : ∀ A, IsInitial (proofs A))

def formulaTheory (A : Subobject S) : Subobject F := imageSubobject (proofs A).a.hom

def conclusion (A : Subobject S) : pullback (proofs A).a.hom sentence ⟶ S :=
  pullback.snd (proofs A).a.hom sentence

def generated (A : Subobject S) : Subobject S := imageSubobject (conclusion proofs A)

theorem generated_eq_pullback (A : Subobject S) :
    generated proofs A = (Subobject.pullback sentence).obj (formulaTheory proofs A) :=
  sentenceImage_subobject (proofs A).a.hom sentence

def axiomProof (A : Subobject S) : (A : D) ⟶ (proofs A).a.left :=
  coprod.inr ≫
    (firstOrderRules logical sentence A.arrow all imp).nullaryToProof (proofs A)

@[reassoc] theorem axiomProof_conclusion (A : Subobject S) :
    axiomProof proofs A ≫ (proofs A).a.hom = A.arrow ≫ sentence := by
  rw [axiomProof, Category.assoc, RulePresentation.nullaryToProof_conclusion]
  exact coprod.inr_desc _ _

theorem extensive (A : Subobject S) : A ≤ generated proofs A := by
  let k := pullback.lift (axiomProof proofs A) A.arrow (axiomProof_conclusion proofs A)
  simpa only [generated, Subobject.mk_arrow] using
    (Subobject.le_mk_of_comm (k ≫ factorThruImage (conclusion proofs A))
      (by simp [k, conclusion, Category.assoc]))

include proofInitial in
theorem monotone : Monotone (generated proofs) := by
  intro A B h
  exact firstOrder_sentence_image_monotone logical sentence A.arrow B.arrow all imp
    (Subobject.ofLE A B h) (Subobject.ofLE_arrow h)
    (proofs A) (proofInitial A) (proofs B)

include proofInitial in
theorem formula_closed (A : Subobject S) :
    ClosedUnder (firstOrderRules logical sentence A.arrow all imp).inference
      (image.ι (proofs A).a.hom) :=
  (firstOrder_least_image logical sentence A.arrow all imp (proofs A) (proofInitial A)).1

include proofInitial in
theorem generated_le_of_formula_factor (A B : Subobject S)
    (k : (B : D) ⟶ image (proofs A).a.hom)
    (hk : k ≫ image.ι (proofs A).a.hom = B.arrow ≫ sentence) :
    generated proofs B ≤ generated proofs A := by
  have hc := firstOrder_closed_reaxiomatize logical sentence A.arrow B.arrow all imp
    (image.ι (proofs A).a.hom) (formula_closed proofs proofInitial A) k hk
  obtain ⟨f, hf⟩ := (firstOrder_least_image logical sentence B.arrow all imp
    (proofs B) (proofInitial B)).2 (image.ι (proofs A).a.hom) hc
  rw [generated_eq_pullback, generated_eq_pullback]
  exact leOfHom ((Subobject.pullback sentence).map (homOfLE
    (Subobject.mk_le_mk_of_comm f hf)))

include proofInitial in
theorem idempotent (A : Subobject S) :
    generated proofs (generated proofs A) = generated proofs A := by
  apply le_antisymm
  · let k : (generated proofs A : D) ⟶ image (proofs A).a.hom :=
      (imageSubobjectIso (conclusion proofs A)).hom ≫
        sentenceImageToFormula (proofs A).a.hom sentence
    apply generated_le_of_formula_factor proofs proofInitial A (generated proofs A) k
    dsimp only [k]
    rw [Category.assoc, sentenceImageToFormula_over, ← Category.assoc]
    exact congrArg (fun h => h ≫ sentence) (imageSubobject_arrow (conclusion proofs A))
  · exact extensive proofs (generated proofs A)

abbrev Theory := {T : Subobject S // generated proofs T = T}

def inclusion : Theory proofs ⥤ Subobject S where
  obj T := T.val
  map f := homOfLE (leOfHom f)

include proofInitial in
theorem generated_le_iff (A : Subobject S) (T : Theory proofs) :
    generated proofs A ≤ T.val ↔ A ≤ T.val := by
  refine ⟨fun h => (extensive proofs A).trans h, fun h => ?_⟩
  simpa only [T.property] using monotone proofs proofInitial h

def generation : Subobject S ⥤ Theory proofs where
  obj A := ⟨generated proofs A, idempotent proofs proofInitial A⟩
  map f := homOfLE (monotone proofs proofInitial (leOfHom f))

def homEquiv (A : Subobject S) (T : Theory proofs) :
    ((generation proofs proofInitial).obj A ⟶ T) ≃
      (A ⟶ (inclusion proofs).obj T) where
  toFun f := homOfLE ((generated_le_iff proofs proofInitial A T).mp (leOfHom f))
  invFun f := homOfLE ((generated_le_iff proofs proofInitial A T).mpr (leOfHom f))
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _

def adjunction : generation proofs proofInitial ⊣ inclusion proofs :=
  Adjunction.mkOfHomEquiv {
    homEquiv := homEquiv proofs proofInitial
    homEquiv_naturality_left_symm := fun _ _ => Subsingleton.elim _ _
    homEquiv_naturality_right := fun _ _ => Subsingleton.elim _ _ }

theorem presentation_hom_ext {A : Over S} {T : Theory proofs}
    (f g : A ⟶ Over.mk T.val.arrow) : f = g := by
  apply Over.OverMorphism.ext
  apply (cancel_mono T.val.arrow).mp
  exact (Over.w f).trans (Over.w g).symm

@[implicit_reducible]
def presentationInclusion : Theory proofs ⥤ Over S where
  obj T := Over.mk T.val.arrow
  map {T U} f := Over.homMk (Subobject.ofLE T.val U.val (leOfHom f))
    (Subobject.ofLE_arrow (leOfHom f))
  map_id _ := presentation_hom_ext proofs _ _
  map_comp _ _ := presentation_hom_ext proofs _ _

omit [HasFiniteCoproducts D] in
theorem image_monotone {A B : Over S} (f : A ⟶ B) :
    imageSubobject A.hom ≤ imageSubobject B.hom := by
  rw [← Over.w f]
  exact imageSubobject_comp_le f.left B.hom

/-- The object action is the formula printed for Γ: generate the image
of the axiom presentation. No derivation algebra for that presentation
is required. -/
def presentationGeneration : Over S ⥤ Theory proofs where
  obj A := ⟨generated proofs (imageSubobject A.hom),
    idempotent proofs proofInitial (imageSubobject A.hom)⟩
  map f := homOfLE (monotone proofs proofInitial (image_monotone f))

theorem presentationGeneration_obj (A : Over S) :
    ((presentationGeneration proofs proofInitial).obj A).val =
      generated proofs (imageSubobject A.hom) := rfl

def presentationHomEquiv (A : Over S) (T : Theory proofs) :
    ((presentationGeneration proofs proofInitial).obj A ⟶ T) ≃
      (A ⟶ (presentationInclusion proofs).obj T) where
  toFun f := by
    let h := (generated_le_iff proofs proofInitial (imageSubobject A.hom) T).mp (leOfHom f)
    refine Over.homMk (factorThruImageSubobject A.hom ≫
      Subobject.ofLE (imageSubobject A.hom) T.val h) ?_
    change (factorThruImageSubobject A.hom ≫
      Subobject.ofLE (imageSubobject A.hom) T.val h) ≫ T.val.arrow = A.hom
    rw [Category.assoc, Subobject.ofLE_arrow, imageSubobject_arrow_comp]
  invFun f := by
    apply homOfLE
    apply (generated_le_iff proofs proofInitial (imageSubobject A.hom) T).mpr
    simpa only [Subobject.mk_arrow] using
      imageSubobject_le_mk T.val.arrow A.hom f.left (Over.w f)
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := presentation_hom_ext proofs _ _

def presentationAdjunction :
    presentationGeneration proofs proofInitial ⊣ presentationInclusion proofs :=
  Adjunction.mkOfHomEquiv {
    homEquiv := presentationHomEquiv proofs proofInitial
    homEquiv_naturality_left_symm := fun _ _ => Subsingleton.elim _ _
    homEquiv_naturality_right := fun _ _ => presentation_hom_ext proofs _ _ }

section PresentationComparison

variable (presentations : {A : D} → (a : A ⟶ S) →
  Endofunctor.Algebra (firstOrderRules logical sentence a all imp).inference)
variable (presentationInitial : ∀ {A : D} (a : A ⟶ S), IsInitial (presentations a))

theorem generated_comparison (A : Subobject S) :
    generated (fun B => presentations B.arrow) A =
      FirstOrderGeneration.generated presentations A := rfl

include presentationInitial in
theorem fixed_iff_closed (A : Subobject S) :
    generated (fun B => presentations B.arrow) A = A ↔
      FirstOrderGeneration.IsClosed presentations A := by
  change FirstOrderGeneration.generated presentations A = A ↔ _
  constructor
  · intro h
    rw [← h]
    exact FirstOrderGeneration.generated_closed presentations presentationInitial A
  · intro h
    exact le_antisymm
      (FirstOrderGeneration.generated_least presentations presentationInitial A A h le_rfl)
      (FirstOrderGeneration.axioms_le_generated presentations A)

include presentationInitial in
theorem presentation_generated_comparison {A : D} (a : A ⟶ S) :
    FirstOrderGeneration.theory presentations a =
      generated (fun B => presentations B.arrow) (imageSubobject a) := by
  change FirstOrderGeneration.theory presentations a =
    FirstOrderGeneration.generated presentations (imageSubobject a)
  apply le_antisymm
  · let h := FirstOrderGeneration.axioms_le_generated presentations (imageSubobject a)
    apply FirstOrderGeneration.theory_least presentations presentationInitial a _
      (FirstOrderGeneration.generated_closed presentations presentationInitial _)
      (factorThruImageSubobject a ≫ Subobject.ofLE _ _ h)
    rw [Category.assoc, Subobject.ofLE_arrow, imageSubobject_arrow_comp]
  · apply FirstOrderGeneration.generated_least presentations presentationInitial _ _
      (FirstOrderGeneration.theory_closed presentations presentationInitial a)
    exact imageSubobject_le_mk (image.ι (FirstOrderGeneration.conclusion presentations a))
      a (FirstOrderGeneration.axiomImage presentations a)
      (FirstOrderGeneration.axiomImage_over presentations a)

end PresentationComparison

end CategoricalEssentialIncompleteness.V46.FirstOrderReflection
