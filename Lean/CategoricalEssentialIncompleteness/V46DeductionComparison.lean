/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46TranslationGalois

/-! # Comparison of generation under a change of category

Preservation of regular epimorphisms compares the images of axiom
presentations. The supplied sentence-derivation morphisms then give the
generation identities and the restriction of a subobject adjunction.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v₁ v₂ u₁ u₂

open CategoryTheory CategoryTheory.Limits

namespace CategoricalEssentialIncompleteness.V46.DeductionComparison

variable {D₁ : Type u₁} {D₂ : Type u₂}
variable [Category.{v₁} D₁] [Category.{v₂} D₂] [Regular D₁] [Regular D₂]

theorem regular_epi_image {X Y Z : D₂} (e : X ⟶ Y) [IsRegularEpi e] (f : Y ⟶ Z) :
    imageSubobject (e ≫ f) = imageSubobject f := by
  apply le_antisymm (imageSubobject_comp_le e f)
  let sq : CommSq (factorThruImage (e ≫ f)) e (image.ι (e ≫ f)) f := ⟨image.fac _⟩
  exact imageSubobject_le_mk (image.ι (e ≫ f)) f sq.lift sq.fac_right

variable (G : D₁ ⥤ D₂) {S₁ : D₁} {S₂ : D₂} (σ : G.obj S₁ ⟶ S₂)

def imageObject (A : Subobject S₁) : Subobject S₂ := imageSubobject (G.map A.arrow ≫ σ)

omit [Regular D₁] in
theorem image_monotone : Monotone (imageObject G σ) := by
  intro A B h
  have w : G.map (Subobject.ofLE A B h) ≫ (G.map B.arrow ≫ σ) = G.map A.arrow ≫ σ := by
    rw [← Category.assoc, ← G.map_comp, Subobject.ofLE_arrow]
  exact imageSubobject_le_mk (image.ι (G.map B.arrow ≫ σ)) (G.map A.arrow ≫ σ)
    (G.map (Subobject.ofLE A B h) ≫ factorThruImage (G.map B.arrow ≫ σ))
    (by rw [Category.assoc, image.fac, w])

def imageFunctor : Subobject S₁ ⥤ Subobject S₂ where
  obj := imageObject G σ
  map f := homOfLE (image_monotone G σ (leOfHom f))

def presentationFunctor : Over S₁ ⥤ Over S₂ where
  obj a := Over.mk (G.map a.hom ≫ σ)
  map {X Y} f := Over.homMk (G.map f.left) (by
    change G.map f.left ≫ (G.map Y.hom ≫ σ) = G.map X.hom ≫ σ
    rw [← Category.assoc, ← G.map_comp, Over.w f])
  map_id _ := by apply Over.OverMorphism.ext; exact G.map_id _
  map_comp f g := by apply Over.OverMorphism.ext; exact G.map_comp f.left g.left

variable (regularEpis : ∀ {X Y : D₁} (f : X ⟶ Y), IsRegularEpi f → IsRegularEpi (G.map f))

include regularEpis in
theorem image_presentation {A : D₁} (a : A ⟶ S₁) :
    imageSubobject (G.map a ≫ σ) = imageObject G σ (imageSubobject a) := by
  let e := factorThruImageSubobject a
  have he : IsRegularEpi e := by dsimp [e, factorThruImageSubobject]; infer_instance
  have := regularEpis e he
  have w : G.map a ≫ σ = G.map e ≫ (G.map (imageSubobject a).arrow ≫ σ) := by
    rw [← Category.assoc, ← G.map_comp]
    dsimp only [e]
    rw [imageSubobject_arrow_comp]
  calc
    imageSubobject (G.map a ≫ σ) =
        imageSubobject (G.map e ≫ (G.map (imageSubobject a).arrow ≫ σ)) :=
      congrArg (fun f : G.obj A ⟶ S₂ => imageSubobject f) w
    _ = imageObject G σ (imageSubobject a) := regular_epi_image _ _

section Presentations

variable [FinitaryExtensive D₁] [FinitaryExtensive D₂]
variable {V₁ : D₁} {V₂ : D₂}
variable (P : FirstOrderPresentation V₁) (Q : FirstOrderPresentation V₂)
variable (σ : G.obj P.syntaxData.sentenceObject ⟶ Q.syntaxData.sentenceObject)

variable (proofMap : ∀ A : Subobject P.syntaxData.sentenceObject,
  G.obj (pullback (P.proofs A).a.hom P.syntaxData.sentenceInclusion) ⟶
    pullback (Q.proofs (imageObject G σ A)).a.hom Q.syntaxData.sentenceInclusion)
variable (proofConclusion : ∀ A,
  proofMap A ≫ FirstOrderReflection.conclusion Q.proofs (imageObject G σ A) =
    G.map (FirstOrderReflection.conclusion P.proofs A) ≫ σ)

include regularEpis proofConclusion in
theorem generation_bound (A : Subobject P.syntaxData.sentenceObject) :
    imageObject G σ (FirstOrderReflection.generated P.proofs A) ≤
      FirstOrderReflection.generated Q.proofs (imageObject G σ A) := by
  change imageObject G σ (imageSubobject (FirstOrderReflection.conclusion P.proofs A)) ≤ _
  calc
    imageObject G σ (imageSubobject (FirstOrderReflection.conclusion P.proofs A)) =
        imageSubobject (G.map (FirstOrderReflection.conclusion P.proofs A) ≫ σ) :=
      (image_presentation G σ regularEpis _).symm
    _ = imageSubobject (proofMap A ≫
        FirstOrderReflection.conclusion Q.proofs (imageObject G σ A)) :=
      congrArg (fun f => imageSubobject f) (proofConclusion A).symm
    _ ≤ FirstOrderReflection.generated Q.proofs (imageObject G σ A) :=
      imageSubobject_comp_le _ _

def theoryFunctor : P.Theories ⥤ Q.Theories where
  obj T := ⟨FirstOrderReflection.generated Q.proofs (imageObject G σ T.val),
    FirstOrderReflection.idempotent Q.proofs Q.initial _⟩
  map f := homOfLE (FirstOrderReflection.monotone Q.proofs Q.initial
    (image_monotone G σ (leOfHom f)))

include regularEpis proofConclusion in
theorem generation_identity (A : Subobject P.syntaxData.sentenceObject) :
    FirstOrderReflection.generated Q.proofs
        (imageObject G σ (FirstOrderReflection.generated P.proofs A)) =
      FirstOrderReflection.generated Q.proofs (imageObject G σ A) := by
  apply le_antisymm
  · simpa only [FirstOrderReflection.idempotent Q.proofs Q.initial] using
      FirstOrderReflection.monotone Q.proofs Q.initial
        (generation_bound G regularEpis P Q σ proofMap proofConclusion A)
  · exact FirstOrderReflection.monotone Q.proofs Q.initial
      (image_monotone G σ (FirstOrderReflection.extensive P.proofs A))

include regularEpis proofConclusion in
theorem generation_square :
    FirstOrderReflection.generation P.proofs P.initial ⋙ theoryFunctor G P Q σ =
      imageFunctor G σ ⋙ FirstOrderReflection.generation Q.proofs Q.initial :=
  CategoryTheory.Functor.ext (fun A => Subtype.ext
    (generation_identity G regularEpis P Q σ proofMap proofConclusion A))

include regularEpis proofConclusion in
theorem presentation_square :
    presentationFunctor G σ ⋙ FirstOrderReflection.presentationGeneration Q.proofs Q.initial =
      FirstOrderReflection.presentationGeneration P.proofs P.initial ⋙ theoryFunctor G P Q σ := by
  refine CategoryTheory.Functor.ext (fun a => ?_) (fun _ _ _ => Subsingleton.elim _ _)
  apply Subtype.ext
  change FirstOrderReflection.generated Q.proofs (imageSubobject (G.map a.hom ≫ σ)) = _
  rw [image_presentation G σ regularEpis]
  exact (generation_identity G regularEpis P Q σ proofMap proofConclusion _).symm

def inclusionComparison :
    FirstOrderReflection.presentationInclusion P.proofs ⋙ presentationFunctor G σ ⟶
      theoryFunctor G P Q σ ⋙ FirstOrderReflection.presentationInclusion Q.proofs where
  app T := Over.homMk
    (factorThruImageSubobject (G.map T.val.arrow ≫ σ) ≫
      Subobject.ofLE _ _ (FirstOrderReflection.extensive Q.proofs (imageObject G σ T.val)))
    (by
      change (_ ≫ Subobject.ofLE _ _ _) ≫
        (FirstOrderReflection.generated Q.proofs (imageObject G σ T.val)).arrow = _
      rw [Category.assoc, Subobject.ofLE_arrow, imageSubobject_arrow_comp]
      rfl)
  naturality {X Y} f := FirstOrderReflection.presentation_hom_ext Q.proofs
    (T := (theoryFunctor G P Q σ).obj Y) _ _

variable (R : Subobject Q.syntaxData.sentenceObject ⥤ Subobject P.syntaxData.sentenceObject)
variable (hR : imageFunctor G σ ⊣ R)

include regularEpis proofConclusion hR in
theorem right_closed (B : Q.Theories) :
    FirstOrderReflection.generated P.proofs (R.obj B.val) = R.obj B.val := by
  have hc : imageObject G σ (R.obj B.val) ≤ B.val := leOfHom (hR.counit.app B.val)
  have h := (generation_bound G regularEpis P Q σ proofMap proofConclusion (R.obj B.val)).trans
    (FirstOrderReflection.monotone Q.proofs Q.initial hc)
  rw [B.property] at h
  exact le_antisymm ((hR.gc _ _).mp h) (FirstOrderReflection.extensive P.proofs _)

def restrictedRight : Q.Theories ⥤ P.Theories where
  obj B := ⟨R.obj B.val, right_closed G regularEpis P Q σ proofMap proofConclusion R hR B⟩
  map f := homOfLE (leOfHom (R.map (homOfLE (leOfHom f))))

def restrictedAdjunction : theoryFunctor G P Q σ ⊣
    restrictedRight G regularEpis P Q σ proofMap proofConclusion R hR :=
  Adjunction.mkOfHomEquiv {
    homEquiv := fun _A B => {
      toFun := fun f => homOfLE ((hR.gc _ _).mp
        ((FirstOrderReflection.generated_le_iff Q.proofs Q.initial _ B).mp (leOfHom f)))
      invFun := fun f => homOfLE ((FirstOrderReflection.generated_le_iff Q.proofs Q.initial _ B).mpr
        ((hR.gc _ _).mpr (leOfHom f)))
      left_inv := fun _ => Subsingleton.elim _ _
      right_inv := fun _ => Subsingleton.elim _ _ }
    homEquiv_naturality_left_symm := fun _ _ => Subsingleton.elim _ _
    homEquiv_naturality_right := fun _ _ => Subsingleton.elim _ _ }

end Presentations
end CategoricalEssentialIncompleteness.V46.DeductionComparison
