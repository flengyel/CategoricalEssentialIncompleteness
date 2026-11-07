/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46CategoricalSubstitution
import CategoricalEssentialIncompleteness.V46ArithmeticIndexedFibersAlgebraSplit
import Mathlib.CategoryTheory.Comma.Over.Pullback

/-! # The proved extensive slice decomposition used by numeral fibers

Morphisms are reconstructed by actual coproduct-fiber case analysis.
Fullness, faithfulness and essential surjectivity are proved explicitly.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness.V46.ArithmeticIndexedFibers

section CoproductSlices
variable {D : Type u} [Category.{v} D] [Regular D] [FinitaryExtensive D]
variable (A B : D)

def splitSlice : Over (A ⨿ B) ⥤ Over A × Over B :=
  (Over.pullback (coprod.inl : A ⟶ A ⨿ B)).prod'
    (Over.pullback (coprod.inr : B ⟶ A ⨿ B))

instance splitSlice_faithful : (splitSlice A B).Faithful where
  map_injective {X Y} {f g} h := by
    apply Over.OverMorphism.ext
    apply BinaryCofan.IsColimit.hom_ext (SumFibers.isColimit X.hom)
    · have he := congrArg (fun k => k.1.left ≫ pullback.fst Y.hom
        (coprod.inl : A ⟶ A ⨿ B)) h
      simpa [splitSlice,Over.pullback] using he
    · have he := congrArg (fun k => k.2.left ≫ pullback.fst Y.hom
        (coprod.inr : B ⟶ A ⨿ B)) h
      simpa [splitSlice,Over.pullback] using he

def glueSliceHom {X Y : Over (A ⨿ B)}
    (f : (splitSlice A B).obj X ⟶ (splitSlice A B).obj Y) : X ⟶ Y :=
  Over.homMk (SumFibers.caseOf X.hom
    (f.1.left ≫ pullback.fst Y.hom (coprod.inl : A ⟶ A ⨿ B))
    (f.2.left ≫ pullback.fst Y.hom (coprod.inr : B ⟶ A ⨿ B))) (by
      apply BinaryCofan.IsColimit.hom_ext (SumFibers.isColimit X.hom)
      · have h₀ : f.1.left ≫ pullback.snd Y.hom (coprod.inl : A ⟶ A ⨿ B) =
          pullback.snd X.hom (coprod.inl : A ⟶ A ⨿ B) := Over.w f.1
        simp only [BinaryCofan.mk_inl]
        rw [← Category.assoc,SumFibers.inl_caseOf,Category.assoc,pullback.condition,
          ← Category.assoc,h₀]
        exact pullback.condition.symm
      · have h₁ : f.2.left ≫ pullback.snd Y.hom (coprod.inr : B ⟶ A ⨿ B) =
          pullback.snd X.hom (coprod.inr : B ⟶ A ⨿ B) := Over.w f.2
        simp only [BinaryCofan.mk_inr]
        rw [← Category.assoc,SumFibers.inr_caseOf,Category.assoc,pullback.condition,
          ← Category.assoc,h₁]
        exact pullback.condition.symm)

omit [Regular D] in
theorem splitSlice_glue {X Y : Over (A ⨿ B)}
    (f : (splitSlice A B).obj X ⟶ (splitSlice A B).obj Y) :
    (splitSlice A B).map (glueSliceHom A B f) = f := by
  apply Prod.ext
  · apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · simp [splitSlice,Over.pullback,glueSliceHom]
    · simpa [splitSlice,Over.pullback] using (Over.w f.1).symm
  · apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · simp [splitSlice,Over.pullback,glueSliceHom]
    · simpa [splitSlice,Over.pullback] using (Over.w f.2).symm

instance splitSlice_full : (splitSlice A B).Full where
  map_surjective f := ⟨glueSliceHom A B f,splitSlice_glue A B f⟩

omit [Regular D] in
theorem map_coprod_pullbacks (X : Over A) (Y : Over B) :
    IsPullback (coprod.inl : X.left ⟶ X.left ⨿ Y.left) X.hom
        (coprod.map X.hom Y.hom) (coprod.inl : A ⟶ A ⨿ B) ∧
      IsPullback (coprod.inr : Y.left ⟶ X.left ⨿ Y.left) Y.hom
        (coprod.map X.hom Y.hom) (coprod.inr : B ⟶ A ⨿ B) := by
  have hv := (BinaryCofan.isVanKampen_iff _).mp
    (FinitaryExtensive.vanKampen _ (coprodIsCoprod A B))
    (BinaryCofan.mk (coprod.inl : X.left ⟶ X.left ⨿ Y.left) coprod.inr)
  exact (hv X.hom Y.hom (coprod.map X.hom Y.hom)
    (by simp) (by simp)).mp ⟨coprodIsCoprod X.left Y.left⟩

instance splitSlice_essSurj : (splitSlice A B).EssSurj where
  mem_essImage X := by
    let Q : Over (A ⨿ B) := Over.mk (coprod.map X.1.hom X.2.hom)
    have h := map_coprod_pullbacks A B X.1 X.2
    let e₀ : X.1 ≅ ((splitSlice A B).obj Q).1 := by
      change X.1 ≅ Over.mk (pullback.snd (coprod.map X.1.hom X.2.hom) coprod.inl)
      exact Over.isoMk h.1.isoPullback (by simp)
    let e₁ : X.2 ≅ ((splitSlice A B).obj Q).2 := by
      change X.2 ≅ Over.mk (pullback.snd (coprod.map X.1.hom X.2.hom) coprod.inr)
      exact Over.isoMk h.2.isoPullback (by simp)
    exact ⟨Q,⟨Iso.prod e₀.symm e₁.symm⟩⟩

instance splitSlice_isEquivalence : (splitSlice A B).IsEquivalence := {}

/-- Finite extensivity gives the equivalence of the two actual pullback
slice functors, including all slice morphisms. -/
def coproductSliceEquivalence : Over (A ⨿ B) ≌ Over A × Over B :=
  (splitSlice A B).asEquivalence

section BaseIso
variable {C : D} (b : A ⨿ B ≅ C)

def splitOverIso : Over C ≌ Over A × Over B :=
  (Over.mapIso b.symm).trans (coproductSliceEquivalence A B)

def splitAtIso : Over C ⥤ Over A × Over B :=
  (Over.pullback ((coprod.inl : A ⟶ A ⨿ B) ≫ b.hom)).prod'
    (Over.pullback ((coprod.inr : B ⟶ A ⨿ B) ≫ b.hom))

omit [Regular D] in
private theorem firstBaseSquare (Q : Over C) :
    IsPullback (pullback.fst (Q.hom ≫ b.inv) (coprod.inl : A ⟶ A ⨿ B))
      (pullback.snd (Q.hom ≫ b.inv) (coprod.inl : A ⟶ A ⨿ B))
      Q.hom ((coprod.inl : A ⟶ A ⨿ B) ≫ b.hom) := by
  apply (IsPullback.of_hasPullback (Q.hom ≫ b.inv)
    (coprod.inl : A ⟶ A ⨿ B)).of_iso
      (Iso.refl _) (Iso.refl _) (Iso.refl _) b
  · simp
  · simp
  · simp
  · simp

omit [Regular D] in
private theorem secondBaseSquare (Q : Over C) :
    IsPullback (pullback.fst (Q.hom ≫ b.inv) (coprod.inr : B ⟶ A ⨿ B))
      (pullback.snd (Q.hom ≫ b.inv) (coprod.inr : B ⟶ A ⨿ B))
      Q.hom ((coprod.inr : B ⟶ A ⨿ B) ≫ b.hom) := by
  apply (IsPullback.of_hasPullback (Q.hom ≫ b.inv)
    (coprod.inr : B ⟶ A ⨿ B)).of_iso
      (Iso.refl _) (Iso.refl _) (Iso.refl _) b
  · simp
  · simp
  · simp
  · simp

def firstBaseIso (Q : Over C) :
    ((splitOverIso A B b).functor.obj Q).1 ≅ ((splitAtIso A B b).obj Q).1 :=
  by
    change Over.mk (pullback.snd (Q.hom ≫ b.inv) (coprod.inl : A ⟶ A ⨿ B)) ≅
      Over.mk (pullback.snd Q.hom ((coprod.inl : A ⟶ A ⨿ B) ≫ b.hom))
    exact Over.isoMk (firstBaseSquare A B b Q).isoPullback (by simp)

def secondBaseIso (Q : Over C) :
    ((splitOverIso A B b).functor.obj Q).2 ≅ ((splitAtIso A B b).obj Q).2 :=
  by
    change Over.mk (pullback.snd (Q.hom ≫ b.inv) (coprod.inr : B ⟶ A ⨿ B)) ≅
      Over.mk (pullback.snd Q.hom ((coprod.inr : B ⟶ A ⨿ B) ≫ b.hom))
    exact Over.isoMk (secondBaseSquare A B b Q).isoPullback (by simp)

/-- Transporting the codomain isomorphism gives the actual two pullback
functors, rather than a replacement fiber construction. -/
def splitAtComparison : (splitOverIso A B b).functor ≅ splitAtIso A B b :=
  NatIso.ofComponents (fun Q => Iso.prod (firstBaseIso A B b Q) (secondBaseIso A B b Q)) (by
    intro Q R f
    apply Prod.ext
    · apply Over.OverMorphism.ext
      apply pullback.hom_ext
      · simp [splitOverIso,coproductSliceEquivalence,splitAtIso,splitSlice,firstBaseIso,Over.pullback,Category.assoc]
      · exact (Over.w _).trans (Over.w _).symm
    · apply Over.OverMorphism.ext
      apply pullback.hom_ext
      · simp [splitOverIso,coproductSliceEquivalence,splitAtIso,splitSlice,secondBaseIso,Over.pullback,Category.assoc]
      · exact (Over.w _).trans (Over.w _).symm)

instance splitAtIso_isEquivalence : (splitAtIso A B b).IsEquivalence :=
  Functor.isEquivalence_of_iso (splitAtComparison A B b)

def splitAtEquivalence : Over C ≌ Over A × Over B := (splitAtIso A B b).asEquivalence

end BaseIso

/-- Cartesian product with a fixed object preserves the displayed
binary coproduct, by its actual van Kampen pullback squares. -/
def productSumIsColimit (X : D) :
    IsColimit (BinaryCofan.mk
      (prod.map (coprod.inl : A ⟶ A ⨿ B) (𝟙 X))
      (prod.map (coprod.inr : B ⟶ A ⨿ B) (𝟙 X))) := by
  have hv := (BinaryCofan.isVanKampen_iff _).mp
    (FinitaryExtensive.vanKampen _ (coprodIsCoprod A B))
    (BinaryCofan.mk (prod.map (coprod.inl : A ⟶ A ⨿ B) (𝟙 X))
      (prod.map (coprod.inr : B ⟶ A ⨿ B) (𝟙 X)))
  exact ((hv prod.fst prod.fst prod.fst (by simp) (by simp)).mpr
    ⟨(IsPullback.of_prod_fst_with_id coprod.inl X).flip,
      (IsPullback.of_prod_fst_with_id coprod.inr X).flip⟩).some

def productSumIso (X : D) : (A ⨯ X) ⨿ (B ⨯ X) ≅ (A ⨿ B) ⨯ X where
  hom := coprod.desc (prod.map coprod.inl (𝟙 X)) (prod.map coprod.inr (𝟙 X))
  inv := BinaryCofan.IsColimit.desc (productSumIsColimit A B X) coprod.inl coprod.inr
  hom_inv_id := by
    apply coprod.hom_ext
    · rw [coprod.inl_desc_assoc]
      simpa only [BinaryCofan.mk_inl,Category.comp_id] using
        BinaryCofan.IsColimit.inl_desc (productSumIsColimit A B X) coprod.inl coprod.inr
    · rw [coprod.inr_desc_assoc]
      simpa only [BinaryCofan.mk_inr,Category.comp_id] using
        BinaryCofan.IsColimit.inr_desc (productSumIsColimit A B X) coprod.inl coprod.inr
  inv_hom_id := by
    apply BinaryCofan.IsColimit.hom_ext (productSumIsColimit A B X)
    · rw [← Category.assoc,BinaryCofan.IsColimit.inl_desc]
      simp
    · rw [← Category.assoc,BinaryCofan.IsColimit.inr_desc]
      simp

@[simp, reassoc] theorem productSumIso_inl (X : D) :
    coprod.inl ≫ (productSumIso A B X).hom = prod.map coprod.inl (𝟙 X) := by
  simp [productSumIso]

@[simp, reassoc] theorem productSumIso_inr (X : D) :
    coprod.inr ≫ (productSumIso A B X).hom = prod.map coprod.inr (𝟙 X) := by
  simp [productSumIso]

end CoproductSlices
end CategoricalEssentialIncompleteness.V46.ArithmeticIndexedFibers
