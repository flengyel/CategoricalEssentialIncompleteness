/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46LogicalTranslations

/-! # The Galois connection induced by a logical translation

Finite-proof translation first gives an inclusion between generated
sentence images. This proves that inverse image preserves theories and
establishes the adjunction and generation and composition identities.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u

open CategoryTheory CategoryTheory.Limits

namespace CategoricalEssentialIncompleteness.V46.FirstOrderPresentation

variable {D : Type u} [Category.{v} D] [Regular D] [FinitaryExtensive D]
variable {V : D} {P Q R : FirstOrderPresentation V}

namespace Translation

variable (σ : Translation P Q)

theorem map_generated_le
    (A : Subobject P.syntaxData.sentenceObject) (B : Subobject Q.syntaxData.sentenceObject)
    (k : (A : D) ⟶ (B : D)) (hk : k ≫ B.arrow = A.arrow ≫ σ.sentence) :
    (Subobject.«exists» σ.sentence).obj (FirstOrderReflection.generated P.proofs A) ≤
      FirstOrderReflection.generated Q.proofs B := by
  let τ := σ.rulesMap A B k hk
  let f := τ.sentenceMap P.syntaxData.sentenceInclusion Q.syntaxData.sentenceInclusion
    σ.sentence σ.sentences (P.proofs A) (P.initial A) (Q.proofs B)
  let sq : Arrow.mk (FirstOrderReflection.conclusion P.proofs A) ⟶
      Arrow.mk (FirstOrderReflection.conclusion Q.proofs B) :=
    Arrow.homMk f σ.sentence (τ.sentenceMap_conclusion _ _ _ _ _ _ _)
  exact Subobject.exists_le_of_comm σ.sentence (imageSubobjectMap sq)
    (imageSubobjectMap_arrow sq)

theorem map_generated_of_le
    (A : Subobject P.syntaxData.sentenceObject) (B : Subobject Q.syntaxData.sentenceObject)
    (h : (Subobject.«exists» σ.sentence).obj A ≤ B) :
    (Subobject.«exists» σ.sentence).obj (FirstOrderReflection.generated P.proofs A) ≤
      FirstOrderReflection.generated Q.proofs B := by
  apply σ.map_generated_le A B
    ((Subobject.imageFactorisation σ.sentence A).F.e ≫ Subobject.ofLE _ _ h)
  rw [Category.assoc, Subobject.ofLE_arrow]
  exact (Subobject.imageFactorisation σ.sentence A).F.fac

theorem inverse_closed (T : Q.Theories) :
    FirstOrderReflection.generated P.proofs ((Subobject.pullback σ.sentence).obj T.val) =
      (Subobject.pullback σ.sentence).obj T.val := by
  let A := (Subobject.pullback σ.sentence).obj T.val
  have h := σ.map_generated_le A T.val (Subobject.pullbackπ σ.sentence T.val)
    (Subobject.isPullback σ.sentence T.val).w
  rw [T.property] at h
  exact le_antisymm ((Subobject.existsPullbackAdj σ.sentence).gc _ _ |>.mp h)
    (FirstOrderReflection.extensive P.proofs A)

def inverseImage : Q.Theories ⥤ P.Theories where
  obj T := ⟨(Subobject.pullback σ.sentence).obj T.val, σ.inverse_closed T⟩
  map f := homOfLE (leOfHom ((Subobject.pullback σ.sentence).map (homOfLE (leOfHom f))))

def pushforward : P.Theories ⥤ Q.Theories where
  obj T := ⟨FirstOrderReflection.generated Q.proofs ((Subobject.«exists» σ.sentence).obj T.val),
    FirstOrderReflection.idempotent Q.proofs Q.initial _⟩
  map f := homOfLE (FirstOrderReflection.monotone Q.proofs Q.initial
    (leOfHom ((Subobject.«exists» σ.sentence).map (homOfLE (leOfHom f)))))

theorem pushforward_le_iff (T : P.Theories) (U : Q.Theories) :
    (σ.pushforward.obj T).val ≤ U.val ↔ T.val ≤ (σ.inverseImage.obj U).val := by
  change FirstOrderReflection.generated Q.proofs ((Subobject.«exists» σ.sentence).obj T.val) ≤
      U.val ↔ T.val ≤ (Subobject.pullback σ.sentence).obj U.val
  rw [FirstOrderReflection.generated_le_iff Q.proofs Q.initial _ U]
  exact (Subobject.existsPullbackAdj σ.sentence).gc _ _

def homEquiv (T : P.Theories) (U : Q.Theories) :
    (σ.pushforward.obj T ⟶ U) ≃ (T ⟶ σ.inverseImage.obj U) where
  toFun f := homOfLE ((σ.pushforward_le_iff T U).mp (leOfHom f))
  invFun f := homOfLE ((σ.pushforward_le_iff T U).mpr (leOfHom f))
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _

def adjunction : σ.pushforward ⊣ σ.inverseImage :=
  Adjunction.mkOfHomEquiv {
    homEquiv := σ.homEquiv
    homEquiv_naturality_left_symm := fun _ _ => Subsingleton.elim _ _
    homEquiv_naturality_right := fun _ _ => Subsingleton.elim _ _ }

theorem generation_identity (A : Subobject P.syntaxData.sentenceObject) :
    FirstOrderReflection.generated Q.proofs ((Subobject.«exists» σ.sentence).obj A) =
      FirstOrderReflection.generated Q.proofs ((Subobject.«exists» σ.sentence).obj
        (FirstOrderReflection.generated P.proofs A)) := by
  apply le_antisymm
  · exact FirstOrderReflection.monotone Q.proofs Q.initial
      (leOfHom ((Subobject.«exists» σ.sentence).map
        (homOfLE (FirstOrderReflection.extensive P.proofs A))))
  · have h := σ.map_generated_le A ((Subobject.«exists» σ.sentence).obj A)
      (Subobject.imageFactorisation σ.sentence A).F.e
      (Subobject.imageFactorisation σ.sentence A).F.fac
    simpa only [FirstOrderReflection.idempotent Q.proofs Q.initial] using
      FirstOrderReflection.monotone Q.proofs Q.initial h

theorem generation_functor_identity :
    Subobject.«exists» σ.sentence ⋙ FirstOrderReflection.generation Q.proofs Q.initial =
      FirstOrderReflection.generation P.proofs P.initial ⋙ σ.pushforward := by
  apply CategoryTheory.Functor.ext (fun A => Subtype.ext (σ.generation_identity A))

theorem pushforward_comp (τ : Translation Q R) :
    (σ.comp τ).pushforward = σ.pushforward ⋙ τ.pushforward := by
  apply CategoryTheory.Functor.ext
    (fun T => Subtype.ext (by
      change FirstOrderReflection.generated R.proofs
          ((Subobject.«exists» (σ.sentence ≫ τ.sentence)).obj T.val) = _
      rw [Subobject.exists_comp]
      exact τ.generation_identity ((Subobject.«exists» σ.sentence).obj T.val)))

theorem inverseImage_comp (τ : Translation Q R) :
    (σ.comp τ).inverseImage = τ.inverseImage ⋙ σ.inverseImage := by
  apply CategoryTheory.Functor.ext
    (fun T => Subtype.ext (Subobject.pullback_comp σ.sentence τ.sentence T.val))

theorem pushforward_id (P : FirstOrderPresentation V) : (id P).pushforward = 𝟭 P.Theories := by
  apply CategoryTheory.Functor.ext
    (fun T => Subtype.ext (by
      change FirstOrderReflection.generated P.proofs ((Subobject.«exists» (𝟙 _)).obj T.val) = _
      rw [Subobject.exists_iso_map, Subobject.map_id]
      exact T.property))

theorem inverseImage_id (P : FirstOrderPresentation V) : (id P).inverseImage = 𝟭 P.Theories := by
  apply CategoryTheory.Functor.ext (fun T => Subtype.ext (Subobject.pullback_id T.val))

end Translation
end CategoricalEssentialIncompleteness.V46.FirstOrderPresentation
