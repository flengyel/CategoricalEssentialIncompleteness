/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46CategoricalSubstitution
public import Mathlib.CategoryTheory.Comma.Over.Pullback

/-! The success-fiber functor and its explicit option-extension right adjoint. -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v u
open CategoryTheory CategoryTheory.Limits

namespace CategoricalEssentialIncompleteness.V46.SyntacticDerivation.SuccessAdjunction
variable {D : Type u} [Category.{v} D] [Regular D] [FinitaryExtensive D]
variable (F : D)

def some : F ⟶ OptionSyntax.obj F := coprod.inr

abbrev extend : Over F ⥤ Over (OptionSyntax.obj F) where
  obj Q := Over.mk (OptionSyntax.map Q.hom)
  map f := Over.homMk (OptionSyntax.map f.left) (by
    change coprod.map (𝟙 _) f.left ≫ coprod.map (𝟙 _) _ = coprod.map (𝟙 _) _
    rw [coprod.map_map, Category.comp_id, Over.w f])
  map_id Q := by
    apply Over.OverMorphism.ext
    change coprod.map (𝟙 _) (𝟙 _) = 𝟙 _
    exact coprod.map_id_id
  map_comp f g := by
    apply Over.OverMorphism.ext
    change coprod.map (𝟙 _) (f.left ≫ g.left) =
      coprod.map (𝟙 _) f.left ≫ coprod.map (𝟙 _) g.left
    rw [coprod.map_map, Category.comp_id]

/-- The option extension square is a pullback even when the conclusion morphism is neither
monic nor epic. -/
theorem extensionSquare (Q : Over F) :
    IsPullback (coprod.inr : Q.left ⟶ OptionSyntax.obj Q.left) Q.hom
      (OptionSyntax.map Q.hom) (some F) := by
  have hv := (BinaryCofan.isVanKampen_iff _).mp
    (FinitaryExtensive.vanKampen _ (coprodIsCoprod (⊤_ D) F))
    (BinaryCofan.mk (coprod.inl : ⊤_ D ⟶ OptionSyntax.obj Q.left) coprod.inr)
  exact ((hv (𝟙 _) Q.hom (OptionSyntax.map Q.hom)
    (by simp [OptionSyntax.map]) (by simp [OptionSyntax.map])).mp
      ⟨coprodIsCoprod (⊤_ D) Q.left⟩).2

def extension {X : Over (OptionSyntax.obj F)} {Q : Over F}
    (f : (Over.pullback (some F)).obj X ⟶ Q) : X ⟶ (extend F).obj Q :=
  Over.homMk
    (SumFibers.caseOf X.hom
      (terminal.from _ ≫ coprod.inl) (f.left ≫ coprod.inr))
    (by
      change SumFibers.caseOf X.hom _ _ ≫ OptionSyntax.map Q.hom = X.hom
      apply BinaryCofan.IsColimit.hom_ext (SumFibers.isColimit X.hom)
      · simp only [BinaryCofan.mk_inl]
        rw [← Category.assoc, SumFibers.inl_caseOf]
        simp only [Category.assoc, OptionSyntax.map, coprod.inl_map, Category.id_comp]
        rw [pullback.condition]
        congr 1
        exact Subsingleton.elim _ _
      · simp only [BinaryCofan.mk_inr]
        rw [← Category.assoc, SumFibers.inr_caseOf]
        simp only [Category.assoc, OptionSyntax.map, coprod.inr_map]
        rw [← Category.assoc, Over.w f]
        exact pullback.condition.symm)

def restriction {X : Over (OptionSyntax.obj F)} {Q : Over F}
    (g : X ⟶ (extend F).obj Q) : (Over.pullback (some F)).obj X ⟶ Q :=
  Over.homMk
    ((extensionSquare F Q).lift (pullback.fst X.hom (some F) ≫ g.left)
      (pullback.snd X.hom (some F)) (by
        have hg : g.left ≫ OptionSyntax.map Q.hom = X.hom := Over.w g
        rw [Category.assoc, hg]
        exact pullback.condition))
    ((extensionSquare F Q).lift_snd _ _ _)

@[simp, reassoc] theorem restriction_some {X : Over (OptionSyntax.obj F)} {Q : Over F}
    (g : X ⟶ (extend F).obj Q) :
    (restriction F g).left ≫ coprod.inr = pullback.fst X.hom (some F) ≫ g.left :=
  (extensionSquare F Q).lift_fst _ _ _

theorem restriction_extension {X : Over (OptionSyntax.obj F)} {Q : Over F}
    (f : (Over.pullback (some F)).obj X ⟶ Q) :
    restriction F (extension F f) = f := by
  apply Over.OverMorphism.ext
  apply (cancel_mono (coprod.inr : Q.left ⟶ OptionSyntax.obj Q.left)).mp
  rw [restriction_some]
  exact SumFibers.inr_caseOf X.hom _ _

theorem extension_restriction {X : Over (OptionSyntax.obj F)} {Q : Over F}
    (g : X ⟶ (extend F).obj Q) : extension F (restriction F g) = g := by
  apply Over.OverMorphism.ext
  apply BinaryCofan.IsColimit.hom_ext (SumFibers.isColimit X.hom)
  · change pullback.fst X.hom coprod.inl ≫
        SumFibers.caseOf X.hom _ _ = pullback.fst X.hom coprod.inl ≫ g.left
    rw [SumFibers.inl_caseOf]
    have h : (pullback.fst X.hom coprod.inl ≫ g.left) ≫ OptionSyntax.map Q.hom =
        pullback.snd X.hom coprod.inl ≫ coprod.inl := by
      have hg : g.left ≫ OptionSyntax.map Q.hom = X.hom := Over.w g
      rw [Category.assoc, hg]
      exact pullback.condition
    have hv := (BinaryCofan.isVanKampen_iff _).mp
      (FinitaryExtensive.vanKampen _ (coprodIsCoprod (⊤_ D) F))
      (BinaryCofan.mk (coprod.inl : ⊤_ D ⟶ OptionSyntax.obj Q.left) coprod.inr)
    have hp : IsPullback (coprod.inl : ⊤_ D ⟶ OptionSyntax.obj Q.left) (𝟙 _)
        (OptionSyntax.map Q.hom) (coprod.inl : ⊤_ D ⟶ OptionSyntax.obj F) :=
      ((hv (𝟙 _) Q.hom (OptionSyntax.map Q.hom)
        (by simp [OptionSyntax.map]) (by simp [OptionSyntax.map])).mp
          ⟨coprodIsCoprod (⊤_ D) Q.left⟩).1
    have hf := hp.lift_fst
      (pullback.fst X.hom coprod.inl ≫ g.left)
      (pullback.snd X.hom coprod.inl) h
    rw [show hp.lift _ _ h = terminal.from _ from Subsingleton.elim _ _] at hf
    exact hf
  · change pullback.fst X.hom coprod.inr ≫
        SumFibers.caseOf X.hom _ _ = pullback.fst X.hom coprod.inr ≫ g.left
    rw [SumFibers.inr_caseOf]
    exact restriction_some F g

def homEquiv (X : Over (OptionSyntax.obj F)) (Q : Over F) :
    ((Over.pullback (some F)).obj X ⟶ Q) ≃ (X ⟶ (extend F).obj Q) where
  toFun := extension F
  invFun := restriction F
  left_inv := restriction_extension F
  right_inv := extension_restriction F

def adjunction : Over.pullback (some F) ⊣ extend F :=
  Adjunction.mkOfHomEquiv
    { homEquiv := homEquiv F
      homEquiv_naturality_left_symm := by
        intro X Y Q f g
        apply Over.OverMorphism.ext
        apply (cancel_mono (coprod.inr : Q.left ⟶ OptionSyntax.obj Q.left)).mp
        change (restriction F (f ≫ g)).left ≫ coprod.inr =
          (((Over.pullback (some F)).map f).left ≫ (restriction F g).left) ≫ coprod.inr
        rw [Category.assoc, restriction_some, restriction_some]
        change pullback.fst X.hom (some F) ≫ (f.left ≫ g.left) =
          pullback.lift _ _ _ ≫ pullback.fst Y.hom (some F) ≫ g.left
        rw [pullback.lift_fst_assoc]
        exact (Category.assoc _ _ _).symm
      homEquiv_naturality_right := by
        intro X Q Q' f g
        apply Over.OverMorphism.ext
        change SumFibers.caseOf X.hom _ _ =
          SumFibers.caseOf X.hom _ _ ≫ OptionSyntax.map g.left
        apply BinaryCofan.IsColimit.hom_ext (SumFibers.isColimit X.hom)
        · simp only [BinaryCofan.mk_inl]
          rw [SumFibers.inl_caseOf, ← Category.assoc, SumFibers.inl_caseOf]
          simp [OptionSyntax.map]
        · simp only [BinaryCofan.mk_inr]
          rw [SumFibers.inr_caseOf, ← Category.assoc, SumFibers.inr_caseOf]
          simp [OptionSyntax.map, Category.assoc] }

end CategoricalEssentialIncompleteness.V46.SyntacticDerivation.SuccessAdjunction
