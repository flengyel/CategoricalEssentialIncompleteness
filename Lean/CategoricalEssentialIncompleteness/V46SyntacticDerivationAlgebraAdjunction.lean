/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46AlgebraTransport

/-! Initial algebras under a left adjoint with an invertible functor comparison.
This is used for the success fiber of a rule-tree validator. -/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v₁ v₂ u₁ u₂
open CategoryTheory CategoryTheory.Limits

namespace CategoricalEssentialIncompleteness.V46.SyntacticDerivation.AlgebraAdjunction
variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
variable {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
variable {F : C ⥤ C} {G : D ⥤ D} (θ : F ⋙ L ≅ L ⋙ G)

def leftAlgebra (A : Endofunctor.Algebra F) : Endofunctor.Algebra G where
  a := L.obj A.a
  str := θ.inv.app A.a ≫ L.map A.str

def rightAlgebra (B : Endofunctor.Algebra G) : Endofunctor.Algebra F where
  a := R.obj B.a
  str := adj.homEquiv _ _
    (θ.hom.app (R.obj B.a) ≫ G.map (adj.counit.app B.a) ≫ B.str)

theorem unmate_mate {X : C} {Y : D} (f : L.obj X ⟶ Y) :
    L.map (adj.homEquiv _ _ f) ≫ adj.counit.app Y = f := by
  exact (adj.homEquiv_counit (g := adj.homEquiv _ _ f)).symm.trans
    ((adj.homEquiv _ _).symm_apply_apply f)

/-- The ordinary adjunction equivalence restricts to algebra morphisms.
The equation is derived by naturality of the comparison and the counit. -/
theorem mate_hom_iff (A : Endofunctor.Algebra F) (B : Endofunctor.Algebra G)
    (f : L.obj A.a ⟶ B.a) :
    F.map (adj.homEquiv _ _ f) ≫ (rightAlgebra adj θ B).str =
        A.str ≫ adj.homEquiv _ _ f ↔
      G.map f ≫ B.str = (leftAlgebra θ A).str ≫ f := by
  dsimp only [leftAlgebra, rightAlgebra]
  rw [← (adj.homEquiv _ _).symm.injective.eq_iff,
    Adjunction.homEquiv_naturality_left_symm,
    Adjunction.homEquiv_naturality_left_symm]
  simp only [Equiv.symm_apply_apply]
  have hn : L.map (F.map (adj.homEquiv _ _ f)) ≫ θ.hom.app (R.obj B.a) =
      θ.hom.app A.a ≫ G.map (L.map (adj.homEquiv _ _ f)) := θ.hom.naturality _
  rw [← Category.assoc, hn]
  simp only [Category.assoc]
  have hg : G.map (L.map (adj.homEquiv _ _ f)) ≫ G.map (adj.counit.app B.a) ≫ B.str =
      G.map f ≫ B.str := by
    rw [← Category.assoc, ← G.map_comp, unmate_mate]
  rw [hg]
  change θ.hom.app A.a ≫ (G.map f ≫ B.str) = L.map A.str ≫ f ↔ _
  constructor
  · intro h
    calc
      G.map f ≫ B.str = (θ.inv.app A.a ≫ θ.hom.app A.a) ≫ (G.map f ≫ B.str) := by simp
      _ = θ.inv.app A.a ≫ (θ.hom.app A.a ≫ (G.map f ≫ B.str)) := Category.assoc _ _ _
      _ = θ.inv.app A.a ≫ (L.map A.str ≫ f) := by rw [h]
  · intro h
    rw [h]
    simp only [← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]

def homEquiv (A : Endofunctor.Algebra F) (B : Endofunctor.Algebra G) :
    (leftAlgebra θ A ⟶ B) ≃ (A ⟶ rightAlgebra adj θ B) where
  toFun f := ⟨adj.homEquiv _ _ f.f, (mate_hom_iff adj θ A B f.f).mpr f.h⟩
  invFun f := ⟨(adj.homEquiv _ _).symm f.f,
    (mate_hom_iff adj θ A B _).mp (by
      simp only [Equiv.apply_symm_apply]
      exact f.h)⟩
  left_inv f := Endofunctor.Algebra.Hom.ext ((adj.homEquiv _ _).symm_apply_apply f.f)
  right_inv f := Endofunctor.Algebra.Hom.ext ((adj.homEquiv _ _).apply_symm_apply f.f)

/-- No initiality or evaluation hypothesis is added on the target side: every
target-algebra morphism is obtained by the proved adjunction equivalence. -/
def initial (A : Endofunctor.Algebra F) (hA : IsInitial A) :
    IsInitial (leftAlgebra θ A) :=
  IsInitial.ofUniqueHom
    (fun B => (homEquiv adj θ A B).symm (hA.to (rightAlgebra adj θ B)))
    (by
      intro B f
      apply (homEquiv adj θ A B).injective
      simpa only [Equiv.apply_symm_apply] using
        hA.hom_ext ((homEquiv adj θ A B) f) (hA.to (rightAlgebra adj θ B)))

end CategoricalEssentialIncompleteness.V46.SyntacticDerivation.AlgebraAdjunction
