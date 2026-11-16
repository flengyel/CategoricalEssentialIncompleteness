/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module
public import CategoricalEssentialIncompleteness.V46SyntacticDerivationAlgebraAdjunction

/-! # Unique algebra folds along a noninvertible functor comparison

Postcomposition between parameter slices preserves coproducts but need not
preserve relative products. Only the forward polynomial comparison is used.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v₁ v₂ u₁ u₂
open CategoryTheory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness.V46.LaxAlgebraAdjunction
variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
variable {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
variable {F : C ⥤ C} {G : D ⥤ D} (θ : F ⋙ L ⟶ L ⋙ G)

def rightAlgebra (B : Endofunctor.Algebra G) : Endofunctor.Algebra F where
  a := R.obj B.a
  str := adj.homEquiv _ _
    (θ.app (R.obj B.a) ≫ G.map (adj.counit.app B.a) ≫ B.str)

/-- The adjunction identifies algebra morphisms into the constructed
right algebra with the forward comparison equation. No inverse is needed. -/
theorem mate_hom_iff (A : Endofunctor.Algebra F) (B : Endofunctor.Algebra G)
    (f : L.obj A.a ⟶ B.a) :
    F.map (adj.homEquiv _ _ f) ≫ (rightAlgebra adj θ B).str =
        A.str ≫ adj.homEquiv _ _ f ↔
      θ.app A.a ≫ G.map f ≫ B.str = L.map A.str ≫ f := by
  dsimp only [rightAlgebra]
  rw [← (adj.homEquiv _ _).symm.injective.eq_iff,
    Adjunction.homEquiv_naturality_left_symm,
    Adjunction.homEquiv_naturality_left_symm]
  simp only [Equiv.symm_apply_apply]
  have hn : L.map (F.map (adj.homEquiv _ _ f)) ≫ θ.app (R.obj B.a) =
      θ.app A.a ≫ G.map (L.map (adj.homEquiv _ _ f)) := θ.naturality _
  rw [← Category.assoc, hn]
  simp only [Category.assoc]
  rw [← G.map_comp_assoc, SyntacticDerivation.AlgebraAdjunction.unmate_mate]

def fold (A : Endofunctor.Algebra F) (hA : IsInitial A)
    (B : Endofunctor.Algebra G) : L.obj A.a ⟶ B.a :=
  (adj.homEquiv _ _).symm (hA.to (rightAlgebra adj θ B)).f

theorem fold_constructor (A : Endofunctor.Algebra F) (hA : IsInitial A)
    (B : Endofunctor.Algebra G) :
    θ.app A.a ≫ G.map (fold adj θ A hA B) ≫ B.str =
      L.map A.str ≫ fold adj θ A hA B := by
  apply (mate_hom_iff adj θ A B _).mp
  simpa only [fold, Equiv.apply_symm_apply] using (hA.to (rightAlgebra adj θ B)).h

include adj in
/-- Uniqueness covers every underlying morphism satisfying the original
constructor equation across the change of parameter. -/
theorem unique (A : Endofunctor.Algebra F) (hA : IsInitial A)
    (B : Endofunctor.Algebra G) (f g : L.obj A.a ⟶ B.a)
    (hf : θ.app A.a ≫ G.map f ≫ B.str = L.map A.str ≫ f)
    (hg : θ.app A.a ≫ G.map g ≫ B.str = L.map A.str ≫ g) : f = g := by
  apply (adj.homEquiv _ _).injective
  exact congrArg Endofunctor.Algebra.Hom.f (hA.hom_ext
    (⟨adj.homEquiv _ _ f, (mate_hom_iff adj θ A B f).mpr hf⟩ :
      A ⟶ rightAlgebra adj θ B)
    (⟨adj.homEquiv _ _ g, (mate_hom_iff adj θ A B g).mpr hg⟩ :
      A ⟶ rightAlgebra adj θ B))
include adj in
/-- Algebra maps commute with coefficient transitions whenever the two
constructor squares commute. The underlying comparison need not be invertible. -/
theorem fold_natural (A B : Endofunctor.Algebra F) (hA : IsInitial A)
    (A' B' : Endofunctor.Algebra G) (s : L.obj A.a ⟶ A'.a) (t : L.obj B.a ⟶ B'.a)
    (hs : θ.app A.a ≫ G.map s ≫ A'.str = L.map A.str ≫ s)
    (ht : θ.app B.a ≫ G.map t ≫ B'.str = L.map B.str ≫ t)
    (f : A ⟶ B) (g : A' ⟶ B') : s ≫ g.f = L.map f.f ≫ t := by
  apply unique adj θ A hA B'
  · rw [Functor.map_comp, Category.assoc, g.h]
    simpa only [Category.assoc] using congrArg (fun m => m ≫ g.f) hs
  · have hn : θ.app A.a ≫ G.map (L.map f.f) = L.map (F.map f.f) ≫ θ.app B.a :=
      (θ.naturality f.f).symm
    rw [Functor.map_comp]
    simp only [Category.assoc]
    rw [← Category.assoc (θ.app A.a) (G.map (L.map f.f)) _, hn,
      Category.assoc, ht, ← L.map_comp_assoc, f.h, L.map_comp, Category.assoc]
end CategoricalEssentialIncompleteness.V46.LaxAlgebraAdjunction
