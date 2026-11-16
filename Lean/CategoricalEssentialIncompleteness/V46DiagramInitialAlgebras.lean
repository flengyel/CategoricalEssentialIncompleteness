/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module
public import Mathlib.CategoryTheory.Endofunctor.Algebra

/-! # Initial algebras with changing coefficient diagrams

Transition morphisms may identify coefficient labels. The transition of
an initial algebra is its unique fold into the reindexed target algebra.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v₁ v₂ u₁ u₂
open CategoryTheory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness.V46.DiagramInitialAlgebras
variable {J : Type u₁} {C : Type u₂} [Category.{v₁} J] [Category.{v₂} C]
variable (P : J ⥤ (C ⥤ C))
variable (A : ∀ j, Endofunctor.Algebra (P.obj j)) (hA : ∀ j, IsInitial (A j))

def transition {j k : J} (f : j ⟶ k) : (A j).a ⟶ (A k).a :=
  ((hA j).to ((Endofunctor.Algebra.functorOfNatTrans (P.map f)).obj (A k))).f

theorem transition_constructor {j k : J} (f : j ⟶ k) :
    (P.obj j).map (transition P A hA f) ≫ (P.map f).app (A k).a ≫ (A k).str =
      (A j).str ≫ transition P A hA f :=
  ((hA j).to ((Endofunctor.Algebra.functorOfNatTrans (P.map f)).obj (A k))).h

theorem transition_unique {j k : J} (f : j ⟶ k) (g : (A j).a ⟶ (A k).a)
    (hg : (P.obj j).map g ≫ (P.map f).app (A k).a ≫ (A k).str = (A j).str ≫ g) :
    g = transition P A hA f :=
  congrArg Endofunctor.Algebra.Hom.f ((hA j).hom_ext
    (⟨g, hg⟩ : A j ⟶ (Endofunctor.Algebra.functorOfNatTrans (P.map f)).obj (A k)) _)

@[simp] theorem transition_id (j : J) : transition P A hA (𝟙 j) = 𝟙 (A j).a := by
  symm
  apply transition_unique
  simp

@[simp] theorem transition_comp {i j k : J} (f : i ⟶ j) (g : j ⟶ k) :
    transition P A hA (f ≫ g) = transition P A hA f ≫ transition P A hA g := by
  symm
  apply transition_unique
  rw [Functor.map_comp, P.map_comp, NatTrans.comp_app]
  simp only [Category.assoc]
  rw [(P.map f).naturality_assoc, transition_constructor]
  simpa only [Category.assoc] using congrArg
    (fun m => m ≫ transition P A hA g) (transition_constructor P A hA f)

def carrier : J ⥤ C where
  obj j := (A j).a
  map f := transition P A hA f
  map_id := transition_id P A hA
  map_comp := transition_comp P A hA

/-- The endofunctor on diagrams uses each coefficient transition and each
recursive child transition. -/
def diagonal : (J ⥤ C) ⥤ (J ⥤ C) where
  obj X := {
    obj j := (P.obj j).obj (X.obj j)
    map {j k} f := (P.obj j).map (X.map f) ≫ (P.map f).app (X.obj k)
    map_id j := by simp
    map_comp {i j k} f g := by
      simp only [X.map_comp, Functor.map_comp, NatTrans.comp_app, Category.assoc]
      rw [← (P.map f).naturality_assoc] }
  map m := {
    app j := (P.obj j).map (m.app j)
    naturality {j k} f := by
      simp only [Category.assoc]
      rw [← (P.map f).naturality, ← Functor.map_comp_assoc, m.naturality,
        Functor.map_comp, Category.assoc] }
  map_id X := by ext j; simp
  map_comp m n := by ext j; simp

def algebra : Endofunctor.Algebra (diagonal P) where
  a := carrier P A hA
  str := {
    app j := (A j).str
    naturality {j k} f := by
      simpa only [diagonal, carrier, Category.assoc] using transition_constructor P A hA f }

def component (B : Endofunctor.Algebra (diagonal P)) (j : J) :
    Endofunctor.Algebra (P.obj j) := ⟨B.a.obj j, B.str.app j⟩

def foldComponent (B : Endofunctor.Algebra (diagonal P)) (j : J) :
    (A j).a ⟶ B.a.obj j := ((hA j).to (component P B j)).f

theorem fold_natural (B : Endofunctor.Algebra (diagonal P)) {j k : J} (f : j ⟶ k) :
    transition P A hA f ≫ foldComponent P A hA B k =
      foldComponent P A hA B j ≫ B.a.map f := by
  let T := (Endofunctor.Algebra.functorOfNatTrans (P.map f)).obj (component P B k)
  have left : (P.obj j).map (transition P A hA f ≫ foldComponent P A hA B k) ≫ T.str =
      (A j).str ≫ (transition P A hA f ≫ foldComponent P A hA B k) := by
    change (P.obj j).map _ ≫ ((P.map f).app (B.a.obj k) ≫ B.str.app k) = _
    rw [Functor.map_comp]
    simp only [Category.assoc]
    rw [(P.map f).naturality_assoc]
    rw [show (P.obj k).map (foldComponent P A hA B k) ≫ B.str.app k =
      (A k).str ≫ foldComponent P A hA B k from ((hA k).to (component P B k)).h]
    simpa only [Category.assoc] using congrArg
      (fun m => m ≫ foldComponent P A hA B k) (transition_constructor P A hA f)
  have right : (P.obj j).map (foldComponent P A hA B j ≫ B.a.map f) ≫ T.str =
      (A j).str ≫ (foldComponent P A hA B j ≫ B.a.map f) := by
    change (P.obj j).map _ ≫ ((P.map f).app (B.a.obj k) ≫ B.str.app k) = _
    rw [Functor.map_comp]
    simp only [Category.assoc]
    rw [show (P.obj j).map (B.a.map f) ≫ (P.map f).app (B.a.obj k) ≫ B.str.app k =
      B.str.app j ≫ B.a.map f from by simpa only [diagonal, Category.assoc] using B.str.naturality f]
    rw [← Category.assoc]
    simpa only [Category.assoc, foldComponent, component] using
      congrArg (fun m => m ≫ B.a.map f) ((hA j).to (component P B j)).h
  exact congrArg Endofunctor.Algebra.Hom.f ((hA j).hom_ext
    (⟨_, left⟩ : A j ⟶ T) (⟨_, right⟩ : A j ⟶ T))

def fold (B : Endofunctor.Algebra (diagonal P)) : algebra P A hA ⟶ B where
  f := { app j := foldComponent P A hA B j, naturality {j k} f := fold_natural P A hA B f }
  h := by
    ext j
    exact ((hA j).to (component P B j)).h

/-- Initiality covers every natural target algebra and every algebra
morphism, with no injectivity condition on coefficient transitions. -/
def initial : IsInitial (algebra P A hA) :=
  IsInitial.ofUniqueHom (fold P A hA) (by
    intro B m
    apply Endofunctor.Algebra.Hom.ext
    ext j
    exact congrArg Endofunctor.Algebra.Hom.f ((hA j).hom_ext
      (⟨m.f.app j, congrArg (fun n => n.app j) m.h⟩ : A j ⟶ component P B j) _))
end CategoricalEssentialIncompleteness.V46.DiagramInitialAlgebras
