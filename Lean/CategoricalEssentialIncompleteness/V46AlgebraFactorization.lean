/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import Mathlib.CategoryTheory.Endofunctor.Algebra
public import Mathlib.CategoryTheory.MorphismProperty.Factorization

/-!
# Factorization systems on algebras of an endofunctor

Appendix A cites Wißmann, Lemma 3.6. If an endofunctor preserves the left
class of an orthogonal factorization system, the two classes lift along the
forgetful functor on its algebras. Orthogonality supplies the structure
morphism on each intermediate object and gives its uniqueness.
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Endofunctor

namespace CategoricalEssentialIncompleteness.V46

universe v u
variable {C : Type u} [Category.{v} C]

/-- Wißmann's Definition 2.10. The two classes admit factorizations,
respect isomorphisms and have a unique diagonal for every square. -/
structure OrthogonalFactorizationSystem (E M : MorphismProperty C) : Prop where
  left_respectsIso : E.RespectsIso
  right_respectsIso : M.RespectsIso
  factorizes : MorphismProperty.HasFactorization E M
  diagonal {A B X Y : C} {e : A ⟶ B} {m : X ⟶ Y} (he : E e) (hm : M m)
    (top : A ⟶ X) (bottom : B ⟶ Y) (sq : top ≫ m = e ≫ bottom) :
    ∃! d : B ⟶ X, e ≫ d = top ∧ d ≫ m = bottom

namespace OrthogonalFactorizationSystem

variable {E M : MorphismProperty C} (S : OrthogonalFactorizationSystem E M)
include S

theorem diagonal_ext {A B X Y : C} {e : A ⟶ B} {m : X ⟶ Y} (he : E e) (hm : M m)
    {r s : B ⟶ X} (left : e ≫ r = e ≫ s) (right : r ≫ m = s ≫ m) : r = s := by
  obtain ⟨_, _, unique⟩ := S.diagonal he hm (e ≫ r) (r ≫ m) (Category.assoc ..)
  exact (unique r ⟨rfl, rfl⟩).trans (unique s ⟨left.symm, right.symm⟩).symm

variable (F : C ⥤ C) (preserves : E ≤ E.inverseImage F)
include preserves

/-- Every underlying factorization of an algebra morphism admits a unique
algebra structure on its intermediate object making both factors algebra morphisms. -/
theorem existsUnique_middle_algebra {A B : Algebra F} (h : A ⟶ B)
    (d : MorphismProperty.MapFactorizationData E M h.f) :
    ∃! s : F.obj d.Z ⟶ d.Z,
      F.map d.i ≫ s = A.str ≫ d.i ∧ s ≫ d.p = F.map d.p ≫ B.str := by
  apply S.diagonal (preserves _ d.hi) d.hp
  rw [Category.assoc, d.fac, ← F.map_comp_assoc, d.fac, h.h]

private theorem algebra_diagonal {A B X Y : Algebra F} (e : A ⟶ B) (m : X ⟶ Y)
    (he : E e.f) (hm : M m.f) (top : A ⟶ X) (bottom : B ⟶ Y)
    (d : B.a ⟶ X.a) (left : e.f ≫ d = top.f) (right : d ≫ m.f = bottom.f) :
    F.map d ≫ X.str = B.str ≫ d := by
  apply S.diagonal_ext (e := F.map e.f) (m := m.f) (preserves _ he) hm
  · calc F.map e.f ≫ F.map d ≫ X.str
          = F.map top.f ≫ X.str := by rw [← F.map_comp_assoc, left]
         _ = A.str ≫ top.f := top.h
         _ = F.map e.f ≫ B.str ≫ d := by rw [← left, ← Category.assoc, ← e.h, Category.assoc]
  · calc (F.map d ≫ X.str) ≫ m.f
          = F.map bottom.f ≫ Y.str := by rw [Category.assoc, ← m.h, ← F.map_comp_assoc, right]
         _ = B.str ≫ bottom.f := bottom.h
         _ = (B.str ≫ d) ≫ m.f := by rw [Category.assoc, right]

/-- The classes in the lifted factorization system are detected by the
forgetful functor on algebras. -/
theorem algebra : OrthogonalFactorizationSystem
    (E.inverseImage (Algebra.forget F)) (M.inverseImage (Algebra.forget F)) := by
  let : E.RespectsIso := S.left_respectsIso
  let : M.RespectsIso := S.right_respectsIso
  refine ⟨inferInstance, inferInstance, ⟨?_⟩, ?_⟩
  · intro A B h
    obtain ⟨d⟩ := S.factorizes.nonempty_mapFactorizationData h.f
    obtain ⟨s, equations, _⟩ := S.existsUnique_middle_algebra F preserves h d
    exact ⟨{ Z := ⟨d.Z, s⟩
             i := ⟨d.i, equations.1⟩
             p := ⟨d.p, equations.2.symm⟩
             fac := Algebra.ext d.fac
             hi := d.hi
             hp := d.hp }⟩
  · intro A B X Y e m he hm top bottom square
    have sq : top.f ≫ m.f = e.f ≫ bottom.f := congrArg Algebra.Hom.f square
    obtain ⟨d, ⟨left, right⟩, unique⟩ := S.diagonal he hm top.f bottom.f sq
    let lift : B ⟶ X := ⟨d, S.algebra_diagonal F preserves e m he hm top bottom d left right⟩
    refine ⟨lift, ⟨Algebra.ext left, Algebra.ext right⟩, ?_⟩
    intro other facts
    apply Algebra.ext
    exact unique other.f ⟨congrArg Algebra.Hom.f facts.1, congrArg Algebra.Hom.f facts.2⟩

end OrthogonalFactorizationSystem
end CategoricalEssentialIncompleteness.V46
