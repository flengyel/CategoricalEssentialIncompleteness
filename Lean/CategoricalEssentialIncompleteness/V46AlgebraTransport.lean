/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import Mathlib.CategoryTheory.Endofunctor.Algebra
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal

/-! # Initial algebras transported across an equivalence of base categories -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v₁ v₂ u₁ u₂

open CategoryTheory CategoryTheory.Limits

namespace CategoricalEssentialIncompleteness.V46.AlgebraTransport

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
variable (E : C ≌ D) {F : C ⥤ C} {G : D ⥤ D}
variable (α : F ⋙ E.functor ≅ E.functor ⋙ G)

def mappedAlgebra (A : Endofunctor.Algebra F) : Endofunctor.Algebra G where
  a := E.functor.obj A.a
  str := α.inv.app A.a ≫ E.functor.map A.str

/-- The structure equation is preserved and reflected by the underlying
equivalence and the natural endofunctor comparison. -/
theorem hom_condition_iff (A B : Endofunctor.Algebra F) (f : A.a ⟶ B.a) :
    G.map (E.functor.map f) ≫ (mappedAlgebra E α B).str =
        (mappedAlgebra E α A).str ≫ E.functor.map f ↔
      F.map f ≫ B.str = A.str ≫ f := by
  change G.map (E.functor.map f) ≫ (α.inv.app B.a ≫ E.functor.map B.str) =
    (α.inv.app A.a ≫ E.functor.map A.str) ≫ E.functor.map f ↔ _
  have hn : G.map (E.functor.map f) ≫ α.inv.app B.a =
      α.inv.app A.a ≫ E.functor.map (F.map f) := by
    simpa only [Functor.comp_map] using α.inv.naturality f
  rw [← Category.assoc, hn, Category.assoc, Category.assoc,
    ← E.functor.map_comp, ← E.functor.map_comp]
  rw [cancel_epi, E.functor.map_injective.eq_iff]

def functor : Endofunctor.Algebra F ⥤ Endofunctor.Algebra G where
  obj := mappedAlgebra E α
  map f := ⟨E.functor.map f.f, (hom_condition_iff E α _ _ f.f).mpr f.h⟩
  map_id A := Endofunctor.Algebra.Hom.ext (E.functor.map_id A.a)
  map_comp f g := Endofunctor.Algebra.Hom.ext (E.functor.map_comp f.f g.f)

instance functor_faithful : (functor E α).Faithful where
  map_injective h := Endofunctor.Algebra.Hom.ext
    (E.functor.map_injective (congrArg Endofunctor.Algebra.Hom.f h))

instance functor_full : (functor E α).Full where
  map_surjective {A B} f := by
    let g := E.functor.preimage f.f
    have hg : E.functor.map g = f.f := E.functor.map_preimage f.f
    refine ⟨⟨g, (hom_condition_iff E α A B g).mp ?_⟩, ?_⟩
    · rw [hg]
      exact f.h
    · exact Endofunctor.Algebra.Hom.ext hg

/-- Pull an arbitrary target algebra back along the inverse equivalence,
using fullness to construct its structure morphism. -/
def liftedAlgebra (B : Endofunctor.Algebra G) : Endofunctor.Algebra F where
  a := E.inverse.obj B.a
  str := E.functor.preimage (α.hom.app (E.inverse.obj B.a) ≫
    G.map (E.counitIso.app B.a).hom ≫ B.str ≫ (E.counitIso.app B.a).inv)

def mappedLiftIso (B : Endofunctor.Algebra G) :
    (functor E α).obj (liftedAlgebra E α B) ≅ B :=
  Endofunctor.Algebra.isoMk (E.counitIso.app B.a) (by
    change _ = (α.inv.app (E.inverse.obj B.a) ≫
      E.functor.map (E.functor.preimage _)) ≫ _
    rw [E.functor.map_preimage]
    simp only [Category.assoc, Iso.inv_hom_id_app_assoc, Iso.inv_hom_id,
      Category.comp_id])

instance functor_essSurj : (functor E α).EssSurj where
  mem_essImage B := ⟨liftedAlgebra E α B, ⟨mappedLiftIso E α B⟩⟩

instance functor_isEquivalence : (functor E α).IsEquivalence := {}

/-- The base comparison induces an actual equivalence of the
algebra categories, including all algebra morphisms. -/
def equivalence : Endofunctor.Algebra F ≌ Endofunctor.Algebra G :=
  (functor E α).asEquivalence

def initial (A : Endofunctor.Algebra F) (hA : IsInitial A) :
    IsInitial (mappedAlgebra E α A) :=
  IsInitial.isInitialObj (functor E α) A hA

def initialIff (A : Endofunctor.Algebra F) :
    IsInitial A ≃ IsInitial (mappedAlgebra E α A) :=
  IsInitial.isInitialIffObj (functor E α) A

end CategoricalEssentialIncompleteness.V46.AlgebraTransport
