import CategoricalEssentialIncompleteness.V46AlgebraTransport
import Mathlib.CategoryTheory.Comma.Over.Basic

/-! A fold into a validator algebra induces an initial algebra in its slice. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v u
open CategoryTheory CategoryTheory.Limits

namespace CategoricalEssentialIncompleteness.V46.SyntacticDerivation.SliceInitial
variable {D : Type u} [Category.{v} D] (S : D ⥤ D)
variable (V : Endofunctor.Algebra S)

abbrev functor : Over V.a ⥤ Over V.a where
  obj X := Over.mk (S.map X.hom ≫ V.str)
  map f := Over.homMk (S.map f.left) (by
    change S.map f.left ≫ (S.map _ ≫ V.str) = S.map _ ≫ V.str
    rw [← Category.assoc, ← S.map_comp, Over.w f])
  map_id X := by
    apply Over.OverMorphism.ext
    exact S.map_id X.left
  map_comp f g := by
    apply Over.OverMorphism.ext
    exact S.map_comp f.left g.left

def underlying (B : Endofunctor.Algebra (functor S V)) : Endofunctor.Algebra S where
  a := B.a.left
  str := B.str.left

def underlyingHom (B : Endofunctor.Algebra (functor S V)) : underlying S V B ⟶ V :=
  ⟨B.a.hom, (Over.w B.str).symm⟩

def algebra (A : Endofunctor.Algebra S) (hA : IsInitial A) :
    Endofunctor.Algebra (functor S V) where
  a := Over.mk (hA.to V).f
  str := Over.homMk A.str ((hA.to V).h.symm)

def fold (A : Endofunctor.Algebra S) (hA : IsInitial A)
    (B : Endofunctor.Algebra (functor S V)) : algebra S V A hA ⟶ B where
  f := Over.homMk (hA.to (underlying S V B)).f (by
    exact congrArg Endofunctor.Algebra.Hom.f
      (hA.hom_ext (hA.to (underlying S V B) ≫ underlyingHom S V B) (hA.to V)))
  h := by
    apply Over.OverMorphism.ext
    exact (hA.to (underlying S V B)).h

/-- Arbitrary slice-algebra arrows are unique because their underlying
arrows are ordinary algebra arrows; the slice condition is derived from
the validator fold, rather than assumed on the candidate evaluation. -/
def initial (A : Endofunctor.Algebra S) (hA : IsInitial A) :
    IsInitial (algebra S V A hA) :=
  IsInitial.ofUniqueHom (fold S V A hA) (by
    intro B f
    apply Endofunctor.Algebra.Hom.ext
    apply Over.OverMorphism.ext
    exact congrArg Endofunctor.Algebra.Hom.f
      (hA.hom_ext (⟨f.f.left, congrArg Over.Hom.left f.h⟩ : A ⟶ underlying S V B)
        (hA.to (underlying S V B))))

end CategoricalEssentialIncompleteness.V46.SyntacticDerivation.SliceInitial
