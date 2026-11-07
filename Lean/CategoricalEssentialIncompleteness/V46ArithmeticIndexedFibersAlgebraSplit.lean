/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46AlgebraTransport

/-! # The product-algebra step in the extensive fiber argument

This constructs the algebra equivalence for a product endofunctor and
proves the initiality of its two components. The indexed inference
application still requires its separately constructed slice equivalence
and constructor-preserving natural isomorphism.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u₁ u₂ v₁ v₂
open CategoryTheory CategoryTheory.Limits

namespace CategoricalEssentialIncompleteness.V46.ArithmeticIndexedAlgebraSplit
variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]

def productInitialFirst (X : C × D) (hX : IsInitial X) : IsInitial X.1 :=
  IsInitial.ofUniqueHom (fun Y => (hX.to (Y,X.2)).1) (by
    intro Y f
    exact congrArg Prod.fst (hX.hom_ext (show X ⟶ (Y,X.2) from (f,𝟙 X.2)) (hX.to (Y,X.2))))

def productInitialSecond (X : C × D) (hX : IsInitial X) : IsInitial X.2 :=
  IsInitial.ofUniqueHom (fun Y => (hX.to (X.1,Y)).2) (by
    intro Y f
    exact congrArg Prod.snd (hX.hom_ext (show X ⟶ (X.1,Y) from (𝟙 X.1,f)) (hX.to (X.1,Y))))

variable (F : C ⥤ C) (G : D ⥤ D)

def split : Endofunctor.Algebra (F.prod G) ⥤
    Endofunctor.Algebra F × Endofunctor.Algebra G where
  obj A := (⟨A.a.1,A.str.1⟩,⟨A.a.2,A.str.2⟩)
  map f := (⟨f.f.1,congrArg Prod.fst f.h⟩,⟨f.f.2,congrArg Prod.snd f.h⟩)
  map_id _A := Prod.ext (Endofunctor.Algebra.Hom.ext rfl) (Endofunctor.Algebra.Hom.ext rfl)
  map_comp _f _g := Prod.ext (Endofunctor.Algebra.Hom.ext rfl) (Endofunctor.Algebra.Hom.ext rfl)

instance split_faithful : (split F G).Faithful where
  map_injective h := by
    apply Endofunctor.Algebra.Hom.ext
    exact Prod.ext (congrArg (fun f => f.1.f) h) (congrArg (fun f => f.2.f) h)

instance split_full : (split F G).Full where
  map_surjective f :=
    ⟨⟨(f.1.f,f.2.f),Prod.ext f.1.h f.2.h⟩,
      Prod.ext (Endofunctor.Algebra.Hom.ext rfl) (Endofunctor.Algebra.Hom.ext rfl)⟩

instance split_essSurj : (split F G).EssSurj where
  mem_essImage B := ⟨⟨(B.1.a,B.2.a),(B.1.str,B.2.str)⟩,⟨Iso.refl _⟩⟩

instance split_isEquivalence : (split F G).IsEquivalence := {}

def equivalence : Endofunctor.Algebra (F.prod G) ≌
    Endofunctor.Algebra F × Endofunctor.Algebra G := (split F G).asEquivalence

def firstInitial (A : Endofunctor.Algebra (F.prod G)) (hA : IsInitial A) :
    IsInitial ((split F G).obj A).1 :=
  productInitialFirst _ (IsInitial.isInitialObj (split F G) A hA)

def secondInitial (A : Endofunctor.Algebra (F.prod G)) (hA : IsInitial A) :
    IsInitial ((split F G).obj A).2 :=
  productInitialSecond _ (IsInitial.isInitialObj (split F G) A hA)

end CategoricalEssentialIncompleteness.V46.ArithmeticIndexedAlgebraSplit
