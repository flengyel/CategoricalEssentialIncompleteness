/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.ForkSyntaxInitial
public import Mathlib.CategoryTheory.Endofunctor.Algebra

/-! # The initial polynomial algebra in the total fork category -/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open CategoryTheory CategoryTheory.RestrictionCategory CategoryTheory.Limits
open CategoryTheory.PCategoryStruct CategoryTheory.CoprodStruct CategoryTheory.HasCoproducts

namespace CategoricalEssentialIncompleteness.LocalConnectedness.ForkSyntax

open EffectiveFork (Object Total)

theorem productMap_total {W X Y Z : Object} (f : W ⟶ X) (g : Y ⟶ Z)
    (hf : isTotal f) (hg : isTotal g) : isTotal (EffectiveFork.productMap f g) := by
  obtain ⟨hf0,hf1,hf2⟩ := (EffectiveFork.total_iff f).mp hf
  obtain ⟨hg0,hg1,hg2⟩ := (EffectiveFork.total_iff g).mp hg
  exact (EffectiveFork.total_iff _).mpr ⟨
    EnumerableCarriers.partialProdMap_total _ _ hf0 hg0,
    EnumerableCarriers.partialProdMap_total _ _ hf1 hg1,
    EnumerableCarriers.partialProdMap_total _ _ hf2 hg2⟩

theorem polynomial_map_total {X Y : Object} (f : X ⟶ Y) (hf : isTotal f) :
    isTotal (polynomial.map f) := by
  have hp := productMap_total f f hf hf
  change RestrictionCategory.rst (coprod_map (coprod_map (𝟙 EffectiveFork.V) f)
    (EffectiveFork.productMap f f))=𝟙 _
  rw [restrict_sum,restrict_sum,rst_id,hf,hp,coprod_id,coprod_id]

def polynomialTotal : Total ⥤ Total where
  obj X := ⟨polynomial.obj X.obj⟩
  map f := ⟨polynomial.map f.hom,polynomial_map_total f.hom f.property⟩
  map_id X := by apply WideSubcategory.hom_ext; exact polynomial.map_id X.obj
  map_comp f g := by apply WideSubcategory.hom_ext; exact polynomial.map_comp f.hom g.hom

theorem iota_total : isTotal iota := by
  change RestrictionCategory.rst (copair (copair theta nu) implication)=𝟙 _
  rw [restrict_copair,restrict_copair,theta_total,nu_total,implication_total,
    coprod_id,coprod_id]

def syntaxAlgebra : Endofunctor.Algebra polynomialTotal :=
  ⟨⟨S⟩,⟨iota,iota_total⟩⟩

def foldHom (A : Endofunctor.Algebra polynomialTotal) : syntaxAlgebra ⟶ A where
  f := ⟨(constructors A.str.hom A.str.property).fold,
    (constructors A.str.hom A.str.property).fold_total⟩
  h := by
    apply WideSubcategory.hom_ext
    exact (fold_algebra A.str.hom A.str.property).symm

/-- Proposition 10.2 in the category of total recursive fork maps. -/
def syntaxAlgebra_isInitial : IsInitial syntaxAlgebra :=
  IsInitial.ofUniqueHom foldHom (by
    intro A m
    apply Endofunctor.Algebra.Hom.ext
    apply WideSubcategory.hom_ext
    exact (syntax_initial A.str.hom A.str.property).unique
      ⟨m.f.property,(congrArg (fun k => k.hom) m.h).symm⟩
      ⟨(constructors A.str.hom A.str.property).fold_total,
        fold_algebra A.str.hom A.str.property⟩)

end CategoricalEssentialIncompleteness.LocalConnectedness.ForkSyntax
