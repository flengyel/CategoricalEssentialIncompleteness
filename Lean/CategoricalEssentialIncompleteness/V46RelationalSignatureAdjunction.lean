/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46RelationalSignature
public import Mathlib.CategoryTheory.Adjunction.Basic

/-! # The adjunction for substitution of formulas for relation symbols

Voutsadakis' Theorem 7, cited before Theorem 4.7, takes a map of hierarchies
to a signature morphism by viewing each target symbol as an atomic formula.
The right adjoint takes a signature to its hierarchy of formulas and a
signature morphism to substitution on formulas.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory

namespace CategoricalEssentialIncompleteness.V46.Voutsadakis

/-- A relational signature has a hierarchy of symbols. Its morphisms assign
a target formula to a source symbol in each finite variable context. -/
structure Signature where
  symbols : HSet.{u}

def generators (A : HSet.{u}) : A ⟶ Formula.hierarchy A :=
  ⟨Formula.symbol, fun _ _ h ↦ h⟩

def substitution {A B : HSet.{u}} (f : A ⟶ Formula.hierarchy B) :
    Formula.hierarchy A ⟶ Formula.hierarchy B :=
  ⟨Formula.substitute f.map, fun N p ↦ Formula.substitute_supported f p N⟩

instance : Category Signature.{u} where
  Hom X Y := X.symbols ⟶ Formula.hierarchy Y.symbols
  id X := generators X.symbols
  comp f g := f ≫ substitution g
  id_comp _ := HSet.Hom.ext fun _ ↦ rfl
  comp_id f := HSet.Hom.ext fun x ↦ Formula.substitute_symbol (f.map x)
  assoc f g h := HSet.Hom.ext fun x ↦ Formula.substitute_substitute g.map h.map (f.map x)

def freeSignature : HSet.{u} ⥤ Signature.{u} where
  obj A := ⟨A⟩
  map {A B} f := (⟨fun x ↦ Formula.symbol (f.map x), fun N x h ↦ f.map_mem N x h⟩ :
    A ⟶ Formula.hierarchy B)
  map_id _ := HSet.Hom.ext fun _ ↦ rfl
  map_comp _ _ := HSet.Hom.ext fun _ ↦ rfl

def formulas : Signature.{u} ⥤ HSet.{u} where
  obj X := Formula.hierarchy X.symbols
  map f := substitution f
  map_id _ := HSet.Hom.ext Formula.substitute_symbol
  map_comp f g := HSet.Hom.ext fun p ↦ (Formula.substitute_substitute f.map g.map p).symm

/-- A signature morphism with source `freeSignature.obj A` assigns to every
symbol of `A` a formula in its context. This is the hom-set equivalence
of Voutsadakis' Theorem 7. -/
def signatureAdjunction : freeSignature.{u} ⊣ formulas.{u} :=
  Adjunction.mkOfHomEquiv {
    homEquiv := fun A X ↦ Equiv.refl (A ⟶ Formula.hierarchy X.symbols)
    homEquiv_naturality_left_symm := fun _ _ ↦ HSet.Hom.ext fun _ ↦ rfl
    homEquiv_naturality_right := fun _ _ ↦ HSet.Hom.ext fun _ ↦ rfl }

theorem unit_app (A : HSet.{u}) : signatureAdjunction.unit.app A = generators A := rfl

theorem counit_app (X : Signature.{u}) :
    signatureAdjunction.counit.app X = (𝟙 (Formula.hierarchy X.symbols)) := rfl

end CategoricalEssentialIncompleteness.V46.Voutsadakis
