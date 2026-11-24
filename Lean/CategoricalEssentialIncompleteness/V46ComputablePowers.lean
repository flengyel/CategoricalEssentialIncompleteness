/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ApplicativePolynomials
public import Mathlib.CategoryTheory.Functor.FullyFaithful

/-! # The category of computable morphisms on formal finite powers -/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory PCategoryStruct PCategory RecursionCategory RestrictionCategory

namespace CategoricalEssentialIncompleteness.V46.ApplicativeSystem

universe v u
variable {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
variable {A Z : C} (app : nearProd A A ⟶ A) (t : ∀ X : C, X ⟶ Z)

/-- Restriction terminality determines a morphism to the empty power from its domain. -/
theorem computable_to_terminal_iff (n : ℕ) (f : power Z A (n+1) ⟶ Z) :
    Computable app t (n+1) 0 f ↔
      Computable app t (n+1) (n+1) (PCategoryStruct.rst f) := Iff.rfl

/-- Objects of the polynomial category are formal finite powers. Under combinatory
completeness its morphisms are exactly the computable morphisms of Definition 4.2. -/
structure Powers (app : nearProd A A ⟶ A) (t : ∀ X : C, X ⟶ Z) where
  arity : ℕ

instance : Category.{v} (Powers app t) where
  Hom X Y := {f : power Z A X.arity ⟶ power Z A Y.arity // Polynomial app t X.arity Y.arity f}
  id X := ⟨𝟙 _, .ident X.arity⟩
  comp f g := ⟨f.val ≫ g.val, f.property.comp g.property⟩
  id_comp f := Subtype.ext (Category.id_comp f.val)
  comp_id f := Subtype.ext (Category.comp_id f.val)
  assoc f g h := Subtype.ext (Category.assoc f.val g.val h.val)

instance : RestrictionCategory (Powers app t) where
  rst f := ⟨PCategoryStruct.rst f.val, f.property.domain⟩
  rst_comp_self f := Subtype.ext (RestrictionCategory.rst_comp_self f.val)
  rst_comm f g := Subtype.ext (RestrictionCategory.rst_comm f.val g.val)
  rst_comp_rst f g := Subtype.ext (RestrictionCategory.rst_comp_rst f.val g.val)
  rst_comp f g := Subtype.ext (RestrictionCategory.rst_comp f.val g.val)

def inclusion : Powers app t ⥤ C where
  obj X := power Z A X.arity
  map f := f.val
  map_id _ := rfl
  map_comp _ _ := rfl

instance : (inclusion app t).Faithful where
  map_injective := fun h => Subtype.ext h

/-- Morphisms of the category give all and only the computations of the specified arities. -/
def homEquiv (complete : CombinatoriallyComplete app t)
    (unit : ∀ {X : C} (f : X ⟶ Z), f = PCategoryStruct.rst f ≫ t X)
    (X Y : Powers app t) :
    (X ⟶ Y) ≃ {f : power Z A X.arity ⟶ power Z A Y.arity //
      Computable app t X.arity Y.arity f} where
  toFun f := ⟨f.val, (polynomial_iff_computable app t complete unit _ _ _).mp f.property⟩
  invFun f := ⟨f.val, (polynomial_iff_computable app t complete unit _ _ _).mpr f.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem all_polynomial (h : IsTuringMorphism app) (ht : isTotal (t A))
    (unit : ∀ {X : C} (f : X ⟶ Z), f = PCategoryStruct.rst f ≫ t X)
    (n m : ℕ) (f : power Z A n ⟶ power Z A m) : Polynomial app t n m f := by
  apply (polynomial_iff_computable app t (turing_combinatoriallyComplete app t h ht)
    unit n m f).mpr
  have coords (i j : ℕ) (g : power Z A i ⟶ positivePower A j) : CodedCoordinates app t i j g := by
    induction j with
    | zero => exact exists_code app t h ht i _
    | succ j ih => exact ⟨ih _, exists_code app t h ht i _⟩
  cases m with
  | zero =>
    cases n with
    | zero =>
      obtain ⟨p, hp⟩ := exists_code app t h ht 1 (𝟙 A)
      have total : isTotal p := hp.1
      exact ⟨f ≫ p, (rst_comp_of_isTotal' f total).symm, exists_code app t h ht 0 _⟩
    | succ n => exact coords (n+1) n _
  | succ k => exact coords n k f

def fullyFaithfulInclusion (h : IsTuringMorphism app) (ht : isTotal (t A))
    (unit : ∀ {X : C} (f : X ⟶ Z), f = PCategoryStruct.rst f ≫ t X) :
    (inclusion app t).FullyFaithful where
  preimage f := ⟨f, all_polynomial app t h ht unit _ _ f⟩
  map_preimage _ := rfl
  preimage_map _ := rfl

end CategoricalEssentialIncompleteness.V46.ApplicativeSystem
