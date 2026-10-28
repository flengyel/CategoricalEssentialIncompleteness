/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.Diagonal
import PCats.DomSemilattice
import PCats.DomTotalEmbedding

/-!
# Restriction idempotents as an indexed predicate lattice

The order and meet are the existing domain order and composition. Joins and
their stability are additional data, as in the manuscript. Restriction zeros
are assumed directly; ranges, coproducts, and density hypotheses are unnecessary.
-/

set_option autoImplicit false

noncomputable section

universe v u

open CategoryTheory CategoryTheory.Limits CategoryTheory.PCategoryStruct
open CategoryTheory.RestrictionCategory (TotalSubcategory)

namespace CategoricalEssentialIncompleteness

variable {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]

/-- The actual inverse image of a restriction idempotent. -/
def domainInverseImage {X Y : C} (f : X ⟶ Y) (e : DomSemilattice Y) : DomSemilattice X :=
  ⟨rst (f ≫ e.hom), PCategory.rst_rst _⟩

theorem domainInverseImage_meet {X Y : C} (f : X ⟶ Y) (a b : DomSemilattice Y) :
    domainInverseImage f (DomSemilattice.meet a b) =
      DomSemilattice.meet (domainInverseImage f a) (domainInverseImage f b) := by
  apply DomSemilattice.ext'
  have h : rst (f ≫ a.hom) ≫ f = f ≫ a.hom := by
    rw [PCategory.rst_comp', a.isDomain]
  change rst (f ≫ (a.hom ≫ b.hom)) = rst (f ≫ a.hom) ≫ rst (f ≫ b.hom)
  calc
    _ = rst ((rst (f ≫ a.hom) ≫ f) ≫ b.hom) := by rw [h, Category.assoc]
    _ = _ := by rw [Category.assoc, PCategory.rst_comp_rst']

/-- Binary joins on the existing domain order, with distributivity and stability
under total inverse image. No complement for an arbitrary domain is specified. -/
class DomainJoins (C : Type u) [Category.{v} C] [PCategoryStruct C] [PCategory C] where
  join : ∀ {X : C}, DomSemilattice X → DomSemilattice X → DomSemilattice X
  le_join_left : ∀ {X : C} (a b : DomSemilattice X), a ≤ join a b
  le_join_right : ∀ {X : C} (a b : DomSemilattice X), b ≤ join a b
  join_le : ∀ {X : C} (a b c : DomSemilattice X), a ≤ c → b ≤ c → join a b ≤ c
  distrib : ∀ {X : C} (a b c : DomSemilattice X),
    DomSemilattice.meet (join a b) (join a c) ≤ join a (DomSemilattice.meet b c)
  pull_join : ∀ {X Y : C} (f : X ⟶ Y), RestrictionCategory.isTotal f →
    ∀ a b : DomSemilattice Y,
      domainInverseImage f (join a b) = join (domainInverseImage f a) (domainInverseImage f b)

instance domainDistribLattice [DomainJoins C] (X : C) : DistribLattice (DomSemilattice X) :=
  { (inferInstance : PartialOrder (DomSemilattice X)) with
    inf := DomSemilattice.meet
    inf_le_left := DomSemilattice.meet_le_left
    inf_le_right := DomSemilattice.meet_le_right
    le_inf _ _ _ := DomSemilattice.le_meet
    sup := DomainJoins.join
    le_sup_left := DomainJoins.le_join_left
    le_sup_right := DomainJoins.le_join_right
    sup_le := DomainJoins.join_le
    le_sup_inf := DomainJoins.distrib }

/-- Restriction zeros are precisely the extra zero law used below. -/
class RestrictionZeros (C : Type u) [Category.{v} C] [PCategoryStruct C]
    [HasZeroMorphisms C] : Prop where
  rst_zero : ∀ X Y : C, rst (0 : X ⟶ Y) = 0

/-- The existing prodominical hypothesis implies the required restriction-zero law. -/
instance [HasZeroMorphisms C] [CategoryTheory.RecursionCategory.Prodominical C] :
    RestrictionZeros C := ⟨DomSemilattice.rst_zero⟩

instance domainBoundedOrder [HasZeroMorphisms C] [RestrictionZeros C] (X : C) :
    BoundedOrder (DomSemilattice X) where
  top := DomSemilattice.top X
  le_top := DomSemilattice.le_top
  bot := ⟨0, RestrictionZeros.rst_zero X X⟩
  bot_le a := by change (0 : X ⟶ X) ≫ a.hom = 0; simp

/-- The existing near-product cone is a categorical product of total arrows. -/
def totalBinaryProductLimit (X Y : TotalSubcategory C) :
    IsLimit (BinaryFan.mk (TotalSubcategory.binaryProductFst X Y)
      (TotalSubcategory.binaryProductSnd X Y)) :=
  BinaryFan.isLimitMk
    (fun t => TotalSubcategory.binaryProductLift t.fst t.snd)
    (fun t => TotalSubcategory.binaryProductLift_fst t.fst t.snd)
    (fun t => TotalSubcategory.binaryProductLift_snd t.fst t.snd)
    (fun _ m hf hg => TotalSubcategory.binaryProductLift_unique m hf hg)

instance totalHasBinaryProduct (X Y : TotalSubcategory C) : HasLimit (pair X Y) :=
  ⟨⟨_, totalBinaryProductLimit X Y⟩⟩

instance totalHasBinaryProducts : HasBinaryProducts (TotalSubcategory C) :=
  hasBinaryProducts_of_hasLimit_pair (TotalSubcategory C)

variable [DomainJoins C] [HasZeroMorphisms C] [RestrictionZeros C]

/-- Total inverse image as a bounded lattice homomorphism. -/
def domainPull {X Y : C} (f : X ⟶ Y) (hf : RestrictionCategory.isTotal f) :
    BoundedLatticeHom (DomSemilattice Y) (DomSemilattice X) where
  toFun := domainInverseImage f
  map_sup' := DomainJoins.pull_join f hf
  map_inf' := domainInverseImage_meet f
  map_top' := by
    apply DomSemilattice.ext'
    change rst (f ≫ 𝟙 Y) = 𝟙 X
    rw [Category.comp_id]
    exact hf
  map_bot' := by
    apply DomSemilattice.ext'
    change rst (f ≫ 0) = 0
    rw [comp_zero, RestrictionZeros.rst_zero]

/-- `E` on the genuine total-arrow category, with `f* e = rst (f ≫ e)`. -/
def restrictionPredicates : PredicateLattice (TotalSubcategory C) where
  obj X := DomSemilattice X.obj
  lattice _ := inferInstance
  bounds _ := inferInstance
  pull f := domainPull f.hom f.property
  pull_id X e := by
    apply DomSemilattice.ext'
    change rst (𝟙 X.obj ≫ e.hom) = e.hom
    rw [Category.id_comp, e.isDomain]
  pull_comp f g e := by
    apply DomSemilattice.ext'
    change rst ((f.hom ≫ g.hom) ≫ e.hom) = rst (f.hom ≫ rst (g.hom ≫ e.hom))
    rw [Category.assoc, ← PCategory.rst_comp_rst_right']

/-- The lattice nontriviality premise is exactly the identity/zero distinction. -/
theorem restrictionPredicates_nontrivial (U : TotalSubcategory C)
    (hU : (𝟙 U.obj : U.obj ⟶ U.obj) ≠ 0) :
    (⊥ : (restrictionPredicates (C := C)).obj U) ≠ ⊤ := by
  intro h
  exact hU (congrArg DomSemilattice.hom h).symm

/-- The external diagonal theorem on genuine restriction idempotents and total arrows. -/
theorem restriction_integration_diagonal
    {P : PredicateLattice (TotalSubcategory C)}
    (D : DiagonalData (restrictionPredicates (C := C)) P)
    (hU : (𝟙 D.U.obj : D.U.obj ⟶ D.U.obj) ≠ 0)
    (a : ComplementaryPair (DomSemilattice D.S.obj)) (ha : D.Separates a) :
    ¬ ∃ g, D.Represents (D.diagonalPair a) g :=
  D.integration_diagonal (restrictionPredicates_nontrivial D.U hU) a ha

/-- Global inseparability for representation of every complemented domain. -/
theorem restriction_inseparable
    {P : PredicateLattice (TotalSubcategory C)}
    (D : DiagonalData (restrictionPredicates (C := C)) P)
    (hU : (𝟙 D.U.obj : D.U.obj ⟶ D.U.obj) ≠ 0)
    (represent : ∀ a : ComplementaryPair (DomSemilattice D.U.obj), ∃ g, D.Represents a g) :
    ¬ ∃ a, D.Separates a :=
  D.inseparable (restrictionPredicates_nontrivial D.U hU) represent

end CategoricalEssentialIncompleteness
