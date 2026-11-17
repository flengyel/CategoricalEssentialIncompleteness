/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ForkDerivationDiagram

/-! # Propositional folds on the original fork formula carrier -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.RestrictionCategory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.LocalConnectedness
namespace CategoricalEssentialIncompleteness.V46.ForkPropositionalFolds
open ForkDerivation

def codedMap {W X Y Z : EffectiveFork.Total}
    (f : W ⟶ X) (g : Y ⟶ Z) :
    codedProduct W Y ⟶ codedProduct X Z :=
  ⟨EffectiveFork.productMap f.hom g.hom,
    ForkSyntax.productMap_total _ _ f.property g.property⟩

@[reassoc (attr := simp)] theorem codedMap_fst {W X Y Z : EffectiveFork.Total}
    (f : W ⟶ X) (g : Y ⟶ Z) :
    codedMap f g ≫ codedFst X Z = codedFst W Y ≫ f := by
  apply WideSubcategory.hom_ext
  apply EffectiveFork.Hom.ext
  · exact EnumerableCarriers.partialProdMap_fst_of_total_right _ _
      ((EffectiveFork.total_iff _).mp g.property).1
  · exact EnumerableCarriers.partialProdMap_fst_of_total_right _ _
      ((EffectiveFork.total_iff _).mp g.property).2.1
  · exact EnumerableCarriers.partialProdMap_fst_of_total_right _ _
      ((EffectiveFork.total_iff _).mp g.property).2.2

@[reassoc (attr := simp)] theorem codedMap_snd {W X Y Z : EffectiveFork.Total}
    (f : W ⟶ X) (g : Y ⟶ Z) :
    codedMap f g ≫ codedSnd X Z = codedSnd W Y ≫ g := by
  apply WideSubcategory.hom_ext
  apply EffectiveFork.Hom.ext
  · exact EnumerableCarriers.partialProdMap_snd_of_total_left _ _
      ((EffectiveFork.total_iff _).mp f.property).1
  · exact EnumerableCarriers.partialProdMap_snd_of_total_left _ _
      ((EffectiveFork.total_iff _).mp f.property).2.1
  · exact EnumerableCarriers.partialProdMap_snd_of_total_left _ _
      ((EffectiveFork.total_iff _).mp f.property).2.2

theorem productComparison_natural {W X Y Z : EffectiveFork.Total}
    (f : W ⟶ X) (g : Y ⟶ Z) :
    (productComparison W Y).hom ≫ codedMap f g =
      prod.map f g ≫ (productComparison X Z).hom := by
  apply codedProduct_hom_ext <;> simp [Category.assoc, productComparison_fst_assoc,
    productComparison_snd_assoc]

def operations (Z : EffectiveFork.Total) (a : variableObject ⟶ Z) (n : Z ⟶ Z)
    (i : Z ⨯ Z ⟶ Z) : ForkSyntax.Algebra Z.obj where
  atom := a.hom
  neg := n.hom
  imp := ((productComparison Z Z).inv ≫ i).hom
  atom_total := a.property
  neg_total := n.property
  imp_total := ((productComparison Z Z).inv ≫ i).property

def totalFold (Z : EffectiveFork.Total) (a : variableObject ⟶ Z) (n : Z ⟶ Z)
    (i : Z ⨯ Z ⟶ Z) : sentenceObject ⟶ Z :=
  ⟨(operations Z a n i).fold, (operations Z a n i).fold_total⟩

@[reassoc] theorem totalFold_atom (Z : EffectiveFork.Total) (a : variableObject ⟶ Z)
    (n : Z ⟶ Z) (i : Z ⨯ Z ⟶ Z) : atom ≫ totalFold Z a n i = a := by
  apply WideSubcategory.hom_ext
  exact (operations Z a n i).atom_fold

@[reassoc] theorem totalFold_negation (Z : EffectiveFork.Total) (a : variableObject ⟶ Z)
    (n : Z ⟶ Z) (i : Z ⨯ Z ⟶ Z) : negation ≫ totalFold Z a n i = totalFold Z a n i ≫ n := by
  apply WideSubcategory.hom_ext
  exact (operations Z a n i).neg_fold

@[reassoc] theorem totalFold_implication (Z : EffectiveFork.Total) (a : variableObject ⟶ Z)
    (n : Z ⟶ Z) (i : Z ⨯ Z ⟶ Z) : implication ≫ totalFold Z a n i =
      prod.map (totalFold Z a n i) (totalFold Z a n i) ≫ i := by
  have h : (⟨ForkSyntax.implication, ForkSyntax.implication_total⟩ :
      codedProduct sentenceObject sentenceObject ⟶ sentenceObject) ≫ totalFold Z a n i =
        codedMap (totalFold Z a n i) (totalFold Z a n i) ≫
          (productComparison Z Z).inv ≫ i := by
    apply WideSubcategory.hom_ext
    exact (operations Z a n i).imp_fold
  unfold implication
  rw [Category.assoc, h, ← Category.assoc, ← Category.assoc,
    productComparison_natural]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]

theorem totalFold_unique (Z : EffectiveFork.Total) (a : variableObject ⟶ Z)
    (n : Z ⟶ Z) (i : Z ⨯ Z ⟶ Z) (m : sentenceObject ⟶ Z)
    (ha : atom ≫ m = a) (hn : negation ≫ m = m ≫ n)
    (hi : implication ≫ m = prod.map m m ≫ i) : m = totalFold Z a n i := by
  apply WideSubcategory.hom_ext
  apply (operations Z a n i).fold_unique
  · exact congrArg (fun k => k.hom) ha
  · exact congrArg (fun k => k.hom) hn
  · have h : (⟨ForkSyntax.implication, ForkSyntax.implication_total⟩ :
        codedProduct sentenceObject sentenceObject ⟶ sentenceObject) ≫ m =
          codedMap m m ≫ (productComparison Z Z).inv ≫ i := by
      apply (cancel_epi (productComparison sentenceObject sentenceObject).hom).mp
      rw [← Category.assoc, ← Category.assoc, productComparison_natural,
        Category.assoc]
      simpa only [implication, Category.assoc, Iso.hom_inv_id_assoc] using hi
    exact congrArg (fun k => k.hom) h

open Diagram
variable (Y : Object) (a : realization.obj variableObject ⟶ Y) (n : Y ⟶ Y)
variable (i : Y ⨯ Y ⟶ Y)

abbrev target := equivalence.inverse.obj Y
abbrev counit := equivalence.counitIso.app Y

def liftedAtom : variableObject ⟶ target Y := realization.preimage (a ≫ (counit Y).inv)
def liftedNegation : target Y ⟶ target Y :=
  realization.preimage ((counit Y).hom ≫ n ≫ (counit Y).inv)
def liftedImplication : target Y ⨯ target Y ⟶ target Y :=
  realization.preimage (prodComparison realization (target Y) (target Y) ≫
    prod.map (counit Y).hom (counit Y).hom ≫ i ≫ (counit Y).inv)

def fold : sentences ⟶ Y := realization.map
  (totalFold (target Y) (liftedAtom Y a) (liftedNegation Y n) (liftedImplication Y i)) ≫
    (counit Y).hom

@[reassoc] theorem fold_atom : realization.map atom ≫ fold Y a n i = a := by
  simp only [fold, ← realization.map_comp_assoc, totalFold_atom, liftedAtom,
    realization.map_preimage, Category.assoc, Iso.inv_hom_id, Category.comp_id]

@[reassoc] theorem fold_negation : realization.map negation ≫ fold Y a n i =
    fold Y a n i ≫ n := by
  simp only [fold, ← realization.map_comp_assoc, totalFold_negation, realization.map_comp,
    liftedNegation, realization.map_preimage, Category.assoc, Iso.inv_hom_id,
    Category.comp_id]

@[reassoc] theorem fold_implication : Diagram.implication ≫ fold Y a n i =
    prod.map (fold Y a n i) (fold Y a n i) ≫ i := by
  simp only [Diagram.implication, fold, Category.assoc, ← realization.map_comp_assoc,
    totalFold_implication, realization.map_comp, liftedImplication, realization.map_preimage]
  erw [prodComparison_natural_assoc]
  simp only [Category.assoc, IsIso.inv_hom_id_assoc, Iso.inv_hom_id,
    Category.comp_id, ← prod.map_map]

/-- Uniqueness is transported through the actual full and faithful realization. -/
theorem unique (m : sentences ⟶ Y) (ha : realization.map atom ≫ m = a)
    (hn : realization.map negation ≫ m = m ≫ n)
    (hi : Diagram.implication ≫ m = prod.map m m ≫ i) : m = fold Y a n i := by
  let k : sentenceObject ⟶ target Y := realization.preimage (m ≫ (counit Y).inv)
  have hk : realization.map k = m ≫ (counit Y).inv := realization.map_preimage _
  have h : k = totalFold (target Y) (liftedAtom Y a)
      (liftedNegation Y n) (liftedImplication Y i) := by
    apply totalFold_unique
    · apply realization.map_injective
      simpa only [realization.map_comp, hk, liftedAtom, realization.map_preimage,
        ← Category.assoc] using congrArg (fun f => f ≫ (counit Y).inv) ha
    · apply realization.map_injective
      simpa only [realization.map_comp, hk, liftedNegation, realization.map_preimage,
        Category.assoc, Iso.inv_hom_id_assoc] using
          congrArg (fun f => f ≫ (counit Y).inv) hn
    · apply realization.map_injective
      simp only [realization.map_comp, liftedImplication, realization.map_preimage]
      erw [prodComparison_natural_assoc]
      simp only [hk, Category.assoc, prod.map_map_assoc,
        Iso.inv_hom_id, Category.comp_id]
      apply (cancel_epi (inv (prodComparison realization sentenceObject sentenceObject))).mp
      simpa only [Category.assoc, IsIso.inv_hom_id_assoc, Diagram.implication] using
        congrArg (fun f => f ≫ (counit Y).inv) hi
  calc
    m = realization.map k ≫ (counit Y).hom := by
      rw [hk, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    _ = fold Y a n i := by rw [h]; rfl

end CategoricalEssentialIncompleteness.V46.ForkPropositionalFolds
