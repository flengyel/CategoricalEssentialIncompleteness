/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ForkTupleFormulaAlgebraCoordinates
public import CategoricalEssentialIncompleteness.V46ForkSignedAtomInclusion
public import CategoricalEssentialIncompleteness.V46AlgebraTransport

/-! # The initial formula algebra in the tuple diagram category

Proposition 10.2 uses the polynomial with one atom summand, one negation summand
and one binary implication summand. Its comparison with the numerical tree
algebra respects the three constructor inclusions.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.LocalConnectedness

namespace CategoricalEssentialIncompleteness.V46.ForkTupleFormulaAlgebra

open ForkDerivation ForkDerivation.Diagram ForkDiagonalObstruction
open EffectiveFork (Total)

/-- The formula constructor endofunctor in the category of numerical tuple diagrams. -/
def polynomial : Object ⥤ Object where
  obj X := (tupleDiagram ⨿ X) ⨿ (X ⨯ X)
  map f := coprod.map (coprod.map (𝟙 tupleDiagram) f) (prod.map f f)
  map_id X := by simp
  map_comp f g := by simp only [coprod.map_map, prod.map_map, Category.id_comp]

def codedAtom (X : Total) : variableObject ⟶ ForkSyntax.polynomialTotal.obj X :=
  codedInl variableObject X ≫ codedInl (codedSum variableObject X) (codedProduct X X)

def codedNeg (X : Total) : X ⟶ ForkSyntax.polynomialTotal.obj X :=
  codedInr variableObject X ≫ codedInl (codedSum variableObject X) (codedProduct X X)

def codedImp (X : Total) : codedProduct X X ⟶ ForkSyntax.polynomialTotal.obj X :=
  codedInr (codedSum variableObject X) (codedProduct X X)

def sumIso (A B : Total) :
    realization.obj A ⨿ realization.obj B ≅ realization.obj (codedSum A B) :=
  asIso (coprodComparison realization A B) ≪≫ realization.mapIso (sumComparison A B).symm

@[reassoc (attr := simp)] private theorem inl_sumIso (A B : Total) :
    coprod.inl ≫ (sumIso A B).hom = realization.map (codedInl A B) := by
  have h := congrArg (fun f => f ≫ (sumComparison A B).inv) (codedInl_comparison A B)
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id] at h
  simpa only [sumIso, Iso.trans_hom, asIso_hom, Functor.mapIso_hom, Iso.symm_hom,
    coprodComparison, coprod.inl_desc_assoc, ← realization.map_comp] using
    congrArg realization.map h.symm

@[reassoc (attr := simp)] private theorem inr_sumIso (A B : Total) :
    coprod.inr ≫ (sumIso A B).hom = realization.map (codedInr A B) := by
  have h := congrArg (fun f => f ≫ (sumComparison A B).inv) (codedInr_comparison A B)
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id] at h
  simpa only [sumIso, Iso.trans_hom, asIso_hom, Functor.mapIso_hom, Iso.symm_hom,
    coprodComparison, coprod.inr_desc_assoc, ← realization.map_comp] using
    congrArg realization.map h.symm

def productIso (X : Total) :
    realization.obj X ⨯ realization.obj X ≅ realization.obj (codedProduct X X) :=
  (asIso (prodComparison realization X X)).symm ≪≫ realization.mapIso (productComparison X X)

@[reassoc] private theorem productIso_natural {X Y : Total} (f : X ⟶ Y) :
    prod.map (realization.map f) (realization.map f) ≫ (productIso Y).hom =
      (productIso X).hom ≫ realization.map (ForkPropositionalFolds.codedMap f f) := by
  apply (cancel_epi (prodComparison realization X X)).mp
  simp only [productIso, Iso.trans_hom, Iso.symm_hom, asIso_inv, Functor.mapIso_hom,
    ← Category.assoc, ← prodComparison_natural]
  simp only [Category.assoc, IsIso.hom_inv_id_assoc, ← realization.map_comp,
    ForkPropositionalFolds.productComparison_natural]

def arityIso (X : Total) :
    polynomial.obj (realization.obj X) ≅ realization.obj (ForkSyntax.polynomialTotal.obj X) :=
  coprod.mapIso (coprod.mapIso labelCoding (Iso.refl _) ≪≫ sumIso variableObject X)
    (productIso X) ≪≫ sumIso _ _

def atomBranch (X : Object) : tupleDiagram ⟶ polynomial.obj X :=
  (coprod.inl : tupleDiagram ⟶ tupleDiagram ⨿ X) ≫ coprod.inl

def negBranch (X : Object) : X ⟶ polynomial.obj X :=
  (coprod.inr : X ⟶ tupleDiagram ⨿ X) ≫ coprod.inl

def impBranch (X : Object) : X ⨯ X ⟶ polynomial.obj X := coprod.inr

@[reassoc (attr := simp)] private theorem arityIso_atom (X : Total) :
    atomBranch (realization.obj X) ≫ (arityIso X).hom =
      labelCoding.hom ≫ realization.map (codedAtom X) := by
  simp only [atomBranch, arityIso, codedAtom, Iso.trans_hom, coprod.mapIso_hom,
    Category.assoc, coprod.inl_map_assoc, inl_sumIso_assoc, inl_sumIso, Functor.map_comp]

@[reassoc (attr := simp)] private theorem arityIso_neg (X : Total) :
    negBranch (realization.obj X) ≫ (arityIso X).hom = realization.map (codedNeg X) := by
  simp only [negBranch, arityIso, codedNeg, Iso.trans_hom, coprod.mapIso_hom, Iso.refl_hom,
    Category.assoc, coprod.inl_map_assoc, coprod.inr_map_assoc, inl_sumIso, inr_sumIso_assoc,
    Category.id_comp, Functor.map_comp]

@[reassoc (attr := simp)] private theorem arityIso_imp (X : Total) :
    impBranch (realization.obj X) ≫ (arityIso X).hom =
      (productIso X).hom ≫ realization.map (codedImp X) := by
  simp only [impBranch, arityIso, codedImp, Iso.trans_hom, coprod.mapIso_hom,
    coprod.inr_map_assoc, inr_sumIso]

@[reassoc (attr := simp)] private theorem atomBranch_map {X Y : Object} (f : X ⟶ Y) :
    atomBranch X ≫ polynomial.map f = atomBranch Y := by
  simp only [atomBranch, polynomial, Category.assoc, coprod.inl_map, coprod.inl_map_assoc,
    Category.id_comp]

@[reassoc (attr := simp)] private theorem negBranch_map {X Y : Object} (f : X ⟶ Y) :
    negBranch X ≫ polynomial.map f = f ≫ negBranch Y := by
  simp only [negBranch, polynomial, Category.assoc, coprod.inl_map, coprod.inr_map_assoc]

@[reassoc (attr := simp)] private theorem impBranch_map {X Y : Object} (f : X ⟶ Y) :
    impBranch X ≫ polynomial.map f = prod.map f f ≫ impBranch Y := coprod.inr_map _ _

private theorem arity_hom_ext {X Y : Object} {f g : polynomial.obj X ⟶ Y}
    (ha : atomBranch X ≫ f = atomBranch X ≫ g)
    (hn : negBranch X ≫ f = negBranch X ≫ g) (hi : impBranch X ≫ f = impBranch X ≫ g) : f = g :=
  coprod.hom_ext (coprod.hom_ext (by simpa only [atomBranch, Category.assoc] using ha)
    (by simpa only [negBranch, Category.assoc] using hn)) hi

theorem arityIso_natural {X Y : Total} (f : X ⟶ Y) :
    polynomial.map (realization.map f) ≫ (arityIso Y).hom =
      (arityIso X).hom ≫ realization.map (ForkSyntax.polynomialTotal.map f) := by
  have ha : codedAtom X ≫ ForkSyntax.polynomialTotal.map f = codedAtom Y :=
    WideSubcategory.hom_ext _ (ForkSyntax.atomInj_map f.hom)
  have hn : codedNeg X ≫ ForkSyntax.polynomialTotal.map f = f ≫ codedNeg Y :=
    WideSubcategory.hom_ext _ (ForkSyntax.negInj_map f.hom)
  have hi : codedImp X ≫ ForkSyntax.polynomialTotal.map f =
      ForkPropositionalFolds.codedMap f f ≫ codedImp Y :=
    WideSubcategory.hom_ext _ (ForkSyntax.impInj_map f.hom)
  apply arity_hom_ext
  · simp only [atomBranch_map_assoc, arityIso_atom, arityIso_atom_assoc, ← realization.map_comp, ha]
  · simp only [negBranch_map_assoc, arityIso_neg, arityIso_neg_assoc, ← realization.map_comp, hn]
  · simp only [impBranch_map_assoc, arityIso_imp, arityIso_imp_assoc, productIso_natural_assoc,
      ← realization.map_comp, hi]

/-- The comparison sends each constructor inclusion to the same numerical constructor. -/
def polynomialComparison :
    ForkSyntax.polynomialTotal ⋙ realization ≅ realization ⋙ polynomial :=
  (NatIso.ofComponents arityIso (fun f => arityIso_natural f)).symm

def atom : tupleDiagram ⟶ sentences := labelCoding.hom ≫ realization.map ForkDerivation.atom

def negation : sentences ⟶ sentences := realization.map ForkDerivation.negation

/-- The copairing of the atom, negation and implication constructors of §10. -/
def constructor : polynomial.obj sentences ⟶ sentences :=
  coprod.desc (coprod.desc atom negation) Diagram.implication

@[reassoc (attr := simp)] theorem atomBranch_constructor :
    atomBranch sentences ≫ constructor = atom := by
  unfold atomBranch constructor
  rw [Category.assoc, coprod.inl_desc, coprod.inl_desc]

@[reassoc (attr := simp)] theorem negBranch_constructor :
    negBranch sentences ≫ constructor = negation := by
  unfold negBranch constructor
  rw [Category.assoc, coprod.inl_desc, coprod.inr_desc]

@[reassoc (attr := simp)] theorem impBranch_constructor :
    impBranch sentences ≫ constructor = Diagram.implication := coprod.inr_desc _ _

def formulaAlgebra : Endofunctor.Algebra polynomial := ⟨sentences, constructor⟩

theorem mapped_structure :
    (AlgebraTransport.mappedAlgebra equivalence polynomialComparison ForkSyntax.syntaxAlgebra).str =
      constructor := by
  change (arityIso sentenceObject).hom ≫ realization.map ForkSyntax.syntaxAlgebra.str = constructor
  have ha : codedAtom sentenceObject ≫ ForkSyntax.syntaxAlgebra.str = ForkDerivation.atom :=
    WideSubcategory.hom_ext _ ForkSyntax.atomInj_iota
  have hn : codedNeg sentenceObject ≫ ForkSyntax.syntaxAlgebra.str = ForkDerivation.negation :=
    WideSubcategory.hom_ext _ ForkSyntax.negInj_iota
  have hi : codedImp sentenceObject ≫ ForkSyntax.syntaxAlgebra.str =
      (⟨ForkSyntax.implication, ForkSyntax.implication_total⟩ :
        codedProduct sentenceObject sentenceObject ⟶ sentenceObject) :=
    WideSubcategory.hom_ext _ ForkSyntax.impInj_iota
  apply arity_hom_ext
  · rw [arityIso_atom_assoc, ← realization.map_comp, ha]
    exact atomBranch_constructor.symm
  · rw [arityIso_neg_assoc, ← realization.map_comp, hn]
    exact negBranch_constructor.symm
  · rw [arityIso_imp_assoc, ← realization.map_comp, hi]
    change (productIso sentenceObject).hom ≫ _ = impBranch sentences ≫ constructor
    simp only [impBranch_constructor, Diagram.implication,
      ForkDerivation.implication, productIso, Iso.trans_hom, Iso.symm_hom, asIso_inv,
      Functor.mapIso_hom, Functor.map_comp, Category.assoc]

/-- Proposition 10.2 for all algebras of the displayed endofunctor on numerical tuple diagrams. -/
def formulaAlgebra_isInitial : IsInitial formulaAlgebra := by
  have e : AlgebraTransport.mappedAlgebra equivalence polynomialComparison ForkSyntax.syntaxAlgebra =
      formulaAlgebra := by
    change Endofunctor.Algebra.mk sentences _ = Endofunctor.Algebra.mk sentences _
    exact congrArg (Endofunctor.Algebra.mk sentences) mapped_structure
  exact e ▸ AlgebraTransport.initial equivalence polynomialComparison
    ForkSyntax.syntaxAlgebra ForkSyntax.syntaxAlgebra_isInitial

theorem unique_fold (Z : Object) (a : polynomial.obj Z ⟶ Z) :
    ∃! u : sentences ⟶ Z, constructor ≫ u = polynomial.map u ≫ a := by
  let A : Endofunctor.Algebra polynomial := ⟨Z, a⟩
  let m := formulaAlgebra_isInitial.to A
  refine ⟨m.f, m.h.symm, fun u hu => ?_⟩
  exact congrArg Endofunctor.Algebra.Hom.f
    (formulaAlgebra_isInitial.hom_ext (⟨u, hu.symm⟩ : formulaAlgebra ⟶ A) m)

/-- An algebra morphism is equivalently a natural transformation respecting each
of the three constructors. -/
theorem fold_iff {Z : Object} (a : polynomial.obj Z ⟶ Z) (u : sentences ⟶ Z) :
    constructor ≫ u = polynomial.map u ≫ a ↔
      atom ≫ u = atomBranch Z ≫ a ∧
      negation ≫ u = u ≫ negBranch Z ≫ a ∧
      Diagram.implication ≫ u = prod.map u u ≫ impBranch Z ≫ a := by
  constructor
  · intro h
    exact ⟨by simpa only [atomBranch_constructor_assoc, atomBranch_map_assoc] using
        congrArg (fun m => atomBranch sentences ≫ m) h,
      by simpa only [negBranch_constructor_assoc, negBranch_map_assoc] using
        congrArg (fun m => negBranch sentences ≫ m) h,
      by simpa only [impBranch_constructor_assoc, impBranch_map_assoc] using
        congrArg (fun m => impBranch sentences ≫ m) h⟩
  · rintro ⟨h₁, h₂, h₃⟩
    exact arity_hom_ext (by simpa only [atomBranch_constructor_assoc, atomBranch_map_assoc] using h₁)
      (by simpa only [negBranch_constructor_assoc, negBranch_map_assoc] using h₂)
      (by simpa only [impBranch_constructor_assoc, impBranch_map_assoc] using h₃)

/-- Evaluate numerical formula trees with the three operations of the target algebra. -/
def evaluate (Z : Object) (a : polynomial.obj Z ⟶ Z) : sentences ⟶ Z :=
  ForkPropositionalFolds.fold Z (labelCoding.inv ≫ atomBranch Z ≫ a)
    (negBranch Z ≫ a) (impBranch Z ≫ a)

theorem evaluate_constructor (Z : Object) (a : polynomial.obj Z ⟶ Z) :
    constructor ≫ evaluate Z a = polynomial.map (evaluate Z a) ≫ a := by
  apply (fold_iff _ _).mpr
  refine ⟨?_, ForkPropositionalFolds.fold_negation _ _ _ _,
    ForkPropositionalFolds.fold_implication _ _ _ _⟩
  unfold atom evaluate
  rw [Category.assoc, ForkPropositionalFolds.fold_atom, Iso.hom_inv_id_assoc]

theorem eq_evaluate {Z : Object} (a : polynomial.obj Z ⟶ Z) (u : sentences ⟶ Z)
    (h : constructor ≫ u = polynomial.map u ≫ a) : u = evaluate Z a :=
  (unique_fold Z a).unique h (evaluate_constructor Z a)

end CategoricalEssentialIncompleteness.V46.ForkTupleFormulaAlgebra
