/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ForkTupleFormulaAlgebra

/-! # The three formula constructors and the universal property in Proposition 10.2 -/

@[expose] public section

noncomputable section
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46
open ForkDiagonalObstruction (tupleDiagram)
open ForkDerivation.Diagram (sentences realization)
open ForkTupleFormulaAlgebra

namespace CategoricalEssentialIncompleteness.V46.ForkTupleFormulaAlgebra.Checks

local notation "TupleDiagrams" => WalkingSpan ⥤ NumericalTuples.Object

example (X : TupleDiagrams) : polynomial.obj X = ((tupleDiagram ⨿ X) ⨿ (X ⨯ X)) := rfl

example {X Y : TupleDiagrams} (f : X ⟶ Y) : polynomial.map f =
    coprod.map (coprod.map (𝟙 tupleDiagram) f) (prod.map f f) := rfl

example (k z a b : ℕ) : ((labelCoding.hom.app .zero).toFun ⟨(k, z, a, b), Set.mem_univ _⟩).val =
    Nat.pair k (Nat.pair z (Nat.pair a b)) := labelCoding_center k z a b

example : (coprod.inl : tupleDiagram ⟶ tupleDiagram ⨿ sentences) ≫ coprod.inl ≫ formulaAlgebra.str =
    labelCoding.hom ≫ realization.map ForkDerivation.atom := by
  exact (Category.assoc _ _ _).symm.trans atomBranch_constructor

example : (coprod.inr : sentences ⟶ tupleDiagram ⨿ sentences) ≫ coprod.inl ≫ formulaAlgebra.str =
    realization.map ForkDerivation.negation := by
  exact (Category.assoc _ _ _).symm.trans negBranch_constructor

example : (coprod.inr : sentences ⨯ sentences ⟶ polynomial.obj sentences) ≫ formulaAlgebra.str =
    ForkDerivation.Diagram.implication := impBranch_constructor

example : IsInitial (formulaAlgebra : Endofunctor.Algebra polynomial) := formulaAlgebra_isInitial

example (Z : TupleDiagrams) (a : (tupleDiagram ⨿ Z) ⨿ (Z ⨯ Z) ⟶ Z) :
    ∃! u : sentences ⟶ Z, formulaAlgebra.str ≫ u =
      coprod.map (coprod.map (𝟙 tupleDiagram) u) (prod.map u u) ≫ a := unique_fold Z a

example {Z : TupleDiagrams} (a : polynomial.obj Z ⟶ Z) (u : sentences ⟶ Z)
    (h : formulaAlgebra.str ≫ u = polynomial.map u ≫ a) :
    u = ForkPropositionalFolds.fold Z (labelCoding.inv ≫ atomBranch Z ≫ a)
      (negBranch Z ≫ a) (impBranch Z ≫ a) := eq_evaluate a u h

example {Z : TupleDiagrams} (a : polynomial.obj Z ⟶ Z) {j k : WalkingSpan} (e : j ⟶ k) :
    sentences.map e ≫ (evaluate Z a).app k = (evaluate Z a).app j ≫ Z.map e :=
  (evaluate Z a).naturality e

end CategoricalEssentialIncompleteness.V46.ForkTupleFormulaAlgebra.Checks
