/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46LogicalSchemes
public import Mathlib.Tactic.FinCases

/-! # The seven parameter injections of a syntax algebra -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v u
open CategoryTheory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness.V46.SyntacticFiniteNamedSchemes
variable {C : Type u} [Category.{v} C] [Regular C] [FinitaryExtensive C]
variable {V : C} {σ π : ℕ → C} {d : ℕ} (S : CategoricalSyntax V σ π d)
/-- The original parameter object of each of the seven named schemes. -/
def schemeParameters : Fin 7 → C :=
  ![(S).algebra.a.2 ⨯ (S).algebra.a.2,
    ((S).algebra.a.2 ⨯ (S).algebra.a.2) ⨯ (S).algebra.a.2,
    (S).algebra.a.2 ⨯ (S).algebra.a.2,
    (S).instantiationParameters,(S).distributionParameters,
    (S).algebra.a.1,(S).equalitySchemeParameters]

def schemeMorphism : (i : Fin 7) → @Quiver.Hom C inferInstance
    (schemeParameters S i) (S).algebra.a.2 :=
  Fin.cases ((S).hilbertOne)
    (Fin.cases ((S).hilbertTwo)
    (Fin.cases ((S).hilbertThree)
    (Fin.cases ((S).hilbertInstantiation)
    (Fin.cases ((S).hilbertDistribution)
    (Fin.cases ((S).hilbertReflexivity)
    (Fin.cases ((S).hilbertEquality) ((fun k => k.elim0))))))))

def schemeInjection : (i : Fin 7) → @Quiver.Hom C inferInstance
    (schemeParameters S i) (S).logicalParameters :=
  Fin.cases (coprod.inl ≫ coprod.inl ≫ coprod.inl ≫ coprod.inl ≫ coprod.inl ≫ coprod.inl)
    (Fin.cases (coprod.inr ≫ coprod.inl ≫ coprod.inl ≫ coprod.inl ≫ coprod.inl ≫ coprod.inl)
    (Fin.cases (coprod.inr ≫ coprod.inl ≫ coprod.inl ≫ coprod.inl ≫ coprod.inl)
    (Fin.cases (coprod.inr ≫ coprod.inl ≫ coprod.inl ≫ coprod.inl)
    (Fin.cases (coprod.inr ≫ coprod.inl ≫ coprod.inl)
    (Fin.cases (coprod.inr ≫ coprod.inl)
    (Fin.cases (coprod.inr) ((fun k => k.elim0))))))))

theorem schemeInjection_formula (i : Fin 7) :
    schemeInjection S i ≫ (S).logicalAxioms = schemeMorphism S i := by
  fin_cases i
  · change (coprod.inl ≫ coprod.inl ≫ coprod.inl ≫ coprod.inl ≫ coprod.inl ≫ coprod.inl) ≫ (S).logicalAxioms = (S).hilbertOne
    dsimp only [CategoricalSyntax.logicalAxioms]
    simp only [Category.assoc]
    repeat' erw [coprod.inl_desc]
  · change (coprod.inr ≫ coprod.inl ≫ coprod.inl ≫ coprod.inl ≫ coprod.inl ≫ coprod.inl) ≫ (S).logicalAxioms = (S).hilbertTwo
    dsimp only [CategoricalSyntax.logicalAxioms]
    simp only [Category.assoc]
    repeat' first | erw [coprod.inl_desc] | erw [coprod.inr_desc]
  · change (coprod.inr ≫ coprod.inl ≫ coprod.inl ≫ coprod.inl ≫ coprod.inl) ≫ (S).logicalAxioms = (S).hilbertThree
    dsimp only [CategoricalSyntax.logicalAxioms]
    simp only [Category.assoc]
    repeat' first | erw [coprod.inl_desc] | erw [coprod.inr_desc]
  · change (coprod.inr ≫ coprod.inl ≫ coprod.inl ≫ coprod.inl) ≫ (S).logicalAxioms = (S).hilbertInstantiation
    dsimp only [CategoricalSyntax.logicalAxioms]
    simp only [Category.assoc]
    repeat' first | erw [coprod.inl_desc] | erw [coprod.inr_desc]
  · change (coprod.inr ≫ coprod.inl ≫ coprod.inl) ≫ (S).logicalAxioms = (S).hilbertDistribution
    dsimp only [CategoricalSyntax.logicalAxioms]
    simp only [Category.assoc]
    repeat' first | erw [coprod.inl_desc] | erw [coprod.inr_desc]
  · change (coprod.inr ≫ coprod.inl) ≫ (S).logicalAxioms = (S).hilbertReflexivity
    dsimp only [CategoricalSyntax.logicalAxioms]
    simp only [Category.assoc]
    repeat' first | erw [coprod.inl_desc] | erw [coprod.inr_desc]
  · change (coprod.inr) ≫ (S).logicalAxioms = (S).hilbertEquality
    dsimp only [CategoricalSyntax.logicalAxioms]
    repeat' first | erw [coprod.inl_desc] | erw [coprod.inr_desc]

end CategoricalEssentialIncompleteness.V46.SyntacticFiniteNamedSchemes
