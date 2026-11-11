/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46Comparison

/-! Explicit statement correspondence for the four Section 3 results. -/

@[expose] public section

universe v₁ v₂ u₁ u₂

open CategoryTheory CategoryTheory.RestrictionCategory
open CategoryTheory.Limits (HasZeroMorphisms)
open CategoryTheory.CoprodStruct CategoryTheory.HasCoproducts
open PCategoryStruct (nearProd diag)
open CategoricalEssentialIncompleteness.LocalConnectedness

section Comparison

variable {R : Type u₁} {A : Type u₂} [Category.{v₁} R] [Category.{v₂} A]
variable [PCategoryStruct R] [PCategory R] [RestrictionCategory A]
variable [HasZeroMorphisms R] [RestrictionZero R]
variable [HasZeroMorphisms A] [RestrictionZero A]
variable [CoprodStruct R] [CategoryTheory.HasCoproducts R] [RestrictionCoproducts R]
variable [CoprodStruct A] [CategoryTheory.HasCoproducts A] [RestrictionCoproducts A]
variable [Ranges R] [Ranges A]

example (F : RangeFunctor R A) {U : R}
    (τ : nearProd U U ⟶ U) (hτ : RecursionCategory.IsTuringMorphism τ)
    (b : U ≅ coprod U U) (P N : Idem (F.toFunctor.obj U))
    (hPN : P ⊓ N = ⊥)
    (ha0 : F.mapIdem (Idem.pull (diag U ≫ τ ≫ b.hom) ((⊤ : Idem U).sum ⊥)) ≤ P)
    (ha1 : F.mapIdem (Idem.pull (diag U ≫ τ ≫ b.hom) ((⊥ : Idem U).sum ⊤)) ≤ N)
    (s : F.toFunctor.obj U ⟶ coprod (F.toFunctor.obj U) (F.toFunctor.obj U))
    (hs0 : Idem.pull s ((⊤ : Idem (F.toFunctor.obj U)).sum ⊥) = N)
    (hs1 : Idem.pull s ((⊥ : Idem (F.toFunctor.obj U)).sum ⊤) = P)
    (ℓ : U ⟶ coprod U U)
    (hℓ : F.toFunctor.map ℓ = s ≫ (F.comparison U U).hom) :
    ∃ g : U ⟶ U, isTotal g ∧
      Idem.pull (F.toFunctor.map g) P = ⊥ ∧
      Idem.pull (F.toFunctor.map g) N = ⊥ :=
  comparison_zero_inverse_images F τ hτ b P N hPN ha0 ha1 s hs0 hs1 ℓ hℓ

example (F : RangeFunctor R A) {U : R}
    (g : U ⟶ U) (hg : isTotal g) (P N : Idem (F.toFunctor.obj U))
    (hP : Idem.pull (F.toFunctor.map g) P = ⊥)
    (hN : Idem.pull (F.toFunctor.map g) N = ⊥)
    (hU : F.toFunctor.map (𝟙 U) ≠ 0)
    (hjoin : Idem.pull (F.toFunctor.map g) (P ⊔ N) =
      Idem.pull (F.toFunctor.map g) P ⊔ Idem.pull (F.toFunctor.map g) N) :
    P ⊔ N ≠ ⊤ :=
  comparison_noncoverage F g hg P N hP hN hU hjoin

example [TotalJoinInverse A] (F : RangeFunctor R A) {U : R}
    (τ : nearProd U U ⟶ U) (hτ : RecursionCategory.IsTuringMorphism τ)
    (b : U ≅ coprod U U) (hU : F.toFunctor.map (𝟙 U) ≠ 0)
    (P N : Idem (F.toFunctor.obj U)) (hPN : Complementary P N)
    (ha0 : F.mapIdem (Idem.pull (diag U ≫ τ ≫ b.hom) ((⊤ : Idem U).sum ⊥)) ≤ P)
    (ha1 : F.mapIdem (Idem.pull (diag U ≫ τ ≫ b.hom) ((⊥ : Idem U).sum ⊤)) ≤ N) :
    ¬ ∃ (s : F.toFunctor.obj U ⟶ coprod (F.toFunctor.obj U) (F.toFunctor.obj U))
      (ℓ : U ⟶ coprod U U),
      Idem.pull s ((⊤ : Idem (F.toFunctor.obj U)).sum ⊥) = N ∧
      Idem.pull s ((⊥ : Idem (F.toFunctor.obj U)).sum ⊤) = P ∧
      F.toFunctor.map ℓ = s ≫ (F.comparison U U).hom :=
  no_lifted_complementary_separator F τ hτ b hU P N hPN ha0 ha1

example [TotalJoinInverse A] (F : RangeFunctor R A) {U : R}
    (τ : nearProd U U ⟶ U) (hτ : RecursionCategory.IsTuringMorphism τ)
    (b : U ≅ coprod U U) (hU : F.toFunctor.map (𝟙 U) ≠ 0)
    (conditionals : ∀ c c' : Idem U, Complementary c c' →
      ∃ ℓ : U ⟶ coprod U U, isTotal ℓ ∧
        c.hom ≫ ℓ = c.hom ≫ i1 U U ∧ c'.hom ≫ ℓ = c'.hom ≫ i0 U U) :
    Inseparable (Idem.pull (diag U ≫ τ ≫ b.hom) ((⊤ : Idem U).sum ⊥))
      (Idem.pull (diag U ≫ τ ≫ b.hom) ((⊥ : Idem U).sum ⊤)) :=
  source_inseparable_of_complementary_conditionals F τ hτ b hU conditionals

end Comparison

section DisjointJoins

variable {C : Type u₁} [Category.{v₁} C] [RestrictionCategory C]
variable [HasZeroMorphisms C] [RestrictionZero C]
variable [CoprodStruct C] [CategoryTheory.HasCoproducts C] [RestrictionCoproducts C]

example [DisjointArrowJoins C] {X : C} (c c' : Idem X) (hc : PairComplementary c c') :
    ∃ ℓ : X ⟶ coprod X X, isTotal ℓ ∧
      c.hom ≫ ℓ = c.hom ≫ i1 X X ∧ c'.hom ≫ ℓ = c'.hom ≫ i0 X X ∧
      ∀ h : X ⟶ coprod X X,
        ArrowLE (c.hom ≫ i1 X X) h → ArrowLE (c'.hom ≫ i0 X X) h → ArrowLE ℓ h :=
  complementary_conditional_of_disjoint_joins c c' hc

end DisjointJoins
