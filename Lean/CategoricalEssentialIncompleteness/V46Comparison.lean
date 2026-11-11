/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.DisjointJoins

/-! # Diagonal comparison and complementary conditionals -/

@[expose] public section

universe v₁ v₂ u₁ u₂

open CategoryTheory CategoryTheory.RestrictionCategory
open CategoryTheory.Limits (HasZeroMorphisms zero_comp comp_zero)
open CategoryTheory.CoprodStruct CategoryTheory.HasCoproducts
open PCategoryStruct (nearProd diag)

namespace CategoricalEssentialIncompleteness.LocalConnectedness

section Comparison

variable {R : Type u₁} {A : Type u₂} [Category.{v₁} R] [Category.{v₂} A]
variable [PCategoryStruct R] [PCategory R] [RestrictionCategory A]
variable [HasZeroMorphisms R] [RestrictionZero R]
variable [HasZeroMorphisms A] [RestrictionZero A]
variable [CoprodStruct R] [CategoryTheory.HasCoproducts R] [RestrictionCoproducts R]
variable [CoprodStruct A] [CategoryTheory.HasCoproducts A] [RestrictionCoproducts A]
variable [Ranges R] [Ranges A]

/-- Theorem 3.1: a partial lifted conditional for an arbitrary disjoint
target pair supplies a total source witness with both inverse images zero. -/
theorem comparison_zero_inverse_images (F : RangeFunctor R A) {U : R}
    (τ : nearProd U U ⟶ U) (hτ : RecursionCategory.IsTuringMorphism τ)
    (b : U ≅ coprod U U) (P N : Idem (F.toFunctor.obj U))
    (hPN : P ⊓ N = ⊥) (ha0 : F.mapIdem (diagonal0 τ b) ≤ P)
    (ha1 : F.mapIdem (diagonal1 τ b) ≤ N)
    (s : F.toFunctor.obj U ⟶ coprod (F.toFunctor.obj U) (F.toFunctor.obj U))
    (hs0 : Idem.pull s (summand0 (F.toFunctor.obj U) (F.toFunctor.obj U)) = N)
    (hs1 : Idem.pull s (summand1 (F.toFunctor.obj U) (F.toFunctor.obj U)) = P)
    (ℓ : U ⟶ coprod U U)
    (hℓ : F.toFunctor.map ℓ = s ≫ (F.comparison U U).hom) :
    ∃ g : U ⟶ U, isTotal g ∧
      Idem.pull (F.toFunctor.map g) P = ⊥ ∧
      Idem.pull (F.toFunctor.map g) N = ⊥ := by
  obtain ⟨g, hg, hdiag⟩ := turing_diagonal τ hτ b ℓ
  let D := diag U ≫ τ ≫ b.hom
  let E := F.toFunctor.map g
  let H := F.toFunctor.map D ≫ (F.comparison U U).inv
  have hEH : E ≫ H = E ≫ s := by
    have hd : g ≫ D = g ≫ ℓ := hdiag
    have he := congrArg (fun k => F.toFunctor.map k ≫ (F.comparison U U).inv) hd
    simpa only [F.toFunctor.map_comp, hℓ, Category.assoc, Iso.hom_inv_id,
      Category.comp_id] using he
  have hsum0 : Idem.pull (F.comparison U U).inv
      (summand0 (F.toFunctor.obj U) (F.toFunctor.obj U)) =
      F.mapIdem (summand0 U U) := by
    simpa only [summand0, F.map_top, F.map_bot] using
      F.pull_comparison_inv_sum (⊤ : Idem U) (⊥ : Idem U)
  have hsum1 : Idem.pull (F.comparison U U).inv
      (summand1 (F.toFunctor.obj U) (F.toFunctor.obj U)) =
      F.mapIdem (summand1 U U) := by
    simpa only [summand1, F.map_top, F.map_bot] using
      F.pull_comparison_inv_sum (⊥ : Idem U) (⊤ : Idem U)
  have he0 : F.mapIdem (diagonal0 τ b) =
      Idem.pull H (summand0 (F.toFunctor.obj U) (F.toFunctor.obj U)) := by
    change F.mapIdem (Idem.pull D (summand0 U U)) = _
    rw [F.map_pull, show H = F.toFunctor.map D ≫ (F.comparison U U).inv from rfl,
      Idem.pull_comp, hsum0]
  have he1 : F.mapIdem (diagonal1 τ b) =
      Idem.pull H (summand1 (F.toFunctor.obj U) (F.toFunctor.obj U)) := by
    change F.mapIdem (Idem.pull D (summand1 U U)) = _
    rw [F.map_pull, show H = F.toFunctor.map D ≫ (F.comparison U U).inv from rfl,
      Idem.pull_comp, hsum1]
  have h0 : Idem.pull E (F.mapIdem (diagonal0 τ b)) = Idem.pull E N := by
    rw [he0, ← Idem.pull_comp, hEH, Idem.pull_comp, hs0]
  have h1 : Idem.pull E (F.mapIdem (diagonal1 τ b)) = Idem.pull E P := by
    rw [he1, ← Idem.pull_comp, hEH, Idem.pull_comp, hs1]
  have hle0 := Idem.pull_mono E ha0
  have hle1 := Idem.pull_mono E ha1
  rw [h0] at hle0
  rw [h1] at hle1
  have hequal := le_antisymm hle1 hle0
  have hzero : Idem.pull E P = ⊥ := by
    have hd := congrArg (Idem.pull E) hPN
    simpa only [Idem.pull_inf, Idem.pull_bot, ← hequal, inf_idem] using hd
  exact ⟨g, hg, hzero, hequal.symm.trans hzero⟩

omit [RestrictionZero R] [RestrictionCoproducts R] [RestrictionCoproducts A] in
/-- The noncoverage conclusion of Theorem 3.1, for the same witness.
Only preservation of this particular join is needed. -/
theorem comparison_noncoverage [BinaryJoins A] (F : RangeFunctor R A) {U : R}
    (g : U ⟶ U) (hg : isTotal g) (P N : Idem (F.toFunctor.obj U))
    (hP : Idem.pull (F.toFunctor.map g) P = ⊥)
    (hN : Idem.pull (F.toFunctor.map g) N = ⊥)
    (hU : F.toFunctor.map (𝟙 U) ≠ 0)
    (hjoin : Idem.pull (F.toFunctor.map g) (P ⊔ N) =
      Idem.pull (F.toFunctor.map g) P ⊔ Idem.pull (F.toFunctor.map g) N) :
    P ⊔ N ≠ ⊤ := by
  intro hcover
  have he : (⊤ : Idem (F.toFunctor.obj U)) = ⊥ := by
    rw [hcover, Idem.pull_top_of_total _ (F.map_total g hg), hP, hN, sup_idem] at hjoin
    exact hjoin
  apply hU
  rw [F.toFunctor.map_id]
  exact congrArg Idem.hom he

/-- Corollary 3.2: complementary target separators have no lifted
partial conditional with the reversed summand inverse images. -/
theorem no_lifted_complementary_separator [BinaryJoins A] [TotalJoinInverse A]
    (F : RangeFunctor R A) {U : R}
    (τ : nearProd U U ⟶ U) (hτ : RecursionCategory.IsTuringMorphism τ)
    (b : U ≅ coprod U U) (hU : F.toFunctor.map (𝟙 U) ≠ 0)
    (P N : Idem (F.toFunctor.obj U)) (hPN : Complementary P N)
    (ha0 : F.mapIdem (diagonal0 τ b) ≤ P)
    (ha1 : F.mapIdem (diagonal1 τ b) ≤ N) :
    ¬ ∃ (s : F.toFunctor.obj U ⟶ coprod (F.toFunctor.obj U) (F.toFunctor.obj U))
      (ℓ : U ⟶ coprod U U),
      Idem.pull s (summand0 (F.toFunctor.obj U) (F.toFunctor.obj U)) = N ∧
      Idem.pull s (summand1 (F.toFunctor.obj U) (F.toFunctor.obj U)) = P ∧
      F.toFunctor.map ℓ = s ≫ (F.comparison U U).hom := by
  rintro ⟨s, ℓ, hs0, hs1, hℓ⟩
  obtain ⟨g, hg, hP, hN⟩ :=
    comparison_zero_inverse_images F τ hτ b P N hPN.disjoint ha0 ha1 s hs0 hs1 ℓ hℓ
  exact comparison_noncoverage F g hg P N hP hN hU
    (TotalJoinInverse.pull_sup _ (F.map_total g hg) P N) hPN.cover

/-- Corollary 3.3: total source conditionals on complementary pairs
imply inseparability of the source Turing diagonal pair. -/
theorem source_inseparable_of_complementary_conditionals
    [BinaryJoins R] [BinaryJoins A] [TotalJoinInverse A]
    (F : RangeFunctor R A) {U : R}
    (τ : nearProd U U ⟶ U) (hτ : RecursionCategory.IsTuringMorphism τ)
    (b : U ≅ coprod U U) (hU : F.toFunctor.map (𝟙 U) ≠ 0)
    (conditionals : ∀ c c' : Idem U, Complementary c c' →
      ∃ ℓ : U ⟶ coprod U U, isTotal ℓ ∧
        c.hom ≫ ℓ = c.hom ≫ i1 U U ∧ c'.hom ≫ ℓ = c'.hom ≫ i0 U U) :
    Inseparable (diagonal0 τ b) (diagonal1 τ b) := by
  constructor
  · rw [diagonal0, diagonal1, ← Idem.pull_inf, summands_disjoint, Idem.pull_bot]
  · rintro ⟨c, c', hc, ha0, ha1⟩
    obtain ⟨ℓ, htotal, h1, h0⟩ := conditionals c c' hc
    have hfib := switch_fibers hc ℓ htotal h1 h0
    let s := F.toFunctor.map ℓ ≫ (F.comparison U U).inv
    have hs0 : Idem.pull s (summand0 (F.toFunctor.obj U) (F.toFunctor.obj U)) =
        F.mapIdem c' := by
      change Idem.pull (F.toFunctor.map ℓ ≫ (F.comparison U U).inv) _ = _
      rw [Idem.pull_comp]
      have hsum : Idem.pull (F.comparison U U).inv
          (summand0 (F.toFunctor.obj U) (F.toFunctor.obj U)) =
          F.mapIdem (summand0 U U) := by
        simpa only [summand0, F.map_top, F.map_bot] using
          F.pull_comparison_inv_sum (⊤ : Idem U) (⊥ : Idem U)
      rw [hsum, ← F.map_pull, hfib.1]
    have hs1 : Idem.pull s (summand1 (F.toFunctor.obj U) (F.toFunctor.obj U)) =
        F.mapIdem c := by
      change Idem.pull (F.toFunctor.map ℓ ≫ (F.comparison U U).inv) _ = _
      rw [Idem.pull_comp]
      have hsum : Idem.pull (F.comparison U U).inv
          (summand1 (F.toFunctor.obj U) (F.toFunctor.obj U)) =
          F.mapIdem (summand1 U U) := by
        simpa only [summand1, F.map_top, F.map_bot] using
          F.pull_comparison_inv_sum (⊥ : Idem U) (⊤ : Idem U)
      rw [hsum, ← F.map_pull, hfib.2]
    apply no_lifted_complementary_separator F τ hτ b hU
      (F.mapIdem c) (F.mapIdem c') (F.map_complementary hc)
      (F.map_mono ha0) (F.map_mono ha1)
    refine ⟨s, ℓ, hs0, hs1, ?_⟩
    simp only [s, Category.assoc, Iso.inv_hom_id, Category.comp_id]

end Comparison

section DisjointJoins

variable {C : Type u₁} [Category.{v₁} C] [RestrictionCategory C]
variable [HasZeroMorphisms C] [RestrictionZero C]
variable [CoprodStruct C] [CategoryTheory.HasCoproducts C] [RestrictionCoproducts C]

/-- Proposition 3.4: the disjoint join of the two conditional branches
is total and has the prescribed agreement equations. -/
theorem complementary_conditional_of_disjoint_joins [DisjointArrowJoins C]
    {X : C} (c c' : Idem X) (hc : PairComplementary c c') :
    ∃ ℓ : X ⟶ coprod X X, isTotal ℓ ∧
      c.hom ≫ ℓ = c.hom ≫ i1 X X ∧ c'.hom ≫ ℓ = c'.hom ≫ i0 X X ∧
      ∀ h : X ⟶ coprod X X,
        ArrowLE (c.hom ≫ i1 X X) h → ArrowLE (c'.hom ≫ i0 X X) h → ArrowLE ℓ h :=
  disjoint_joins_switch c c' hc

end DisjointJoins

end CategoricalEssentialIncompleteness.LocalConnectedness
