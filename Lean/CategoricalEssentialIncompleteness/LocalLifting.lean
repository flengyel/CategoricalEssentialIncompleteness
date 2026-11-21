/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.RangeFunctor
public import PCats.Recursion

/-! # The source Turing diagonal and range-functor lifting -/

@[expose] public section

universe v₁ v₂ u₁ u₂

open CategoryTheory CategoryTheory.RestrictionCategory
open CategoryTheory.Limits (HasZeroMorphisms zero_comp comp_zero)
open CategoryTheory.CoprodStruct CategoryTheory.HasCoproducts

namespace CategoricalEssentialIncompleteness.LocalConnectedness

section ChosenSection

variable {C : Type u₂} [Category.{v₂} C] [RestrictionCategory C]
variable [HasZeroMorphisms C] [RestrictionZero C] [BinaryJoins C]
variable [CoprodStruct C] [CategoryTheory.HasCoproducts C] [RestrictionCoproducts C]
variable [Ranges C] [Splits C] [JoinInverse C] [LocallyConnected C] [WeakChoice C]

/-- The unique section of the local switch. -/
noncomputable def switchSection {X : C} (c c' : Idem X) (hc : Complementary c c') :
    X ⟶ coprod X X := Classical.choose (complementary_switch c c' hc)

theorem switchSection_spec {X : C} (c c' : Idem X) (hc : Complementary c c') :
    SectionOf (copair c'.hom c.hom) (switchSection c c' hc) ∧
      isTotal (switchSection c c' hc) ∧
      c.hom ≫ switchSection c c' hc = c.hom ≫ i1 X X ∧
      c'.hom ≫ switchSection c c' hc = c'.hom ≫ i0 X X :=
  Classical.choose_spec (complementary_switch c c' hc)

end ChosenSection

section Turing

variable {R : Type u₁} [Category.{v₁} R] [PCategoryStruct R] [PCategory R]

open PCategoryStruct PCategory

/-- Turing universality supplies a total parameter and a source diagonal
equation, without applying a functor to any product. -/
theorem turing_diagonal {U : R} (τ : nearProd U U ⟶ U)
    (hτ : RecursionCategory.IsTuringMorphism τ) {V : R}
    (b : U ≅ V) (ℓ : U ⟶ V) :
    ∃ g : U ⟶ U, isTotal g ∧ g ≫ diag U ≫ τ ≫ b.hom = g ≫ ℓ := by
  obtain ⟨g, hg, hparam⟩ := hτ U (p1 U U ≫ ℓ ≫ b.inv)
  refine ⟨g, hg, ?_⟩
  have hdiag : partialPairing (𝟙 U) g ≫ nearProd_map g (𝟙 U) = g ≫ diag U := by
    rw [partialPairing_comp_nearProd_map, Category.id_comp, Category.comp_id]
    simpa only [Category.comp_id, partialPairing_id_id] using
      (comp_partialPairing g (𝟙 U) (𝟙 U)).symm
  have he := congrArg (fun k => partialPairing (𝟙 U) g ≫ k ≫ b.hom) hparam
  simp only [← Category.assoc] at he
  rw [hdiag, p1_partialPairing, PCategory.rst_id, Category.id_comp] at he
  simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using he

end Turing

section Lifting

variable {R : Type u₁} {A : Type u₂} [Category.{v₁} R] [Category.{v₂} A]
variable [PCategoryStruct R] [PCategory R] [RestrictionCategory A]
variable [HasZeroMorphisms R] [RestrictionZero R] [BinaryJoins R]
variable [HasZeroMorphisms A] [RestrictionZero A] [BinaryJoins A]
variable [CoprodStruct R] [CategoryTheory.HasCoproducts R] [RestrictionCoproducts R]
variable [CoprodStruct A] [CategoryTheory.HasCoproducts A] [RestrictionCoproducts A]
variable [Ranges R] [Ranges A]
variable [Splits A] [JoinInverse A] [LocallyConnected A] [WeakChoice A]

/-- Only the sections belonging to complementary source pairs have to lift. The source
lifts are arbitrary partial morphisms. -/
def SectionLifting (F : RangeFunctor R A) (U : R) : Prop :=
  ∀ (c c' : Idem U) (hc : Complementary c c'), ∃ ℓ : U ⟶ coprod U U,
    F.toFunctor.map ℓ =
      switchSection (F.mapIdem c) (F.mapIdem c') (F.map_complementary hc) ≫
        (F.comparison U U).hom

open PCategoryStruct (nearProd diag)

/-- The first restriction idempotent of the diagonal pair. -/
def diagonal0 {U : R} (τ : nearProd U U ⟶ U) (b : U ≅ coprod U U) : Idem U :=
  Idem.pull (diag U ≫ τ ≫ b.hom) (summand0 U U)

/-- The second restriction idempotent of the diagonal pair. -/
def diagonal1 {U : R} (τ : nearProd U U ⟶ U) (b : U ≅ coprod U U) : Idem U :=
  Idem.pull (diag U ≫ τ ≫ b.hom) (summand1 U U)

/-- Binary restriction products and the chosen Turing morphism suffice for this
section-lifting theorem. -/
theorem local_lifting (F : RangeFunctor R A) {U : R}
    (τ : nearProd U U ⟶ U) (hτ : RecursionCategory.IsTuringMorphism τ)
    (b : U ≅ coprod U U) (hU : F.toFunctor.map (𝟙 U) ≠ 0)
    (lift : SectionLifting F U) : Inseparable (diagonal0 τ b) (diagonal1 τ b) := by
  constructor
  · rw [diagonal0, diagonal1, ← Idem.pull_inf, summands_disjoint, Idem.pull_bot]
  · rintro ⟨c, c', hc, ha0, ha1⟩
    obtain ⟨ℓ, hℓ⟩ := lift c c' hc
    obtain ⟨g, hg, hdiag⟩ := turing_diagonal τ hτ b ℓ
    let D := diag U ≫ τ ≫ b.hom
    let E := F.toFunctor.map g
    let H := F.toFunctor.map D ≫ (F.comparison U U).inv
    let s := switchSection (F.mapIdem c) (F.mapIdem c') (F.map_complementary hc)
    have hE : isTotal E := F.map_total g hg
    have hEH : E ≫ H = E ≫ s := by
      have hd : g ≫ D = g ≫ ℓ := hdiag
      have he := congrArg (fun k => F.toFunctor.map k ≫ (F.comparison U U).inv) hd
      simpa only [F.toFunctor.map_comp, hℓ, Category.assoc, Iso.hom_inv_id,
        Category.comp_id] using he
    have hspec := switchSection_spec (F.mapIdem c) (F.mapIdem c')
      (F.map_complementary hc)
    have hfib := switch_fibers (F.map_complementary hc) s hspec.2.1
      hspec.2.2.1 hspec.2.2.2
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
    have h0 : Idem.pull E (F.mapIdem (diagonal0 τ b)) = Idem.pull E (F.mapIdem c') := by
      rw [he0, ← Idem.pull_comp, hEH, Idem.pull_comp, hfib.1]
    have h1 : Idem.pull E (F.mapIdem (diagonal1 τ b)) = Idem.pull E (F.mapIdem c) := by
      rw [he1, ← Idem.pull_comp, hEH, Idem.pull_comp, hfib.2]
    have hle0 := Idem.pull_mono E (F.map_mono ha0)
    have hle1 := Idem.pull_mono E (F.map_mono ha1)
    rw [h0] at hle0
    rw [h1] at hle1
    have hequal := le_antisymm hle1 hle0
    have hcompl := (F.map_complementary hc).pull E hE
    have hzero : Idem.pull E (F.mapIdem c) = ⊥ := by
      simpa only [← hequal, inf_idem] using hcompl.disjoint
    have hone : (⊤ : Idem (F.toFunctor.obj U)) = ⊥ := by
      rw [← hcompl.cover, ← hequal, hzero, sup_idem]
    apply hU
    rw [F.toFunctor.map_id]
    exact congrArg Idem.hom hone

/-- The section-lifting theorem for a recursion category. -/
theorem range_functor_lifting
    [RecursionCategory.Prodominical R] [RecursionCategory.Isotype R]
    (F : RangeFunctor R A) {U : R}
    (τ : nearProd U U ⟶ U) (hτ : RecursionCategory.IsTuringMorphism τ)
    (b : U ≅ coprod U U) (hU : F.toFunctor.map (𝟙 U) ≠ 0)
    (lift : SectionLifting F U) : Inseparable (diagonal0 τ b) (diagonal1 τ b) :=
  local_lifting F τ hτ b hU lift

/-- Section lifting gives an inseparable pair. Preservation of total joins in the source
gives the domain-incompleteness conclusion. -/
theorem categorical_essential_incompleteness [TotalJoinInverse R]
    (F : RangeFunctor R A) {U : R}
    (τ : nearProd U U ⟶ U) (hτ : RecursionCategory.IsTuringMorphism τ)
    (b : U ≅ coprod U U) (hU : F.toFunctor.map (𝟙 U) ≠ 0)
    (lift : SectionLifting F U) {S : R}
    (θ : U ⟶ S) (hθ : isTotal θ) (ν : S ⟶ S) (hν : isTotal ν)
    (t₀ : Idem S) (ha : diagonal0 τ b ≤ Idem.pull θ t₀)
    (hb : diagonal1 τ b ≤ Idem.pull θ (Idem.pull ν t₀))
    (t : Idem S) (ht : t₀ ≤ t) (hconsistent : t ⊓ Idem.pull ν t = ⊥) :
    Inseparable t (Idem.pull ν t) ∧ t ⊔ Idem.pull ν t ≠ ⊤ :=
  domain_incompleteness (local_lifting F τ hτ b hU lift)
    θ hθ ν hν t₀ ha hb t ht hconsistent

end Lifting

end CategoricalEssentialIncompleteness.LocalConnectedness
