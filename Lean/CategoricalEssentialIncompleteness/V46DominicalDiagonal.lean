/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import PCats.DominicalRecursion
public import CategoricalEssentialIncompleteness.RestrictionCompatibility

/-!
# The two summand domains of a dominical Turing diagonal

In Di Paola and Heller's Theorem 8.15 the evaluator has codomain `X + X`.
A section of the copairing of two complementary domains is total and has
those domains as its two summand inverse images. Apply the fixed-source
Turing property to this section with the summands reversed. A separator
would force the identity of `X` to be zero.
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory CategoryTheory.DiPaolaHeller CategoryTheory.RestrictionCategory
open CategoryTheory.PCategoryStruct CategoryTheory.CoprodStruct CategoryTheory.HasCoproducts
open CategoryTheory.Limits CategoricalEssentialIncompleteness.LocalConnectedness

namespace CategoricalEssentialIncompleteness.V46.DominicalDiagonal

universe v u
variable {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]

/-- A section supplies the range through its restriction idempotent. -/
@[reducible] noncomputable def rangesOfChoice [HasChoice C] : Ranges C where
  range f := ⟨(exists_isRange_of_hasChoice f).choose,
    (exists_isRange_of_hasChoice f).choose_spec.isDomain⟩
  receives f := (exists_isRange_of_hasChoice f).choose_spec.receives
  agreement f := (exists_isRange_of_hasChoice f).choose_spec.uniq

variable [HasZeroMorphisms C]

theorem zeroRestriction (hd : Dominical C) : RestrictionZero C :=
  ⟨fun _ _ => (hd.eq_zero_iff_rst_eq_zero _).mp rfl⟩

variable [CoprodStruct C] [CategoryTheory.HasCoproducts C]

section Sections

variable [RestrictionZero C] [RestrictionCoproducts C] [Ranges C] [HasChoice C]

/-- The two summand inverse images of a section of a complementary copairing. -/
theorem complementary_section {X : C} (a b : Idem X) (cover : Complementary a b) :
    ∃ s : X ⟶ coprod X X, isTotal s ∧
      Idem.pull s (summand0 X X) = a ∧ Idem.pull s (summand1 X X) = b := by
  let p := copair a.hom b.hom
  obtain ⟨s, hs⟩ := HasChoice.exists_isSection p
  have sp : s ≫ p = 𝟙 X := by
    have h := Ranges.agreement p (s ≫ p) (𝟙 X) (by rw [hs.comp_self, Category.comp_id])
    simpa only [p, range_copair_idem, cover.cover, Idem.top_hom, Category.id_comp] using h
  have total : isTotal s := hs.comp_eq_rst.symm.trans sp
  have supported := ((section_iff_existing p s).mpr hs).support
  have restriction (e : Idem (coprod X X)) :
      RestrictionCategory.rst (s ≫ e.hom) = RestrictionCategory.rst ((s ≫ e.hom) ≫ p) := by
    rw [rst_comp_rst_right (s ≫ e.hom) p, Category.assoc,
      show e.hom ≫ RestrictionCategory.rst p = RestrictionCategory.rst p ≫ e.hom from
        e.comm (Idem.ofRestrict p), ← Category.assoc, supported]
  refine ⟨s, total, Idem.ext ?_, Idem.ext ?_⟩
  · rw [Idem.pull_hom, restriction, Category.assoc, ← switch_first a b cover.disjoint,
      ← Category.assoc, sp, Category.id_comp, a.restriction]
  · rw [Idem.pull_hom, restriction, Category.assoc, ← switch_second a b cover.disjoint,
      ← Category.assoc, sp, Category.id_comp, b.restriction]

end Sections

/-- A morphism with empty inverse images of two complementary domains is zero. -/
theorem zero_of_empty_preimages [RestrictionZero C] [Ranges C]
    {X Y : C} {a b : Idem Y} (cover : Complementary a b) (f : X ⟶ Y)
    (ha : Idem.pull f a = ⊥) (hb : Idem.pull f b = ⊥) : f = 0 := by
  have killed (e : Idem Y) (he : Idem.pull f e = ⊥) : e.hom ≫ (Ranges.range f).hom = 0 := by
    have fe : f ≫ e.hom = 0 := by
      rw [← Idem.pull_commute, he, Idem.bot_hom, zero_comp]
    have h := Ranges.agreement f e.hom 0 (by rw [fe, comp_zero])
    rw [comp_zero, (Ranges.range f).comm e] at h
    exact h
  have h := Ranges.agreement (copair a.hom b.hom) (Ranges.range f).hom 0 (by
    rw [copair_comp, killed a ha, killed b hb, comp_zero]
    apply CategoryTheory.HasCoproducts.hom_ext <;> simp only [i0_copair, i1_copair, comp_zero])
  rw [range_copair_idem, cover.cover, Idem.top_hom, Category.id_comp, Category.id_comp] at h
  rw [← Ranges.receives f, h, comp_zero]

omit [CoprodStruct C] [CategoryTheory.HasCoproducts C] in
open PCategory in
/-- On the diagonal the total index of the second projection followed by `s`
computes `s` at that index. Its parameter object is `X`. -/
theorem fixed_source_diagonal {X Y : C} (τ : nearProd X X ⟶ Y)
    (universal : DiPaolaHeller.IsTuringMorphism τ) (s : X ⟶ Y) :
    ∃ h : X ⟶ X, DiPaolaHeller.IsTotal h ∧ h ≫ diag X ≫ τ = h ≫ s := by
  obtain ⟨h, total, index⟩ := universal (p1 X X ≫ s)
  have diagonal : partialPairing (𝟙 X) h ≫ nearProd_map h (𝟙 X) = h ≫ diag X := by
    rw [partialPairing_comp_nearProd_map, Category.id_comp, Category.comp_id]
    simpa only [Category.comp_id, partialPairing_id_id] using
      (comp_partialPairing h (𝟙 X) (𝟙 X)).symm
  refine ⟨h, total, ?_⟩
  have equation := congrArg (fun k => partialPairing (𝟙 X) h ≫ k) index
  simpa only [← Category.assoc, diagonal, p1_partialPairing, PCategory.rst_id,
    Category.id_comp] using equation

/-- Theorem 8.15 with the nonzero identity used in its proof. Choice supplies
the ranges and the sections. The proof applies to any chosen binary coproducts. -/
theorem inseparable [HasChoice C] (hd : Dominical C) {X : C}
    (τ : nearProd X X ⟶ coprod X X) (universal : DiPaolaHeller.IsTuringMorphism τ)
    (nonzero : 𝟙 X ≠ (0 : X ⟶ X)) :
    letI : RestrictionZero C := zeroRestriction hd
    letI : Ranges C := rangesOfChoice
    Inseparable (Idem.pull (diag X ≫ τ) (summand0 X X))
      (Idem.pull (diag X ≫ τ) (summand1 X X)) := by
  let : RestrictionZero C := zeroRestriction hd
  let : Ranges C := rangesOfChoice
  change Inseparable (Idem.pull (diag X ≫ τ) (summand0 X X))
    (Idem.pull (diag X ≫ τ) (summand1 X X))
  constructor
  · rw [← Idem.pull_inf, summands_disjoint, Idem.pull_bot]
  · rintro ⟨a, b, cover, le_a, le_b⟩
    obtain ⟨s, _, left, right⟩ := complementary_section b a cover.symm
    obtain ⟨h, total, equation⟩ := fixed_source_diagonal τ universal s
    have first := Idem.pull_mono h le_a
    have second := Idem.pull_mono h le_b
    rw [← Idem.pull_comp, equation, Idem.pull_comp, left] at first
    rw [← Idem.pull_comp, equation, Idem.pull_comp, right] at second
    have equal := le_antisymm second first
    have empty : Idem.pull h a = ⊥ := by
      have disjoint := congrArg (Idem.pull h) cover.disjoint
      simpa only [Idem.pull_inf, Idem.pull_bot, ← equal, inf_idem] using disjoint
    have zero := zero_of_empty_preimages cover h empty (equal.symm.trans empty)
    exact nonzero (total (𝟙 X) (by rw [zero, comp_zero]))

end CategoricalEssentialIncompleteness.V46.DominicalDiagonal
