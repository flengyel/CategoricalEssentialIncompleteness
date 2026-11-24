/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.RestrictionCompatibility

/-!
# Effective inseparability of two domains

Di Paola and Heller's Definition 8.17 tests a binary productive morphism
against indices for two disjoint domains extending the given pair. For the
application in Montagna, Remark 3.1, totality means restriction totality.
The domain reduction in Theorem 8.18 chooses a section of the copairing
of two domains and takes its two summand inverse images.
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory CategoryTheory.PCategoryStruct CategoryTheory.PCategory
open CategoryTheory.RestrictionCategory (isTotal)
open CategoryTheory.CoprodStruct CategoryTheory.HasCoproducts CategoryTheory.Limits
open CategoricalEssentialIncompleteness.LocalConnectedness

namespace CategoricalEssentialIncompleteness.V46.EffectiveInseparability

universe v u
variable {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
variable [HasZeroMorphisms C] [RestrictionZero C]

section Reduction

variable [CoprodStruct C] [CategoryTheory.HasCoproducts C] [Ranges C] [HasChoice C]
variable [JoinInverse C]

/-- A section divides the union of two domains into disjoint subdomains. -/
theorem reduction {X : C} (a b : Idem X) :
    ∃ c d : Idem X, c ≤ a ∧ d ≤ b ∧ c ⊓ d = ⊥ ∧ c ⊔ d = a ⊔ b := by
  let p := copair a.hom b.hom
  obtain ⟨s, sectionOf⟩ := HasChoice.exists_isSection p
  let c := Idem.pull s (summand0 X X)
  let d := Idem.pull s (summand1 X X)
  have le_branch (i : Idem (coprod X X)) (e : Idem X)
      (fixed : (i.hom ≫ p) ≫ e.hom = i.hom ≫ p) : Idem.pull s i ≤ e := by
    let j := Idem.pull s i
    have idji : j.hom ≫ rst s = j.hom := by
      change rst (s ≫ i.hom) ≫ rst s = rst (s ≫ i.hom)
      rw [rst_comm']
      exact RestrictionCategory.rst_comp_absorb s i.hom
    have image : j.hom = s ≫ i.hom ≫ p := by
      calc j.hom = j.hom ≫ s ≫ p := by rw [sectionOf.comp_eq_rst, idji]
           _ = s ≫ i.hom ≫ p := by rw [← Category.assoc, Idem.pull_commute, Category.assoc]
    change j.hom ≫ e.hom = j.hom
    rw [image, Category.assoc, fixed]
  refine ⟨c, d, le_branch _ a ?_, le_branch _ b ?_, ?_, ?_⟩
  · apply CategoryTheory.HasCoproducts.hom_ext <;>
      simp only [p, ← Category.assoc, i0_summand0, i1_summand0, i0_copair, a.idem, zero_comp]
  · apply CategoryTheory.HasCoproducts.hom_ext <;>
      simp only [p, ← Category.assoc, i0_summand1, i1_summand1, i1_copair, b.idem, zero_comp]
  · exact (Idem.pull_inf s _ _).symm.trans (by rw [summands_disjoint, Idem.pull_bot])
  · change Idem.pull s (summand0 X X) ⊔ Idem.pull s (summand1 X X) = _
    rw [← JoinInverse.pull_sup, (summands_complementary X X).cover, Idem.pull_top,
      ((section_iff_existing p s).mpr sectionOf).domain, range_copair_idem]

end Reduction

/-- Di Paola and Heller's Definition 4.4, allowing the parameter morphism to
have any source. Evaluation represents the domain at every argument. -/
def Index {U W : C} (τ : nearProd U U ⟶ U) (e : Idem U) (h : W ⟶ U) : Prop :=
  isTotal h ∧ nearProd_map h (𝟙 U) ≫ τ = p1 W U ≫ e.hom

omit [HasZeroMorphisms C] [RestrictionZero C] in
private theorem indexed_domain {U W : C} (τ : nearProd U U ⟶ U) (l : U ⟶ U)
    (e : Idem U) (h j : W ⟶ U) (index : Index τ e h) (coord : j ≫ l = h) :
    Idem.pull j (Idem.ofRestrict (partialPairing l (𝟙 U) ≫ τ)) = Idem.pull j e := by
  have eval := congrArg (fun k => partialPairing (𝟙 W) j ≫ k) index.2
  simp only [← Category.assoc, partialPairing_comp_nearProd_map, Category.id_comp,
    Category.comp_id, p1_partialPairing_of_isTotal j (PCategory.rst_id W)] at eval
  apply Idem.ext
  change rst (j ≫ rst (partialPairing l (𝟙 U) ≫ τ)) = rst (j ≫ e.hom)
  rw [← rst_comp_rst_right', ← Category.assoc, comp_partialPairing, coord, Category.comp_id, eval]

variable [CoprodStruct C] [CategoryTheory.HasCoproducts C] [Ranges C] [HasChoice C]
variable [JoinInverse C]

/-- Swapping the two evaluation tests gives a single total productive
morphism on pairs of indices. The same morphism works at every source. -/
theorem exists_productive_pair {U : C} (τ : nearProd U U ⟶ U) (pair : nearProd U U ≅ U) :
    ∃ (c d : Idem U) (m : nearProd U U ⟶ U), c ⊓ d = ⊥ ∧ isTotal m ∧
      ∀ {W : C} (e f : Idem U) (h k : W ⟶ U), Index τ e h → Index τ f k →
        c ≤ e → d ≤ f → e ⊓ f = ⊥ →
        (partialPairing h k ≫ m) ≫ e.hom = 0 ∧ (partialPairing h k ≫ m) ≫ f.hom = 0 := by
  let left := pair.inv ≫ p0 U U
  let right := pair.inv ≫ p1 U U
  let a := Idem.ofRestrict (partialPairing right (𝟙 U) ≫ τ)
  let b := Idem.ofRestrict (partialPairing left (𝟙 U) ≫ τ)
  obtain ⟨c, d, ca, db, disjoint, cover⟩ := reduction a b
  refine ⟨c, d, pair.hom, disjoint, iso_total pair, ?_⟩
  intro W e f h k ih ik ce df ef
  let j := partialPairing h k ≫ pair.hom
  have jl : j ≫ left = h := by
    simp only [j, left, Category.assoc, Iso.hom_inv_id_assoc, p0_partialPairing_of_isTotal h ik.1]
  have jr : j ≫ right = k := by
    simp only [j, right, Category.assoc, Iso.hom_inv_id_assoc, p1_partialPairing_of_isTotal k ih.1]
  have ja : Idem.pull j a = Idem.pull j f := indexed_domain τ right f k j ik jr
  have jb : Idem.pull j b = Idem.pull j e := indexed_domain τ left e h j ih jl
  have sep : Idem.pull j e ⊓ Idem.pull j f = ⊥ := by rw [← Idem.pull_inf, ef, Idem.pull_bot]
  have jc : Idem.pull j c = ⊥ := by
    apply le_antisymm _ bot_le
    rw [← sep]
    exact le_inf (Idem.pull_mono j ce) ((Idem.pull_mono j ca).trans_eq ja)
  have jd : Idem.pull j d = ⊥ := by
    apply le_antisymm _ bot_le
    rw [← sep]
    exact le_inf ((Idem.pull_mono j db).trans_eq jb) (Idem.pull_mono j df)
  have both := congrArg (Idem.pull j) cover
  simp only [JoinInverse.pull_sup, jc, jd, ja, jb, sup_idem] at both
  have vanish (q : Idem U) (hq : Idem.pull j q ≤ Idem.pull j f ⊔ Idem.pull j e) :
      j ≫ q.hom = 0 := by
    have he := le_antisymm (hq.trans_eq both.symm) bot_le
    rw [← Idem.pull_commute, he, Idem.bot_hom, zero_comp]
  exact ⟨vanish e le_sup_right, vanish f le_sup_left⟩

end CategoricalEssentialIncompleteness.V46.EffectiveInseparability
