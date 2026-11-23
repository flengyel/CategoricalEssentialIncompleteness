/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46DisjointProgramPoints

/-! # Inseparable predicates in a discrete Turing category

Theorem 7.8 of Cockett's *Categories and Computability*, attributed there to Lengyel,
is cited in §1. The inverse images of the two disjoint program-point predicates
under diagonal application have no complementary separator.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.RestrictionCategory
open CategoryTheory.PCategoryStruct CategoryTheory.PCategory
open CategoricalEssentialIncompleteness.LocalConnectedness

namespace CategoricalEssentialIncompleteness.V46.ProgramOrder
open RestrictionSubobjects RestrictionTerminal

/-- A binary join of compatible morphisms is preserved by precomposition when
each precomposition gives the least upper bound of the two restricted morphisms. -/
def CompatibleJoinsPreservedByPrecomposition (C : Type*) [Category* C] [RestrictionCategory C] : Prop :=
  ∀ {X Y : C} (f g : X ⟶ Y), RestrictionCategory.rst f ≫ g = RestrictionCategory.rst g ≫ f →
    ∃ j : X ⟶ Y, ∀ {W : C} (k : W ⟶ X),
      ArrowLE (k ≫ f) (k ≫ j) ∧ ArrowLE (k ≫ g) (k ≫ j) ∧
      ∀ h : W ⟶ Y, ArrowLE (k ≫ f) h → ArrowLE (k ≫ g) h → ArrowLE (k ≫ j) h

section Joins
variable {C : Type*} [Category* C] [RestrictionCategory C] [HasZeroMorphisms C] [RestrictionZero C]
variable (joins : CompatibleJoinsPreservedByPrecomposition C)

include joins in
private theorem joint_zero {X W : C} (a b : Idem X) (hc : PairComplementary a b) (k : W ⟶ X)
    (ha : k ≫ a.hom = 0) (hb : k ≫ b.hom = 0) : k = 0 := by
  obtain ⟨j, hj⟩ := joins a.hom b.hom (by rw [a.restriction,b.restriction,a.comm b])
  have h := hj (𝟙 X)
  simp only [Category.id_comp] at h
  have hr : RestrictionCategory.rst j = j := by
    have hjid := h.2.2 (𝟙 X) (show ArrowLE a.hom (𝟙 X) by simp only [ArrowLE,a.restriction,Category.comp_id])
      (show ArrowLE b.hom (𝟙 X) by simp only [ArrowLE,b.restriction,Category.comp_id])
    simpa only [ArrowLE,Category.comp_id] using hjid
  let d : Idem X := ⟨j,hr⟩
  have hd : d = ⊤ := top_le_iff.mp (hc.cover d
    (show a.hom ≫ j = a.hom by simpa only [ArrowLE,a.restriction] using h.1)
    (show b.hom ≫ j = b.hom by simpa only [ArrowLE,b.restriction] using h.2.1))
  have hj1 : j = 𝟙 X := congrArg Idem.hom hd
  have upper := (hj k).2.2 (0 : W ⟶ X)
  rw [ha,hb,hj1,Category.comp_id] at upper
  have h0 : ArrowLE (0 : W ⟶ X) 0 := by simp only [ArrowLE,comp_zero]
  simpa only [ArrowLE,comp_zero,eq_comm] using upper h0 h0

include joins in
private theorem branches {X Y : C} (a b : Idem X) (hd : a ⊓ b = ⊥)
    (f g : X ⟶ Y) (hf : isTotal f) (hg : isTotal g) :
    ∃ j : X ⟶ Y, a.hom ≫ j = a.hom ≫ f ∧ b.hom ≫ j = b.hom ≫ g := by
  have h₀ : RestrictionCategory.rst (a.hom ≫ f) = a.hom :=
    (RestrictionCategory.rst_comp_of_isTotal _ hf).trans a.restriction
  have h₁ : RestrictionCategory.rst (b.hom ≫ g) = b.hom :=
    (RestrictionCategory.rst_comp_of_isTotal _ hg).trans b.restriction
  have hab : a.hom ≫ b.hom = 0 := congrArg Idem.hom hd
  have hba := (b.comm a).trans hab
  obtain ⟨j,hj⟩ := joins (a.hom ≫ f) (b.hom ≫ g) (by
    rw [h₀,h₁,← Category.assoc,hab,zero_comp,← Category.assoc,hba,zero_comp])
  have h := hj (𝟙 X)
  simp only [Category.id_comp,ArrowLE,h₀,h₁] at h
  exact ⟨j,h.1,h.2.1⟩

end Joins

variable {C : Type*} [Category* C] [PCategoryStruct C] [PCategory C]
variable {U : C} {Z : Tot C} (hZ : IsTerminal Z)
variable (τ : nearProd U U ⟶ U) (hτ : RecursionCategory.IsTuringMorphism τ)
variable [HasZeroMorphisms C] [RestrictionZero C]

omit [HasZeroMorphisms C] [RestrictionZero C] in
private theorem below_fibre {X : C} (a : Idem X) (f p : X ⟶ U) (hp : isTotal p) (N : Idem U)
    (hn : p ≫ N.hom = p) (hf : a.hom ≫ f = a.hom ≫ p) : a ≤ Idem.pull f N := by
  change a.hom ≫ RestrictionCategory.rst (f ≫ N.hom) = a.hom
  calc
    _ = RestrictionCategory.rst (a.hom ≫ f ≫ N.hom) := by
      simpa only [a.restriction] using (RestrictionCategory.rst_comp_rst a.hom (f ≫ N.hom)).symm
    _ = RestrictionCategory.rst (a.hom ≫ p) := by rw [← Category.assoc,hf,Category.assoc,hn]
    _ = a.hom := (RestrictionCategory.rst_comp_of_isTotal _ hp).trans a.restriction

omit [HasZeroMorphisms C] [RestrictionZero C] in
private theorem switched_fibre (c : Idem U) {p k : Z.obj ⟶ U} (hp : isTotal p) (hk : isTotal k)
    (N : Idem U) (hn : p ≫ N.hom = p) (j : U ⟶ U) (hj : program hZ τ k = j)
    (hbranch : c.hom ≫ j = c.hom ≫ terminate hZ U ≫ p) :
    Idem.pull k c ≤ Idem.pull k (Idem.pull (diag U ≫ τ) N) := by
  rw [← Idem.pull_comp]
  apply below_fibre _ _ p hp N hn
  calc
    _ = (Idem.pull k c).hom ≫ k ≫ j := by rw [diagonal_point hZ τ hk,hj]
    _ = (k ≫ c.hom) ≫ j := by rw [← Idem.pull_commute,Category.assoc]
    _ = k ≫ c.hom ≫ terminate hZ U ≫ p := by rw [Category.assoc,hbranch]
    _ = (Idem.pull k c).hom ≫ p := by
      rw [← Category.assoc k c.hom,← Idem.pull_commute k c,Category.assoc,
        ← Category.assoc k (terminate hZ U),terminate_point hZ hk,Category.id_comp]

include hZ hτ in
/-- In a nontrivial discrete Turing category, finite compatible joins stable under
composition suffice for an inseparable pair. Only their precomposition law and
discreteness of the Turing object enter the proof. -/
theorem exists_inseparable (hne : ∃ X : C, 𝟙 X ≠ (0 : X ⟶ X))
    (joins : CompatibleJoinsPreservedByPrecomposition C) (δ : nearProd U U ⟶ U)
    (hi : diag U ≫ δ = 𝟙 U) (hd : δ ≫ diag U = RestrictionCategory.rst δ) :
    ∃ a b : Idem U, a ⊓ b = ⊥ ∧
      ¬ ∃ c n : Idem U, PairComplementary c n ∧ a ≤ c ∧ b ≤ n := by
  obtain ⟨p,q,P,N,hp,hq,hPN,hpP,hqN⟩ := disjoint_point_predicates hZ τ hτ δ hi hd
  let D := diag U ≫ τ
  refine ⟨Idem.pull D P,Idem.pull D N,by rw [← Idem.pull_inf,hPN,Idem.pull_bot],?_⟩
  rintro ⟨c,n,hcn,hc,hn⟩
  obtain ⟨j,hc',hn'⟩ := branches joins c n hcn.disjoint (terminate hZ U ≫ q) (terminate hZ U ≫ p)
    (RestrictionCategory.isTotal_comp (terminate_total hZ U) hq)
    (RestrictionCategory.isTotal_comp (terminate_total hZ U) hp)
  obtain ⟨k,hk,hj⟩ := exists_code hZ τ hτ j
  have ha : Idem.pull k c ≤ Idem.pull k n :=
    (switched_fibre hZ τ c hq hk N hqN j hj hc').trans (Idem.pull_mono k hn)
  have hb : Idem.pull k n ≤ Idem.pull k c :=
    (switched_fibre hZ τ n hp hk P hpP j hj hn').trans (Idem.pull_mono k hc)
  have hempty : Idem.pull k c ⊓ Idem.pull k n = ⊥ := by rw [← Idem.pull_inf,hcn.disjoint,Idem.pull_bot]
  have he : Idem.pull k c = ⊥ := (inf_eq_left.mpr ha).symm.trans hempty
  have he' : Idem.pull k n = ⊥ := (le_antisymm hb ha).trans he
  have hk0 := joint_zero joins c n hcn k
    (by rw [← Idem.pull_commute,he,Idem.bot_hom,zero_comp])
    (by rw [← Idem.pull_commute,he',Idem.bot_hom,zero_comp])
  exact terminal_nonzero hZ hne (hk.symm.trans
    ((congrArg RestrictionCategory.rst hk0).trans (RestrictionZero.restrict_zero Z.obj U)))

include hZ hτ in
theorem inseparable_idempotents [BinaryJoins C] (hne : ∃ X : C, 𝟙 X ≠ (0 : X ⟶ X))
    (joins : CompatibleJoinsPreservedByPrecomposition C) (δ : nearProd U U ⟶ U)
    (hi : diag U ≫ δ = 𝟙 U) (hd : δ ≫ diag U = RestrictionCategory.rst δ) :
    ∃ a b : Idem U, Inseparable a b := by
  obtain ⟨a,b,hab,hs⟩ := exists_inseparable hZ τ hτ hne joins δ hi hd
  refine ⟨a,b,hab,?_⟩
  rintro ⟨c,n,hcn,hc,hn⟩
  exact hs ⟨c,n,hcn.toPair,hc,hn⟩

end CategoricalEssentialIncompleteness.V46.ProgramOrder
