/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import PCats.Recursion
public import CategoricalEssentialIncompleteness.V46RestrictionTerminal
public import CategoricalEssentialIncompleteness.DisjointJoins

/-! # Provability of the restriction order

Cockett's provability predicate in §1 (Categories and Computability, Theorem 7.14) holds of two program points precisely when
their programs are ordered by restriction. Specializing a diagonal computation
to a constant program gives a predicate of the restriction terminal object.
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

variable {C : Type*} [Category* C] [PCategoryStruct C] [PCategory C]
variable {U : C} {Z : Tot C} (hZ : IsTerminal Z)
variable (τ : nearProd U U ⟶ U) (hτ : RecursionCategory.IsTuringMorphism τ)

/-- The program at a total point of the Turing object. -/
def program (k : Z.obj ⟶ U) : U ⟶ U :=
  partialPairing (terminate hZ U ≫ k) (𝟙 U) ≫ τ

include hτ in
theorem exists_code (f : U ⟶ U) :
    ∃ k : Z.obj ⟶ U, isTotal k ∧ program hZ τ k = f := by
  obtain ⟨k, hk, H⟩ := hτ Z.obj (p1 Z.obj U ≫ f)
  refine ⟨k, hk, ?_⟩
  have eqn := congrArg (fun v => partialPairing (terminate hZ U) (𝟙 U) ≫ v) H
  simpa only [program, ← Category.assoc, partialPairing_comp_nearProd_map, Category.id_comp,
    p1_partialPairing_of_isTotal (𝟙 U) (terminate_total hZ U)] using eqn

theorem terminate_point {k : Z.obj ⟶ U} (hk : isTotal k) :
    k ≫ terminate hZ U = 𝟙 Z.obj :=
  (terminate_unique hZ _ (RestrictionCategory.isTotal_comp hk (terminate_total hZ U))).trans
    (terminate_self hZ)

theorem apply_point {x : Z.obj ⟶ U} (hx : isTotal x) (k : Z.obj ⟶ U) :
    partialPairing k x ≫ τ = x ≫ program hZ τ k := by
  have h : x ≫ partialPairing (terminate hZ U ≫ k) (𝟙 U) = partialPairing k x := by
    rw [comp_partialPairing]
    simp only [← Category.assoc, terminate_point hZ hx, Category.id_comp, Category.comp_id]
  simpa only [program, Category.assoc] using congrArg (fun f => f ≫ τ) h.symm

theorem diagonal_point {k : Z.obj ⟶ U} (hk : isTotal k) :
    k ≫ (diag U ≫ τ) = k ≫ program hZ τ k := by
  have h : k ≫ partialPairing (terminate hZ U ≫ k) (𝟙 U) = k ≫ diag U := by
    rw [← partialPairing_id_id U, comp_partialPairing, comp_partialPairing]
    simp only [← Category.assoc, terminate_point hZ hk, Category.id_comp, Category.comp_id]
  simpa only [program, Category.assoc] using congrArg (fun f => f ≫ τ) h.symm

include hτ in
/-- One total specialization assigns to a point the code of its constant diagonal value. -/
theorem constant_diagonal_codes :
    ∃ g : U ⟶ U, isTotal g ∧ ∀ k : Z.obj ⟶ U,
      program hZ τ (k ≫ g) = terminate hZ U ≫ k ≫ diag U ≫ τ := by
  obtain ⟨g, hg, H⟩ := hτ U (p0 U U ≫ diag U ≫ τ)
  refine ⟨g, hg, fun k => ?_⟩
  have eqn := congrArg (fun v => partialPairing (terminate hZ U ≫ k) (𝟙 U) ≫ v) H
  simpa only [program, ← Category.assoc, partialPairing_comp_nearProd_map, Category.id_comp,
    p0_partialPairing_of_isTotal (terminate hZ U ≫ k) (RestrictionCategory.rst_id U)] using eqn

variable [HasZeroMorphisms C] [RestrictionZero C]

/-- A predicate recognizing the restriction order on every pair of total program points. -/
def RecognizesOrder (d : Idem (nearProd U U)) : Prop :=
  ∀ (k j : Z.obj ⟶ U), isTotal k → isTotal j →
    (Idem.pull (partialPairing k j) d = ⊤ ↔ ArrowLE (program hZ τ k) (program hZ τ j))

include hZ in
theorem terminal_nonzero (hne : ∃ X : C, 𝟙 X ≠ (0 : X ⟶ X)) :
    (𝟙 Z.obj : Z.obj ⟶ Z.obj) ≠ 0 := by
  obtain ⟨X, hx⟩ := hne
  intro hz
  have ha : terminate hZ X = 0 := by
    simpa only [Category.comp_id, comp_zero] using congrArg (fun f => terminate hZ X ≫ f) hz
  exact hx ((terminate_total hZ X).symm.trans ((congrArg RestrictionCategory.rst ha).trans (RestrictionZero.restrict_zero X Z.obj)))

include hτ in
theorem exists_nontrivial_terminal_predicate (hne : ∃ X : C, 𝟙 X ≠ (0 : X ⟶ X))
    (d : Idem (nearProd U U)) (hd : RecognizesOrder hZ τ d) :
    ∃ b : Idem Z.obj, b ≠ ⊥ ∧ b ≠ ⊤ := by
  obtain ⟨zeroCode, hzero, hz⟩ := exists_code hZ τ hτ (0 : U ⟶ U)
  obtain ⟨g, hg, hconst⟩ := constant_diagonal_codes hZ τ hτ
  let test := partialPairing g (terminate hZ U ≫ zeroCode)
  let D := Idem.pull test d
  obtain ⟨k, hk, hprog⟩ := exists_code hZ τ hτ D.hom
  let b := Idem.pull k D
  have hkt := terminate_point hZ hk
  have htest : k ≫ test = partialPairing (k ≫ g) zeroCode := by
    simp only [test, comp_partialPairing, ← Category.assoc, hkt, Category.id_comp]
  have heval : program hZ τ (k ≫ g) = terminate hZ U ≫ k ≫ D.hom := by
    rw [hconst k, diagonal_point hZ τ hk, hprog]
  have hjudge : b = ⊤ ↔ program hZ τ (k ≫ g) = 0 := by
    change Idem.pull k (Idem.pull test d) = ⊤ ↔ _
    rw [← Idem.pull_comp, htest, hd _ _ (RestrictionCategory.isTotal_comp hk hg) hzero, hz]
    simp only [ArrowLE, comp_zero, eq_comm]
  have hzeroed : program hZ τ (k ≫ g) = 0 ↔ b = ⊥ := by
    rw [heval]
    constructor
    · intro h
      have hval : k ≫ D.hom = 0 := by
        simpa only [← Category.assoc, hkt, Category.id_comp, comp_zero] using congrArg (fun f => k ≫ f) h
      apply Idem.ext
      change RestrictionCategory.rst (k ≫ D.hom) = 0
      rw [hval, RestrictionZero.restrict_zero]
    · intro h
      have hr := congrArg Idem.hom h
      change RestrictionCategory.rst (k ≫ D.hom) = 0 at hr
      have hv : k ≫ D.hom = 0 := by
        calc
          _ = RestrictionCategory.rst (k ≫ D.hom) ≫ (k ≫ D.hom) :=
            (RestrictionCategory.rst_comp_self _).symm
          _ = 0 := by rw [hr, zero_comp]
      rw [hv, comp_zero]
  have hdiff : (⊤ : Idem Z.obj) ≠ ⊥ := fun h => terminal_nonzero hZ hne (congrArg Idem.hom h)
  have H := hjudge.trans hzeroed
  exact ⟨b, fun h => hdiff ((H.mpr h).symm.trans h), fun h => hdiff (h.symm.trans (H.mp h))⟩

include hτ in
/-- A predicate on the Turing object may read the two indices through a pairing
morphism. Pulling it back along the pairing gives the binary order predicate. -/
theorem terminal_predicate_of_coded_order (hne : ∃ X : C, 𝟙 X ≠ (0 : X ⟶ X))
    (pair : nearProd U U ⟶ U) (d : Idem U)
    (hd : ∀ k j : Z.obj ⟶ U, isTotal k → isTotal j →
      (Idem.pull (partialPairing k j ≫ pair) d = ⊤ ↔
        ArrowLE (program hZ τ k) (program hZ τ j))) :
    ∃ b : Idem Z.obj, b ≠ ⊥ ∧ b ≠ ⊤ := by
  apply exists_nontrivial_terminal_predicate hZ τ hτ hne (Idem.pull pair d)
  intro k j hk hj
  simpa only [Idem.pull_comp] using hd k j hk hj

end CategoricalEssentialIncompleteness.V46.ProgramOrder
