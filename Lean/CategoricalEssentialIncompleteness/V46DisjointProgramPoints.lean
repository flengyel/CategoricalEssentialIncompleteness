/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ProgramOrder

/-! # Disjoint point predicates in a discrete Turing category

In Cockett's theorem on inseparable restriction idempotents, discreteness makes the
diagonal a partial isomorphism. The identity and zero programs give two total
points whose equality predicate has empty restriction.
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
variable (δ : nearProd U U ⟶ U)

private def pointPredicate (p : Z.obj ⟶ U) : Idem U :=
  Idem.pull (partialPairing (𝟙 U) (terminate hZ U ≫ p)) (Idem.ofRestrict δ)

private theorem pointPredicate_fixed {p : Z.obj ⟶ U} (hp : isTotal p)
    (hinv : diag U ≫ δ = 𝟙 U) : p ≫ (pointPredicate hZ δ p).hom = p := by
  let B := partialPairing (𝟙 U) (terminate hZ U ≫ p)
  have hb : p ≫ B = p ≫ diag U := by
    rw [← partialPairing_id_id U]
    simp only [B, comp_partialPairing, ← Category.assoc, terminate_point hZ hp, Category.id_comp, Category.comp_id]
  have hd : Idem.pull (diag U) (Idem.ofRestrict δ) = ⊤ := by
    apply Idem.ext
    change RestrictionCategory.rst (diag U ≫ RestrictionCategory.rst δ) = 𝟙 U
    rw [← RestrictionCategory.rst_comp_rst_right, hinv, RestrictionCategory.rst_id]
  have h : Idem.pull p (pointPredicate hZ δ p) = ⊤ := by
    change Idem.pull p (Idem.pull B (Idem.ofRestrict δ)) = ⊤
    rw [← Idem.pull_comp, hb, Idem.pull_comp, hd, Idem.pull_top_of_total p hp]
  rw [← Idem.pull_commute, h, Idem.top_hom, Category.id_comp]

private theorem pointPredicate_restriction {p : Z.obj ⟶ U} (hp : isTotal p)
    (hd : δ ≫ diag U = RestrictionCategory.rst δ) (c : Idem U)
    (hc : c ≤ pointPredicate hZ δ p) : c.hom = c.hom ≫ terminate hZ U ≫ p := by
  let B := partialPairing (𝟙 U) (terminate hZ U ≫ p)
  have he : c.hom ≫ B = (c.hom ≫ B ≫ δ) ≫ diag U := by
    have hh := congrArg (fun f => f ≫ B) (Idem.le_def.mp hc)
    change (c.hom ≫ (Idem.pull B (Idem.ofRestrict δ)).hom) ≫ B = c.hom ≫ B at hh
    rw [Category.assoc, Idem.pull_commute] at hh
    change c.hom ≫ B ≫ RestrictionCategory.rst δ = c.hom ≫ B at hh
    simpa only [Category.assoc,hd] using hh.symm
  have e₀ := congrArg (fun f => f ≫ p0 U U) he
  have e₁ := congrArg (fun f => f ≫ p1 U U) he
  have e : (c.hom ≫ B) ≫ p0 U U = (c.hom ≫ B) ≫ p1 U U := by
    simpa only [Category.assoc,diag_p0,diag_p1,Category.comp_id] using e₀.trans (by
      simpa only [Category.assoc,diag_p0,diag_p1,Category.comp_id] using e₁.symm)
  simpa only [Category.assoc,B,p0_partialPairing_of_isTotal (𝟙 U)
    (RestrictionCategory.isTotal_comp (terminate_total hZ U) hp),
    p1_partialPairing_of_isTotal _ (RestrictionCategory.rst_id U),Category.comp_id] using e

variable [HasZeroMorphisms C] [RestrictionZero C]

omit [RestrictionZero C] in
private theorem apart_codes {p q : Z.obj ⟶ U} (hp : isTotal p)
    (hi : program hZ τ p = 𝟙 U) (hz : program hZ τ q = 0)
    {X : C} (w : X ⟶ Z.obj) (h : w ≫ p = w ≫ q) : w = 0 := by
  have e : w ≫ p = 0 := by
    have eqn : w ≫ (partialPairing p p ≫ τ) = w ≫ (partialPairing q p ≫ τ) := by
      rw [← Category.assoc, ← Category.assoc, comp_partialPairing, comp_partialPairing, h]
    simpa only [apply_point hZ τ hp,hi,hz,Category.comp_id,comp_zero] using eqn
  calc w = (w ≫ p) ≫ terminate hZ U := by rw [Category.assoc,terminate_point hZ hp,Category.comp_id]
       _ = 0 := by rw [e,zero_comp]

include hτ hZ in
/-- The codes for identity and zero belong to disjoint restriction idempotents on the
Turing object. Discreteness is required only at this object. -/
theorem disjoint_point_predicates (hi : diag U ≫ δ = 𝟙 U)
    (hd : δ ≫ diag U = RestrictionCategory.rst δ) :
    ∃ (p q : Z.obj ⟶ U) (P N : Idem U), isTotal p ∧ isTotal q ∧ P ⊓ N = ⊥ ∧
      p ≫ P.hom = p ∧ q ≫ N.hom = q := by
  obtain ⟨p, hp, hid⟩ := exists_code hZ τ hτ (𝟙 U)
  obtain ⟨q, hq, hz⟩ := exists_code hZ τ hτ (0 : U ⟶ U)
  let P := pointPredicate hZ δ p
  let N := pointPredicate hZ δ q
  let c := P ⊓ N
  refine ⟨p,q,P,N,hp,hq,?_,pointPredicate_fixed hZ δ hp hi,pointPredicate_fixed hZ δ hq hi⟩
  have ep := pointPredicate_restriction hZ δ hp hd c (show c ≤ P from inf_le_left)
  have en := pointPredicate_restriction hZ δ hq hd c (show c ≤ N from inf_le_right)
  have hzero := apart_codes hZ τ hp hid hz (c.hom ≫ terminate hZ U) (by
    simpa only [Category.assoc] using ep.symm.trans en)
  apply Idem.ext
  change c.hom = 0
  rw [ep,← Category.assoc,hzero,zero_comp]

end CategoricalEssentialIncompleteness.V46.ProgramOrder
