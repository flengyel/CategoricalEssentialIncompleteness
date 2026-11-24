/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46AlgebraFactorization
public import Mathlib.CategoryTheory.RegularCategory.Basic

/-!
# Stable factorizations and regular epimorphisms

Cockett, Guo and Hofstra, *Range categories II*, Proposition 3.17, is cited
in Appendix A. In a finitely complete category with stable factorizations,
if the right class consists of all monomorphisms, the left class consists of
the regular epimorphisms. To descend a morphism constant on a kernel pair,
factor its graph and show that the first projection of the image is invertible.
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits

namespace CategoricalEssentialIncompleteness.V46.OrthogonalFactorizationSystem

universe v u
variable {C : Type u} [Category.{v} C] [HasFiniteLimits C]
variable {E : MorphismProperty C} (S : OrthogonalFactorizationSystem E (.monomorphisms C))
include S

private theorem left_extremal {X Y : C} {e : X ⟶ Y} (he : E e) : ExtremalEpi e := by
  apply ExtremalEpi.mk_of_hasEqualizers
  intro Z a m fac hm
  obtain ⟨s, ⟨_, right⟩, _⟩ := S.diagonal he hm a (𝟙 Y) (by simpa using fac)
  exact ⟨s, by rw [← cancel_mono m, Category.assoc, right, Category.comp_id, Category.id_comp],
    right⟩

variable (stable : E.IsStableUnderBaseChange)
include stable

/-- Equality of two morphisms into the codomain of a cover can be tested after
pulling back that cover along each of them. -/
private theorem mono_of_cover {X I Y : C} {a : X ⟶ I} (ha : E a) (p : I ⟶ Y)
    (local_test : ∀ {Z : C} (u v : Z ⟶ X), (u ≫ a) ≫ p = (v ≫ a) ≫ p → u ≫ a = v ≫ a) :
    Mono p := by
  constructor
  intro W r s eq
  let r' := pullback.snd a r
  let s' := pullback.snd a (r' ≫ s)
  let u := s' ≫ pullback.fst a r
  let v := pullback.fst a (r' ≫ s)
  have hu : u ≫ a = (s' ≫ r') ≫ r := by
    simp only [u, r', Category.assoc, pullback.condition]
  have hv : v ≫ a = (s' ≫ r') ≫ s := by
    simpa only [v, s', Category.assoc] using pullback.condition (f := a) (g := r' ≫ s)
  have hr : E r' := stable.of_isPullback (IsPullback.of_hasPullback a r) ha
  have hs : E s' := stable.of_isPullback (IsPullback.of_hasPullback a (r' ≫ s)) ha
  have := (S.left_extremal hr).toEpi
  have := (S.left_extremal hs).toEpi
  apply (cancel_epi (s' ≫ r')).mp
  rw [← hu, ← hv]
  apply local_test
  simp only [hu, hv, Category.assoc, eq]

theorem regularEpi_of_left {X Y : C} {f : X ⟶ Y} (hf : E f) : IsRegularEpi f := by
  have extremal := S.left_extremal hf
  have := extremal.toEpi
  apply IsRegularEpi.of_epi_of_exists
  intro Z g compatible
  obtain ⟨d⟩ := S.factorizes.nonempty_mapFactorizationData (prod.lift f g)
  have : Mono d.p := d.hp
  let p := d.p ≫ prod.fst
  let q := d.p ≫ prod.snd
  have hp : d.i ≫ p = f := by simp [p, ← Category.assoc]
  have hq : d.i ≫ q = g := by simp [q, ← Category.assoc]
  have : Mono p := S.mono_of_cover stable d.hi p (by
    intro W u v equal
    have eqf : u ≫ f = v ≫ f := by simpa only [Category.assoc, hp] using equal
    have eqg : u ≫ g = v ≫ g := by
      have h := congrArg (fun k => pullback.lift u v eqf ≫ k) compatible
      simpa only [pullback.lift_fst_assoc, pullback.lift_snd_assoc] using h
    apply (cancel_mono d.p).mp
    apply prod.hom_ext
    · simpa only [Category.assoc] using equal
    · simpa only [Category.assoc, ← hq] using eqg)
  have := extremal.isIso d.i p hp
  refine ⟨inv p ≫ q, ?_⟩
  calc f ≫ inv p ≫ q = (d.i ≫ p) ≫ inv p ≫ q := congrArg (fun k => k ≫ inv p ≫ q) hp.symm
       _ = g := by rw [Category.assoc, IsIso.hom_inv_id_assoc, hq]

omit S stable in
/-- Proposition 3.17 identifies both morphism classes. -/
theorem regularEpi_mono_iff {M : MorphismProperty C}
    (system : OrthogonalFactorizationSystem E M) (stableLeft : E.IsStableUnderBaseChange) :
    E = .regularEpi C ∧ M = .monomorphisms C ↔ M = .monomorphisms C := by
  constructor
  · exact And.right
  · rintro rfl
    refine ⟨?_, rfl⟩
    ext X Y f
    constructor
    · exact system.regularEpi_of_left stableLeft
    · intro regular
      have : IsRegularEpi f := regular
      obtain ⟨d⟩ := system.factorizes.nonempty_mapFactorizationData f
      have : Mono d.p := d.hp
      have := ExtremalEpi.isIso f d.i d.p d.fac
      let : E.RespectsIso := system.left_respectsIso
      exact d.fac ▸ MorphismProperty.RespectsIso.postcomp E d.p d.i d.hi

end CategoricalEssentialIncompleteness.V46.OrthogonalFactorizationSystem
