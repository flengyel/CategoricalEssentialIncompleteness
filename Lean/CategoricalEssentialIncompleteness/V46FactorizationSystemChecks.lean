/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SplitRangePullbacks
public import CategoricalEssentialIncompleteness.V46StableFactorization

/-! # Factorization systems in Appendix A.5 and A.7 -/

@[expose] public section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Endofunctor CategoryTheory.Limits
open CategoryTheory.RestrictionCategory CategoricalEssentialIncompleteness.LocalConnectedness
open CategoricalEssentialIncompleteness.LocalConnectedness.V46 (TotalCategory)

namespace CategoricalEssentialIncompleteness.V46.FactorizationSystemChecks

universe v u
variable {C : Type u} [Category.{v} C] {E M : MorphismProperty C}

theorem algebra_factorizations (S : OrthogonalFactorizationSystem E M) (F : C ⥤ C)
    (preserves : ∀ {X Y : C} (e : X ⟶ Y), E e → E (F.map e)) :
    (∀ {A B : Algebra F} (h : A ⟶ B) (d : MorphismProperty.MapFactorizationData E M h.f),
      ∃! s : F.obj d.Z ⟶ d.Z, F.map d.i ≫ s = A.str ≫ d.i ∧
        s ≫ d.p = F.map d.p ≫ B.str) ∧
      OrthogonalFactorizationSystem (E.inverseImage (Algebra.forget F))
        (M.inverseImage (Algebra.forget F)) := by
  have hF : E ≤ E.inverseImage F := by
    intro X Y e he
    exact preserves e he
  exact ⟨fun h d => S.existsUnique_middle_algebra F hF h d, S.algebra F hF⟩

theorem regular_epimorphisms_and_monomorphisms [HasFiniteLimits C]
    (S : OrthogonalFactorizationSystem E M) (stable : E.IsStableUnderBaseChange) :
    ((∀ {X Y : C} (f : X ⟶ Y), E f ↔ IsRegularEpi f) ∧
      (∀ {X Y : C} (f : X ⟶ Y), M f ↔ Mono f)) ↔
        ∀ {X Y : C} (f : X ⟶ Y), M f ↔ Mono f := by
  constructor
  · exact And.right
  · intro monos
    have hm : M = .monomorphisms C := by ext X Y f; exact monos f
    obtain ⟨he, _⟩ := (OrthogonalFactorizationSystem.regularEpi_mono_iff S stable).mpr hm
    exact ⟨fun f => by rw [he]; rfl, fun f => monos f⟩

theorem total_range_factorizations [RestrictionCategory C] [Splits C] (R : RangeOperation C) :
    OrthogonalFactorizationSystem (C := TotalCategory C)
      (fun (X Y : TotalCategory C) (f : X ⟶ Y) => (R.range f.hom).hom = 𝟙 Y.obj)
      (fun (X Y : TotalCategory C) (m : X ⟶ Y) => ∃ r : Y.obj ⟶ X.obj,
        m.hom ≫ r = 𝟙 X.obj ∧ r ≫ m.hom = rst r) ∧
    (∀ {X B Y : TotalCategory C} (f : X ⟶ Y) (m : B ⟶ Y),
      RangeOperation.restrictionMonics m → HasPullback f m) ∧
    (∀ {P X B Y : TotalCategory C} {j : P ⟶ X} {g : P ⟶ B} {f : X ⟶ Y} {m : B ⟶ Y},
      IsPullback j g f m → RangeOperation.restrictionMonics m →
        RangeOperation.restrictionMonics j ∧
          ((R.range f.hom).hom = 𝟙 Y.obj → (R.range g.hom).hom = 𝟙 B.obj)) :=
  R.stableFactorization

end CategoricalEssentialIncompleteness.V46.FactorizationSystemChecks

open CategoricalEssentialIncompleteness.V46

#print axioms OrthogonalFactorizationSystem.existsUnique_middle_algebra
#print axioms OrthogonalFactorizationSystem.algebra
#print axioms OrthogonalFactorizationSystem.regularEpi_mono_iff
#print axioms RangeOperation.factorizationSystem
#print axioms RangeOperation.stableFactorization
#print axioms FactorizationSystemChecks.algebra_factorizations
#print axioms FactorizationSystemChecks.regular_epimorphisms_and_monomorphisms
#print axioms FactorizationSystemChecks.total_range_factorizations
