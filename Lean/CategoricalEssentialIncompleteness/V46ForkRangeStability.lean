/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46PartialMapEquivalence
public import CategoricalEssentialIncompleteness.V46PartialMapRanges
public import CategoricalEssentialIncompleteness.EffectiveForkConstruction
public import CategoricalEssentialIncompleteness.EffectiveForkRegular
public import CategoricalEssentialIncompleteness.EffectiveForkRangeProducts

/-! # Actual monic spans and total base change of effective fork ranges -/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.RestrictionCategory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.LocalConnectedness

namespace CategoricalEssentialIncompleteness.V46.ForkRangeStability

abbrev Total := EffectiveFork.Total
abbrev Object := EffectiveFork.Object
abbrev MonicSpanCategory := PartialMaps.Par Total

/-- Ordinary monic spans, quotiented by actual apex isomorphisms, present
all natural partial recursive fork maps. -/
def equivalence : MonicSpanCategory ≌ Object :=
  PartialMapEquivalence.equivalence (CategoryTheory.Equivalence.refl : Total ≌ Total)

theorem preserves_restrictions {X Y : MonicSpanCategory} (f : X ⟶ Y) :
    equivalence.functor.map (rst f) = rst (equivalence.functor.map f) :=
  PartialMapEquivalence.preserves_restrictions (CategoryTheory.Equivalence.refl : Total ≌ Total) f

theorem inverse_preserves_restrictions {X Y : Object} (f : X ⟶ Y) :
    equivalence.inverse.map (rst f) = rst (equivalence.inverse.map f) :=
  PartialMapEquivalence.inverse_preserves_restrictions
    (CategoryTheory.Equivalence.refl : Total ≌ Total) f

theorem preserves_ranges {X Y : MonicSpanCategory} (f : X ⟶ Y) :
    equivalence.functor.map (Ranges.range f).hom =
      (Ranges.range (equivalence.functor.map f)).hom :=
  PartialMapEquivalence.preserves_ranges (CategoryTheory.Equivalence.refl : Total ≌ Total) f

/-- A total morphism is represented by its identity-domain span. -/
theorem map_total {X Y : MonicSpanCategory} (f : X.obj ⟶ Y.obj) :
    equivalence.functor.map (PartialMaps.ofTotal f) = f.hom := by
  change PartialSpans.inverse (𝟙 X.obj) ≫ f.hom = f.hom
  have h := PartialSpans.hom_inverse (𝟙 X.obj)
  change (𝟙 X.obj.obj : X.obj.obj ⟶ X.obj.obj) ≫
    PartialSpans.inverse (𝟙 X.obj) = 𝟙 X.obj.obj at h
  rw [Category.id_comp] at h
  rw [h, Category.id_comp]

/-- The range of the partial arrow represented by a span is the range
of its total value leg, hence its componentwise regular image. -/
theorem span_range {X Y : Object} (s : PartialSpans.Span X Y) :
    Ranges.range s.value = Ranges.range s.map.hom :=
  Ranges.precomp_split_epi (PartialSpans.inverse s.mono) s.mono.hom
    (PartialSpans.hom_inverse s.mono) s.map.hom

/-- The ordinary monic-span range comparison is the regular image
of its actual total value leg. -/
theorem span_image {X Y : MonicSpanCategory} (s : PartialMaps.Raw X Y) :
    equivalence.functor.map (Ranges.range (PartialMaps.ofSpan s)).hom =
      (Ranges.range s.r.hom).hom := by
  rw [preserves_ranges]
  change (Ranges.range (PartialMapEquivalence.mapSpan
    (CategoryTheory.Equivalence.refl : Total ≌ Total) s).value).hom = _
  rw [span_range]
  rfl

/-- Pulling back the total value leg computes the inverse image of the
range of the represented partial arrow. The monic domain leg is arbitrary. -/
theorem span_pullback_range {X Y : Object} (s : PartialSpans.Span X Y)
    {P Z : Total} {p : P ⟶ s.apex} {q : P ⟶ Z} (g : Z ⟶ (⟨Y⟩ : Total))
    (h : IsPullback p q s.map g) :
    Ranges.range q.hom = Idem.pull g.hom (Ranges.range s.value) := by
  rw [span_range]
  exact EffectiveFork.pullback_image h

/-- A single span for an arbitrary partial fork map computes its range
under every total base change. -/
theorem partial_range_stable {X Y : Object} (f : X ⟶ Y) :
    ∃ s : PartialSpans.Span X Y, s.value = f ∧
      ∀ (Z : Total) (g : Z ⟶ (⟨Y⟩ : Total)),
        Ranges.range (pullback.snd s.map g).hom = Idem.pull g.hom (Ranges.range f) := by
  obtain ⟨s, hs⟩ := PartialSpans.Span.exists_value f
  refine ⟨s, hs, ?_⟩
  intro Z g
  rw [← hs]
  exact span_pullback_range s g (IsPullback.of_hasPullback s.map g)

end CategoricalEssentialIncompleteness.V46.ForkRangeStability
