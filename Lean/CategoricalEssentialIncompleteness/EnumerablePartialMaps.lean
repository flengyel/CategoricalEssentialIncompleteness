/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.EnumerableLocalConnectedness
public import CategoricalEssentialIncompleteness.EnumerableLimits
public import CategoricalEssentialIncompleteness.RestrictionSpanPullbacks

/-! # Monic spans present partial recursive numerical maps -/

@[expose] public section

noncomputable section
open CategoryTheory CategoryTheory.RestrictionCategory

namespace CategoricalEssentialIncompleteness.LocalConnectedness.EnumerableCarriers

abbrev PartialMapCategory := PartialSpans.Par Carrier

def partialMapEquivalence : PartialMapCategory ≌ Carrier := PartialSpans.equivalence

theorem span_composition {X Y Z : Carrier} (s : PartialSpans.Span X Y)
    (t : PartialSpans.Span Y Z) : (s.pullbackComp t).value=s.value ≫ t.value :=
  s.value_pullbackComp t

theorem span_equality {X Y : Carrier} (s t : PartialSpans.Span X Y) :
    s.Isomorphic t ↔ s.value=t.value := s.isomorphic_iff_value_eq t

end CategoricalEssentialIncompleteness.LocalConnectedness.EnumerableCarriers
