/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.EffectiveForkConstruction
public import CategoricalEssentialIncompleteness.EffectiveForkLimits
public import CategoricalEssentialIncompleteness.RestrictionSpanPullbacks

/-! # Comparison with the paper's partial-map category -/

@[expose] public section

noncomputable section
open CategoryTheory CategoryTheory.RestrictionCategory CategoryTheory.Limits

namespace CategoricalEssentialIncompleteness.LocalConnectedness.EffectiveFork

/-- Isomorphism classes of total spans with monic domain leg. -/
abbrev PartialMapCategory := PartialSpans.Par Object

/-- The effective partial functions used in the construction present
`Par(C_rec^J, Mono)`, with the usual pullback composition. -/
def partialMapEquivalence : PartialMapCategory ≌ Object := PartialSpans.equivalence

theorem span_composition {X Y Z : Object} (s : PartialSpans.Span X Y)
    (t : PartialSpans.Span Y Z) :
    (s.pullbackComp t).value=s.value ≫ t.value := s.value_pullbackComp t

theorem span_equality {X Y : Object} (s t : PartialSpans.Span X Y) :
    s.Isomorphic t ↔ s.value=t.value := s.isomorphic_iff_value_eq t

end CategoricalEssentialIncompleteness.LocalConnectedness.EffectiveFork
