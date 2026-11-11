/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerTotalEquivalence
public import CategoricalEssentialIncompleteness.V46MillerTotalRegular
public import CategoricalEssentialIncompleteness.V46MillerTotalExtensive
public import CategoricalEssentialIncompleteness.V46RegularEquivalence

/-! # Category-theoretic constituents of the printed total realization

These conclusions concern the actual Tot(Split(E_z)). Parameter-stable
syntax/list and derivation initiality are separate remaining obligations.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.RestrictionCategory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.LocalConnectedness
namespace CategoricalEssentialIncompleteness.V46.Miller.Total

instance canonicalFiniteLimits (z : Point) : HasFiniteLimits (CanonicalTotal z) where
  out _ _ _ := Adjunction.hasLimitsOfShape_of_equivalence (pointPresentation z).inverse

instance canonicalFiniteCoproducts (z : Point) : HasFiniteCoproducts (CanonicalTotal z) where
  out _ := Adjunction.hasColimitsOfShape_of_equivalence (pointPresentation z).inverse

instance canonicalRegular (z : Point) : Regular (CanonicalTotal z) :=
  RegularEquivalence.regular (pointPresentation z)

instance canonicalExtensive (z : Point) : FinitaryExtensive (CanonicalTotal z) :=
  finitaryExtensive_of_preserves_and_reflects_isomorphism (pointPresentation z).inverse

end CategoricalEssentialIncompleteness.V46.Miller.Total
