/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.PERCoproductDecomposition
public import CategoricalEssentialIncompleteness.PERCoproductSquares
public import CategoricalEssentialIncompleteness.PERRegular
public import Mathlib.CategoryTheory.Extensive

/-!
# Extensivity of the numerical PER category

Every morphism into a coproduct decomposes its source into the two inverse
images of the summands. For the coproduct of two terminal objects, the
injection squares are pullbacks. These properties give the van Kampen
property and hence finite extensivity. In particular, the coproduct injections
are disjoint. Together with regularity, this supplies the target-category
structure required in the numerical interpretation.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness
namespace NumericalPER

theorem two_isVanKampen :
    IsVanKampenColimit (BinaryCofan.mk (inl unitPER unitPER) (inr unitPER unitPER)) := by
  apply BinaryCofan.isVanKampen_mk _
    (fun R S ↦ BinaryCofan.mk (inl R S) (inr R S)) coproductIsColimit
    (fun f g ↦ pullback.cone f g) (fun f g ↦ pullback.isLimit f g)
  · intro R S α β f hl hr
    exact coproduct_to_units_squares α β f hl hr
  · intro R f
    exact chosenPullbackCoproductIsColimit f

instance perFinitaryExtensive : FinitaryExtensive NumericalPER :=
  (finitaryExtensive_iff_of_isTerminal NumericalPER unitPER unitIsTerminal _
    (coproductIsColimit unitPER unitPER)).mpr two_isVanKampen

/-- The pullback of the two coproduct injections is initial. -/
theorem coproduct_disjoint (R S : NumericalPER) :
    IsPullback (initial.to R) (initial.to S) (inl R S) (inr R S) :=
  FinitaryExtensive.isPullback_initial_to_binaryCofan (coproductIsColimit R S)

end NumericalPER
end CategoricalEssentialIncompleteness
