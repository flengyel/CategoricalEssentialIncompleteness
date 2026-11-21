/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerCutApplications


/-! # Inseparability of the lower and upper Miller cuts -/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.RestrictionCategory
open CategoricalEssentialIncompleteness.LocalConnectedness
namespace CategoricalEssentialIncompleteness.V46.Miller.Cut.Checks
attribute [instance 2000] Uniform.nativeRestriction
example (a : Point) (ha : IsMiller a) :
    Inseparable (CutDigits.lowerIdem a) (CutDigits.upperIdem a) := printed_cut_inseparability a ha
example (a : Point) (ha : IsMiller a) :
    Inseparable (CutDigits.lowerIdem a) (CutDigits.upperIdem a) ∧
      ∀ p ∈ representations a,
        CutDigits.lowerCut a ⊆ CutDigits.separator p ∧
          Disjoint (CutDigits.separator p) (CutDigits.upperCut a) ∧
          Nat.RecursiveIn (OracleComputation.oracleSet (OracleRelative.oracleSupport p))
            (fun n => Part.some (CutDigits.decision p n)) := printed_cut_contrast a ha
example (a : Point) (ha : IsMiller a) (p : Bits) (hp : p ∈ representations a) :
    ¬RecursionCategory.IsTuringMorphism ((Uniform.J a p hp).toFunctor.map (Uniform.tau a)) :=
  mapped_tau_notTuring a ha p hp
example (p : Bits) : RangeFunctor (Uniform.RelativeObject p) (CutInseparability.SplitRelative p) :=
  CutInseparability.I p
end CategoricalEssentialIncompleteness.V46.Miller.Cut.Checks
