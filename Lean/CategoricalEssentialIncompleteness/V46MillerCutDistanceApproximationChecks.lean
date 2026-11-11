/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerCutDistanceApproximation


/-! # Statement checks in `V46MillerCutDistanceApproximationChecks` -/

@[expose] public section
noncomputable section
open CategoricalEssentialIncompleteness.V46.Miller

example (p : Bits) (N e m t r : ℕ)
    (hN : Cut.Distance.queryUse (Cut.Distance.dimension (Cut.Boxes.badBoxes e m t)) r≤N) :
    |Cut.Dyadic.value (Cut.Distance.approxCode (bitPrefix p N) e m t r)-
      Cut.Distance.delta e m t (rho p)|≤
      (Cut.Distance.dimension (Cut.Boxes.badBoxes e m t):ℝ)*((2:ℝ)^r)⁻¹ :=
  Cut.Distance.approxCode_error p N e m t r hN

example (p : Bits) (N e m t k : ℕ) (hN : Cut.Distance.use e m t k≤N) :
    |Cut.Dyadic.value (Cut.Distance.approxCode (bitPrefix p N) e m t
      (Cut.Distance.precision e m t k))-Cut.Distance.delta e m t (rho p)|≤((2:ℝ)^(k+2))⁻¹ :=
  Cut.Distance.approxCode_precision_error p N e m t k hN

example : Primrec (fun a:Word×((ℕ×ℕ)×(ℕ×ℕ)) =>
    Cut.Distance.approxCode a.1 a.2.1.1 a.2.1.2 a.2.2.1 a.2.2.2) := Cut.Distance.approxCode_primrec
example : Primrec (fun a:(ℕ×ℕ)×(ℕ×ℕ) => Cut.Distance.use a.1.1 a.1.2 a.2.1 a.2.2) :=
  Cut.Distance.use_primrec
example : Primrec₂ Cut.Distance.finiteIndex := Cut.Distance.finiteIndex_primrec
