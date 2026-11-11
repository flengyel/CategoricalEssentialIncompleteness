/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerCutDyadicBoxes


/-! # Statement checks in `V46MillerCutDyadicBoxesChecks` -/

@[expose] public section
noncomputable section
open CategoricalEssentialIncompleteness.V46.Miller

example (a : Bits) (k : ℕ) (x : ℝ)
    (hx : (numeral a k:ℝ)/(2:ℝ)^k≤x ∧ x≤((numeral a k:ℝ)+1)/(2:ℝ)^k) :
    ∃b:Bits,(∀j<k,b j=a j) ∧ Real.ofDigits b=x :=
  Cut.Boxes.binary_interval_surjective a k x hx

example (s : Word) :
    rho '' cylinder s=⋃b∈Cut.Boxes.rectangleWords s,Cut.Boxes.box s.length b :=
  Cut.Boxes.cylinder_image s

example (e m t : ℕ) :
    {z:Point | ∃c∈Cut.Boxes.badBoxes e m t,z∈Cut.Boxes.box c.1 c.2}=
      rho '' (Cut.haltingStage e m t)ᶜ := Cut.Boxes.badBoxes_spec e m t

example (N : ℕ) (b : Word) : IsClosed (Cut.Boxes.box N b) := Cut.Boxes.box_isClosed N b
example (N : ℕ) (b : Word) : (Cut.Boxes.box N b).Nonempty := Cut.Boxes.box_nonempty N b
example : Primrec (fun a:(ℕ×ℕ)×ℕ => Cut.Boxes.badBoxes a.1.1 a.1.2 a.2) :=
  Cut.Boxes.badBoxes_primrec
