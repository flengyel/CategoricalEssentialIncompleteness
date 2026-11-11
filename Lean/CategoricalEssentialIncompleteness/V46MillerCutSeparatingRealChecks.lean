/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerCutSeparatingReal


/-! # Statement checks in `V46MillerCutSeparatingRealChecks` -/

@[expose] public section
noncomputable section
open CategoricalEssentialIncompleteness.V46.Miller

example (e:ℕ) (z:Point) :
    1/4≤Cut.separatingReal e z ∧ Cut.separatingReal e z≤3/4 := Cut.separatingReal_bounds e z
example (e:ℕ) : Continuous (Cut.separatingReal e) := Cut.separatingReal_continuous e
example (e:ℕ) (z:Point) :
    Cut.separatingReal e z<1/2 ↔ ∃m:ℕ,m%2=0 ∧ m∈Unanimity.tau z e e :=
  Cut.separatingReal_lt_half e z
example (e:ℕ) (z:Point) :
    1/2<Cut.separatingReal e z ↔ ∃m:ℕ,m%2=1 ∧ m∈Unanimity.tau z e e :=
  Cut.separatingReal_gt_half e z
example (e:ℕ) (i:Fin 2) (z:Point) :
    (∃j:ℕ,0<Cut.Distance.delta e (2*(Nat.unpair j).1+i.val) (Nat.unpair j).2 z) ↔
      ∃m:ℕ,m%2=i.val ∧ m∈Unanimity.tau z e e := Cut.deltaTerm_pos_iff e i z
