/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerCategoryTuring


/-! # Statement checks in `V46MillerCategoryTuringChecks` -/

@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.RestrictionCategory
open CategoricalEssentialIncompleteness.LocalConnectedness
namespace CategoricalEssentialIncompleteness.V46.Miller.Uniform
attribute [instance 2000] nativeRestriction

example (z : Point) : RecursionCategory.PRecursionCategory (PointObject z) := inferInstance
example (z : Point) : Ranges (PointObject z) := inferInstance
example (z : Point) : RestrictionCoproducts (PointObject z) := inferInstance
example (z : Point) : DisjointArrowJoins (PointObject z) := inferInstance
example (z : Point) : JoinInverse (PointObject z) := inferInstance
example (z : Point) : LocallyConnected (PointObject z) := inferInstance
example (z : Point) : WeakChoice (PointObject z) := inferInstance
example (z : Point) (e n : ℕ) : (tau z).val (e,n) = Unanimity.tau z e n := tau_is_literal z e n
example (z : Point) (e n m : ℕ) :
    m ∈ (tau z).val (e,n) ↔ ∀ p ∈ representations z,m ∈ OracleProgram.numberedEval e p n :=
  tau_graph z e n m
example (z : Point) : RecursionCategory.IsTuringMorphism (tau z) := tau_isTuring z
example {P : Family} (e : ℕ) (X : Object P) : Computable (parameterIndex e X) :=
  parameterIndex_computable e X
example {P : Family} (e : ℕ) (X : Object P) (x : carrier P X) (p : Bits) (n : ℕ) :
    OracleProgram.numberedEval (parameterIndex e X x) p n =
      OracleProgram.numberedEval e p (Nat.pair (X.type.toNat x) n) := parameterIndex_eval e X x p n
example (z : Point) (Y : PointObject z)
    (f : product Y (N (Family.ofPoint z)) ⟶ N (Family.ofPoint z)) :
    ∃ r : Y ⟶ N (Family.ofPoint z),isTotal r ∧ productMap r (𝟙 (N (Family.ofPoint z))) ≫ tau z = f :=
  tau_parameterization z Y f
end CategoricalEssentialIncompleteness.V46.Miller.Uniform
