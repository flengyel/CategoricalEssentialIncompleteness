/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerTotalProducts


/-! # Restriction products of arbitrary uniformly semidecidable carriers -/

@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.RestrictionCategory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.LocalConnectedness
namespace CategoricalEssentialIncompleteness.V46.Miller.Total
variable {P : Uniform.Family}
example (X Y : Carrier P) : (product X Y).support = {n | (Nat.unpair n).1 ∈ X.support ∧ (Nat.unpair n).2 ∈ Y.support} := rfl
example {X Y : Carrier P} (f : ℕ → ℕ) (hf : Computable f) (h : ∀ x ∈ X.support,f x ∈ Y.support) :
    isTotal (totalFromFunction f hf h) := totalFromFunction_total f hf h
example {W X Y : Carrier P} (f : W ⟶ X) (g : W ⟶ Y) (n m : ℕ) :
    m ∈ val (partialPair f g) n ↔ (Nat.unpair m).1 ∈ val f n ∧ (Nat.unpair m).2 ∈ val g n :=
  mem_partialPair_iff f g n m
example {W X Y : Carrier P} (f : W ⟶ X) (g : W ⟶ Y) : rst (partialPair f g) = rst f ≫ rst g := rst_partialPair f g
end CategoricalEssentialIncompleteness.V46.Miller.Total
