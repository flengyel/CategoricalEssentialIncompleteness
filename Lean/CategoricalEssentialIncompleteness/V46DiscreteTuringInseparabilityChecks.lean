/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46DiscreteTuringInseparability

/-! # The two results from Cockett's Categories and Computability in §1 -/

@[expose] public section
open CategoryTheory CategoryTheory.Limits CategoryTheory.PCategoryStruct
open CategoryTheory.RestrictionCategory
open CategoricalEssentialIncompleteness.LocalConnectedness
open CategoricalEssentialIncompleteness.V46 RestrictionSubobjects ProgramOrder

variable {C : Type*} [Category* C] [PCategoryStruct C] [PCategory C]
variable [HasZeroMorphisms C] [RestrictionZero C] {Z : Tot C} (hZ : IsTerminal Z)
variable {U : C} (τ : nearProd U U ⟶ U) (he : RecursionCategory.IsTuringMorphism τ)
variable (nontrivial : ∃ X : C, 𝟙 X ≠ (0 : X ⟶ X))

include hZ he nontrivial in
example (joins : CompatibleJoinsPreservedByPrecomposition C) (δ : nearProd U U ⟶ U)
    (hi : diag U ≫ δ = 𝟙 U) (hd : δ ≫ diag U = RestrictionCategory.rst δ) :
    ∃ a b : Idem U, a ⊓ b = ⊥ ∧
      ¬ ∃ c n : Idem U, PairComplementary c n ∧ a ≤ c ∧ b ≤ n :=
  exists_inseparable hZ τ he nontrivial joins δ hi hd

include hZ he nontrivial in
example [BinaryJoins C] (joins : CompatibleJoinsPreservedByPrecomposition C) (δ : nearProd U U ⟶ U)
    (hi : diag U ≫ δ = 𝟙 U) (hd : δ ≫ diag U = RestrictionCategory.rst δ) :
    ∃ a b : Idem U, Inseparable a b := inseparable_idempotents hZ τ he nontrivial joins δ hi hd

include he nontrivial in
example (pair : nearProd U U ⟶ U) (d : Idem U)
    (H : ∀ k j : Z.obj ⟶ U, isTotal k → isTotal j →
      (Idem.pull (partialPairing k j ≫ pair) d = ⊤ ↔
        ArrowLE (program hZ τ k) (program hZ τ j))) :
    ∃ b : Idem Z.obj, b ≠ ⊥ ∧ b ≠ ⊤ := terminal_predicate_of_coded_order hZ τ he nontrivial pair d H

#print axioms CategoricalEssentialIncompleteness.V46.ProgramOrder.disjoint_point_predicates
#print axioms CategoricalEssentialIncompleteness.V46.ProgramOrder.exists_inseparable
#print axioms CategoricalEssentialIncompleteness.V46.ProgramOrder.terminal_predicate_of_coded_order
