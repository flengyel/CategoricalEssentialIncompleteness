/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46CategoricalListLaws

/-! # Comparison of stable list algebras

Initiality compares the chosen list carriers and their operations.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u

open CategoryTheory CategoryTheory.Limits

namespace CategoricalEssentialIncompleteness.V46.StableListAlgebra.Comparison

variable {D : Type u} [Category.{v} D] [Regular D] [FinitaryExtensive D]
variable {V : D} (L M : StableListAlgebra V)

def map : L.algebra.carrier ⟶ M.algebra.carrier :=
  L.algebra.fold L.initial M.algebra

@[reassoc (attr := simp)] theorem nil : L.algebra.nil ≫ map L M = M.algebra.nil :=
  L.algebra.fold_nil L.initial M.algebra

@[reassoc] theorem cons : L.algebra.cons ≫ map L M =
    prod.map (𝟙 V) (map L M) ≫ M.algebra.cons :=
  L.algebra.fold_cons L.initial M.algebra

theorem identity : map L L = 𝟙 _ := by
  symm
  apply L.algebra.fold_unique L.initial L.algebra
  · simp
  · simp

theorem comp (N : StableListAlgebra V) : map L M ≫ map M N = map L N := by
  apply L.algebra.fold_unique L.initial N.algebra
  · simp only [← Category.assoc, nil]
  · rw [← Category.assoc, cons, Category.assoc, cons,
      ← Category.assoc, prod.map_map, Category.id_comp]

def iso : L.algebra.carrier ≅ M.algebra.carrier where
  hom := map L M
  inv := map M L
  hom_inv_id := (comp L M L).trans (identity L)
  inv_hom_id := (comp M L M).trans (identity M)

@[reassoc] theorem singleton : L.singleton ≫ map L M = M.singleton := by
  unfold StableListAlgebra.singleton
  rw [Category.assoc, cons, ← Category.assoc, prod.lift_map]
  simp only [Category.comp_id, Category.assoc, nil]

/-- Postcomposition commutes with a coproduct-fiber conditional. -/
theorem branch_postcomp {A B C : D} (b : A ⟶ Two D) (f g : A ⟶ B) (h : B ⟶ C) :
    Two.branch b f g ≫ h = Two.branch b (f ≫ h) (g ≫ h) := by
  apply Two.hom_ext b <;> simp [← Category.assoc, Two.fiberι_branch]

theorem appendParameterValue : L.appendParameterValue ≫ map L M =
    prod.map (map L M) (map L M) ≫ M.appendParameterValue := by
  let n := map L M
  let c : L.algebra.carrier ⨯ (V ⨯ M.algebra.carrier) ⟶ M.algebra.carrier :=
    prod.snd ≫ M.algebra.cons
  have h₁ : L.appendParameterValue ≫ map L M = L.parameterFold n c := by
    apply L.parameterFold_unique n c
    · simp [StableListAlgebra.parameterNil, n, ← Category.assoc]
    · rw [StableListAlgebra.parameterCons, ← Category.assoc,
        L.appendParameterValue_map_cons, Category.assoc, cons]
      have w : prod.map (𝟙 L.algebra.carrier)
          (prod.snd : V ⨯ L.algebra.carrier ⟶ L.algebra.carrier) =
          prod.lift prod.fst (prod.snd ≫ prod.snd) := by
        apply prod.hom_ext <;> simp
      simp only [StableListAlgebra.parameterRec, c, prod.lift_map_assoc,
        Category.comp_id, prod.lift_snd_assoc, Category.assoc, w]
  have h₂ : prod.map (map L M) (map L M) ≫ M.appendParameterValue =
      L.parameterFold n c := by
    apply L.parameterFold_unique n c
    · simp [StableListAlgebra.parameterNil, n, Category.assoc]
    · rw [StableListAlgebra.parameterCons, ← Category.assoc,
        prod.map_map, Category.id_comp, cons]
      have w : prod.map (map L M) (prod.map (𝟙 V) (map L M) ≫ M.algebra.cons) =
          prod.map (𝟙 L.algebra.carrier) (prod.map (𝟙 V) (map L M)) ≫
            prod.map (map L M) M.algebra.cons := by
        rw [prod.map_map, Category.id_comp]
      rw [w, Category.assoc, M.appendParameterValue_map_cons]
      simp [StableListAlgebra.parameterRec, c, prod.comp_lift_assoc,
        prod.map_snd_assoc, Category.assoc]
  exact h₁.trans h₂.symm

theorem append : L.append ≫ map L M =
    prod.map (map L M) (map L M) ≫ M.append := by
  unfold StableListAlgebra.append
  change ((prod.braiding _ _).hom ≫ L.appendParameterValue) ≫ map L M =
    prod.map (map L M) (map L M) ≫ ((prod.braiding _ _).hom ≫ M.appendParameterValue)
  rw [Category.assoc, appendParameterValue]
  have w : (prod.braiding L.algebra.carrier L.algebra.carrier).hom ≫
      prod.map (map L M) (map L M) =
      prod.map (map L M) (map L M) ≫
        (prod.braiding M.algebra.carrier M.algebra.carrier).hom := by
    apply prod.hom_ext <;> simp [prod.braiding_hom]
  exact Category.assoc _ _ _ |>.symm.trans (congrArg (fun k => k ≫ M.appendParameterValue) w)
    |>.trans (Category.assoc _ _ _)

theorem deletion (E : DecidableVariables V) : L.deletion E ≫ map L M =
    prod.map (𝟙 V) (map L M) ≫ M.deletion E := by
  let n := terminal.from V ≫ M.algebra.nil
  let c := M.deletionStep E
  have h₁ : L.deletion E ≫ map L M = L.parameterFold n c := by
    apply L.parameterFold_unique n c
    · simpa [StableListAlgebra.parameterNil, n, Category.assoc] using
        congrArg (fun k => k ≫ map L M) (L.deletion_nil E)
    · rw [StableListAlgebra.parameterCons, ← Category.assoc, L.deletion_cons E,
        branch_postcomp]
      simp [StableListAlgebra.parameterRec, c, StableListAlgebra.deletionStep,
        cons, branch_natural, prod.comp_lift_assoc, prod.lift_map_assoc,
        Category.assoc]
  have h₂ : prod.map (𝟙 V) (map L M) ≫ M.deletion E = L.parameterFold n c := by
    apply L.parameterFold_unique n c
    · simpa [StableListAlgebra.parameterNil, n, prod.lift_map, Category.assoc] using
        M.deletion_nil E
    · rw [StableListAlgebra.parameterCons, ← Category.assoc, prod.map_map,
        Category.id_comp, cons, prod.map_id_comp, Category.assoc, M.deletion_cons E]
      simp [StableListAlgebra.parameterRec, c, StableListAlgebra.deletionStep,
        branch_natural, prod.comp_lift_assoc, prod.lift_map_assoc,
        Category.assoc]
  exact h₁.trans h₂.symm

theorem membership (E : DecidableVariables V) :
    prod.map (𝟙 V) (map L M) ≫ M.membership E = L.membership E := by
  rw [L.membership_eq_parameterFold E]
  apply L.parameterFold_unique (Two.constant V false) (StableListAlgebra.membershipStep E)
  · simp [StableListAlgebra.parameterNil, Category.assoc]
  · rw [StableListAlgebra.parameterCons, ← Category.assoc, prod.map_map,
      Category.id_comp, cons, prod.map_id_comp, Category.assoc, M.membership_cons E]
    simp [StableListAlgebra.parameterRec, StableListAlgebra.membershipStep,
      Two.comp_binary, prod.comp_lift_assoc, prod.lift_map_assoc,
      Category.assoc]

end CategoricalEssentialIncompleteness.V46.StableListAlgebra.Comparison
