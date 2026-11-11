/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46CategoricalListLaws
public import CategoricalEssentialIncompleteness.ComplementedSubobjects

/-! # Uniqueness of the equality test on a variable object

The diagonal determines the Boolean equality test.
-/

@[expose] public section

noncomputable section

universe v u

open CategoryTheory CategoryTheory.Limits

namespace CategoricalEssentialIncompleteness.V46.DecidableVariables

variable {D : Type u} [Category.{v} D] [Regular D] [FinitaryExtensive D]
variable {V : D} (E F : DecidableVariables V)

theorem test_positive : boundFiber E.test (Two.point true) =
    Subobject.mk (prod.lift (𝟙 V) (𝟙 V)) := by
  rw [PresentationLemmas.boundFiber_eq_pullback]
  simp only [Two.point]
  exact Subobject.pullback_obj_mk E.diagonal.flip

theorem test_unique : E.test = F.test := by
  have hn : boundFiber E.test (Two.point false) = boundFiber F.test (Two.point false) := by
    have hE := Two.boundFibers_isCompl E.test
    have hF := Two.boundFibers_isCompl F.test
    rw [test_positive E] at hE
    rw [test_positive F] at hF
    exact hE.left_unique hF
  let p : SubobjectPartition (V ⨯ V) :=
    ⟨boundFiber E.test (Two.point true), boundFiber E.test (Two.point false),
      (Two.boundFibers_isCompl E.test).symm⟩
  have he := p.characteristic_unique_of_fibers E.test rfl rfl
  have hf := p.characteristic_unique_of_fibers F.test hn.symm
    ((test_positive F).trans (test_positive E).symm)
  exact he.trans hf.symm

theorem unique : E = F := by
  cases E with
  | mk e he =>
    cases F with
    | mk f hf =>
      have h : e = f := test_unique ⟨e, he⟩ ⟨f, hf⟩
      subst f
      rfl

end CategoricalEssentialIncompleteness.V46.DecidableVariables
