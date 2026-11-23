/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.ArithmeticObservationFunctor
public import CategoricalEssentialIncompleteness.V46ArithmeticDiagonalCodes
public import CategoricalEssentialIncompleteness.V46NamedArithmeticDiagonalBoundsStandard

/-! # The two numerical presentations of the observations in §8

The native observation functor applies the typed evaluator to a repeated
parameter. The formula translated to named syntax uses diagonal application
in the universal graph. The following equations expose the inputs of that
graph in each presentation.
-/

@[expose] public section
noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory FailureOfComposition.TypedTuringMorphism
open CategoricalEssentialIncompleteness.LocalConnectedness

namespace CategoricalEssentialIncompleteness.V46.ObservationCoding

variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

theorem native_output (j : ℕ) (x : M) :
    (ClassicalPrograms.outputPredicate j).val.Evalb ![x] ↔
      ∃ m : M, UniformTrace.graph.val.Evalb ![pi₁ x, pair (pi₂ x) x, 2 * m + (j : M)] := by
  let : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := models_of_subtheory (U := 𝗣𝗔) inferInstance
  let : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := models_of_subtheory (U := 𝗜𝚺₁) inferInstance
  have graph (y : M) : (FailureOfComposition.ConcreteEvaluator.eventualGraph tauIndex).val.Evalb
      ![pair x x, y] ↔ UniformTrace.graph.val.Evalb ![pi₁ x, pair (pi₂ x) x, y] := by
    simpa only [pi₁_pair, pi₂_pair] using eventualGraph_tauIndex_eval (pair x x) y
  rw [ClassicalPrograms.outputPredicate_eval]
  constructor
  · rintro ⟨_, m, hy, rfl⟩
    exact ⟨m, (graph _).mp hy⟩
  · rintro ⟨m, hm⟩
    exact ⟨_, m, (graph _).mpr hm, rfl⟩

theorem named_source_output (j : ℕ) (x : M) :
    (ArithmeticDiagonalCodes.outputPredicate j).val.Evalb ![x] ↔
      ∃ m : M, UniformTrace.graph.val.Evalb ![x,x,2 * m + (j : M)] := by
  rw [ArithmeticDiagonalCodes.outputPredicate_eval]
  exact exists_congr fun m => ArithmeticDiagonalCodes.diagonal_graph x (2 * m + (j : M))

/-- A theory inclusion acts by the identity on the observation parameter. -/
theorem inclusion_map {T T' : ArithmeticApplication.Theory} (f : T ⟶ T') :
    (ArithmeticApplication.observationFunctor.map f).map = 𝟙 ClassicalPrograms.U := rfl

/-- The named numeral instance is a closed postfix word for the translated formula. -/
theorem named_instance (n : ℕ) :
    NamedArithmeticUnarySubstitution.value ArithmeticDiagonalCodes.alpha.val n =
      NamedArithmeticSignature.formulaCode (NamedArithmeticDiagonalBounds.instanceFormula
        ArithmeticDiagonalCodes.alpha.val n) ∧
      (NamedArithmeticDiagonalBounds.instanceFormula
        ArithmeticDiagonalCodes.alpha.val n).freeVariables = [] :=
  NamedArithmeticDiagonalBounds.standard_instance_result _ n

end CategoricalEssentialIncompleteness.V46.ObservationCoding
