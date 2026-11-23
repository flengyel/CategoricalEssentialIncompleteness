/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ArithmeticDiagonalCodes

/-! # Bounded tests of the arithmetic diagonal computation

At each input and stage the total evaluator returns either an odd or an even number. An odd
return records an even diagonal output, since a successful stage adds one to its output.
-/

@[expose] public section

noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open FailureOfComposition FailureOfComposition.ConcreteEvaluator
open CategoricalRiceShapiro.Evaluator

namespace CategoricalEssentialIncompleteness.V46.ConnectedNumeralDomains

/-- Restrict the output of a stage graph to the numbers of the form `2m+j`. -/
def parityFormula (H : 𝚺₁.Semisentence 4) (d j : ℕ) : 𝚺₁.Semisentence 2 :=
  .mkSigma “n s. ∃ m, !H.val (2 * m + !!j) s !!d n”

private theorem parityFormula_eval {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (H : 𝚺₁.Semisentence 4) (d j : ℕ) (n s : M) : (parityFormula H d j).val.Evalb ![n, s] ↔
      ∃ m : M, H.val.Evalb ![2 * m + (j : M), s, (d : M), n] := by
  simp [parityFormula, numeral_eq_natCast_app]

/-- The parity of the stage evaluator at the fixed diagonal program of §8. -/
def stageParity (j : ℕ) : 𝚺₁.Semisentence 2 :=
  parityFormula evalnGraphFormula ArithmeticDiagonalCodes.diagonalIndex j

section Models
variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

private theorem stageParity_eval (j : ℕ) (n s : M) : (stageParity j).val.Evalb ![n, s] ↔
    ∃ m : M, 2 * m + (j : M) = UniformTrace.stageValue s ArithmeticDiagonalCodes.diagonalIndex n :=
  (parityFormula_eval evalnGraphFormula ArithmeticDiagonalCodes.diagonalIndex j n s).trans
    (exists_congr fun m => UniformTrace.stageFormula_eval (2 * m + (j : M)) s _ n)

theorem stageParity_complement (n s : M) : (stageParity 0).val.Evalb ![n, s] ↔
    ¬(stageParity 1).val.Evalb ![n, s] := by
  rw [stageParity_eval, stageParity_eval]
  simp only [Nat.cast_zero, Nat.cast_one, add_zero]
  let z := UniformTrace.stageValue s (ArithmeticDiagonalCodes.diagonalIndex : M) n
  constructor
  · rintro ⟨a, ha⟩ ⟨b, hb⟩
    have h := congrArg (fun w : M => w % 2) (ha.trans hb.symm)
    simp at h
  · intro h
    rcases Arithmetic.mod_two z with he | ho
    · exact ⟨z / 2, by simpa [he] using Arithmetic.div_add_mod z 2⟩
    · exact (h ⟨z / 2, by simpa [ho] using Arithmetic.div_add_mod z 2⟩).elim

private theorem stage_iff_certificate (n s : M) : (stageParity 1).val.Evalb ![n, s] ↔
    ∃ m : M, evalnCertificateFormula.val.Evalb
      ![s, (ArithmeticDiagonalCodes.diagonalIndex : M), n, 2 * m] := by
  rw [stageParity_eval]
  simp only [Nat.cast_one]
  apply exists_congr
  intro m
  exact ((evalnCertificateFormula_eval_history_iff _ _ _ _).trans
    (UniformTrace.stageFormula_eval _ _ _ _)).symm

/-- The even-output predicate holds exactly when one stage records an even output. -/
theorem alpha_iff_stage (n : M) : ArithmeticDiagonalCodes.alpha.val.Evalb ![n] ↔
    ∃ s : M, (stageParity 1).val.Evalb ![n, s] := by
  have hgraph (y : M) : UniformTrace.graph.val.Evalb
      ![(ArithmeticDiagonalCodes.diagonalIndex : M), n, y] ↔
        (eventualGraph ArithmeticDiagonalCodes.diagonalIndex).val.Evalb ![n, y] := by
    simpa only [numeral_eq_natCast_app] using
      canonicalPartrecGraphFormula_eval_iff_eventualGraph ArithmeticDiagonalCodes.diagonalIndex n y
  rw [ArithmeticDiagonalCodes.alpha_eval]
  simp only [hgraph, eventualGraph_eval, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, numeral_eq_natCast_app, stage_iff_certificate]
  exact exists_comm

/-- Every later stage retains the successful even output of the fixed program. -/
theorem stageParity_mono (n s t : M) (hst : s ≤ t) :
    (stageParity 1).val.Evalb ![n, s] → (stageParity 1).val.Evalb ![n, t] := by
  let : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := models_of_subtheory (U := 𝗣𝗔) inferInstance
  let : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := models_of_subtheory (U := 𝗜𝚺₁) inferInstance
  rintro h
  obtain ⟨m, hm⟩ := (stage_iff_certificate n s).mp h
  exact (stage_iff_certificate n t).mpr ⟨m,
    evalnCertificateFormula_natCode_persist ArithmeticDiagonalCodes.diagonalIndex s t n _ hst hm⟩

/-- A true standard stage is recognized at its numerals in every PA model. -/
theorem standard_stage (n t : ℕ) (h : (stageParity 1).val.Evalb (M := ℕ) ![n, t]) :
    (stageParity 1).val.Evalb ![(ORingStructure.numeral n : M), ORingStructure.numeral t] := by
  let : M↓[ℒₒᵣ] ⊧* 𝗥₀ := models_of_subtheory (U := 𝗣𝗔) inferInstance
  have hs := bold_sigma_one_completeness' (M := M) (stageParity 1).sigma_prop h
  have hv : (ORingStructure.numeral ∘ (![n, t] : Fin 2 → ℕ)) =
      ![(ORingStructure.numeral n : M), ORingStructure.numeral t] := by
    funext i
    fin_cases i <;> rfl
  exact hv ▸ hs

end Models
end CategoricalEssentialIncompleteness.V46.ConnectedNumeralDomains
