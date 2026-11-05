/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46SyntacticSyntaxSorts
import CategoricalEssentialIncompleteness.V46SyntacticSyntaxEvaluation
import CategoricalEssentialIncompleteness.V46SyntacticSyntaxParser

/-! # A value computation has exactly the parser's structural sort skeleton -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open FailureOfComposition.CodedObjectMembership

namespace CategoricalEssentialIncompleteness.V46.SyntacticSyntax.Coding

def statusSortGraph : 𝚺₁.Semisentence 2 :=
  let S := sortsGraph
  .mkSigma “o status. (status = 0 ∧ o = 0) ∨
    (∃ stack out, status = stack + 1 ∧ !S.val out stack ∧ o = out + 1)”

section Models
variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
local instance simulationDecidableEq : DecidableEq M := Classical.decEq M

noncomputable def statusSort (status : M) : M :=
  if status = 0 then 0 else sorts (status - 1) + 1

@[simp] theorem statusSort_zero : statusSort (0 : M) = 0 := by simp [statusSort]
@[simp] theorem statusSort_succ (stack : M) : statusSort (stack + 1) = sorts stack + 1 := by
  simp [statusSort]
@[simp] theorem statusSort_eq_zero (status : M) : statusSort status = 0 ↔ status = 0 := by
  rcases zero_or_succ status with rfl | ⟨stack, rfl⟩ <;> simp

@[simp] theorem statusSortGraph_eval (o status : M) :
    statusSortGraph.val.Evalb ![o, status] ↔ o = statusSort status := by
  rcases zero_or_succ status with rfl | ⟨stack, rfl⟩ <;> simp [statusSortGraph]

instance statusSort_defined : 𝚺₁-Function₁ (statusSort : M → M) via statusSortGraph := .mk fun v => by
  have hv : ![v 0, v 1] = v := (Matrix.fun_eq_vec_two v).symm
  simpa only [hv, Fin.succ_zero_eq_one] using statusSortGraph_eval (v 0) (v 1)
instance statusSort_definable : 𝚺₁-Function₁ (statusSort : M → M) := statusSort_defined.to_definable
instance statusSort_definable' (Γ m) : Γ-[m + 1]-Function₁ (statusSort : M → M) :=
  statusSort_definable.of_sigmaOne

end Models
end CategoricalEssentialIncompleteness.V46.SyntacticSyntax.Coding

namespace CategoricalEssentialIncompleteness.V46.SyntacticSyntax.SliceAlgebra
open Coding Postfix
variable {T : ArithmeticTheory} {P X Y : SyntacticPredicates.Carrier} {a b : RawPolynomial}
variable (A : SliceAlgebra T P X Y a b)
section Models
variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

/-- Both machines use the same numerical underflow and sort tests. The
only extra action of the value machine is the given positive operation
graph; its output payload cannot alter the structural skeleton. -/
theorem stepOutcome_sorts (formula : Bool) (p s parserStack valueStack new : M)
    (hs : sorts parserStack = sorts valueStack)
    (h : A.StepOutcome formula p s valueStack new) :
    statusSort (step a b ⟪s, if formula then 1 else 0⟫ (parserStack + 1)) = statusSort new := by
  have he := refill_sorts (if formula then b else a) s parserStack valueStack hs
  rcases h with ⟨hf, rfl⟩ | ⟨u, rest, value, hf, _, rfl⟩
  · rcases nil_or_adjoin (refill (if formula then b else a) s parserStack) with hp | ⟨v, tail, hp⟩
    · cases formula <;> simp_all [step]
    · simp [hp, hf] at he
  · rcases nil_or_adjoin (refill (if formula then b else a) s parserStack) with hp | ⟨v, tail, hp⟩
    · simp [hp, hf] at he
    · have ht : sorts tail = sorts rest := by simpa [hp, hf] using he
      cases formula <;> simp_all [step]

/-- Every actual value-step trace simulates the total numerical parser
on structural sorts, including the absorbing error case. -/
theorem valueStep_sorts (p record parsed old new : M)
    (hs : statusSort parsed = statusSort old)
    (h : A.valueStepGraph.val.Evalb ![p, record, old, new]) :
    statusSort (step a b record parsed) = statusSort new := by
  obtain ⟨_, _, _, hcase⟩ := (A.valueStepGraph_eval p record old new).mp h
  rcases hcase with ⟨rfl, rfl⟩ | ⟨s, stack, rfl, rfl, ho⟩ | ⟨s, stack, rfl, rfl, ho⟩
  · have hp : parsed = 0 := (statusSort_eq_zero parsed).mp (by simpa using hs)
    simp [hp]
  · rcases zero_or_succ parsed with rfl | ⟨parserStack, rfl⟩
    · simp at hs
    · have ht : sorts parserStack = sorts stack := by simpa using hs
      exact A.stepOutcome_sorts false p s parserStack stack new ht ho
  · rcases zero_or_succ parsed with rfl | ⟨parserStack, rfl⟩
    · simp at hs
    · have ht : sorts parserStack = sorts stack := by simpa using hs
      exact A.stepOutcome_sorts true p s parserStack stack new ht ho

/-- Pi-one induction compares the complete displayed finite record to
the actual primitive-recursion parser at every runPrefix position. -/
theorem valueRecord_sorts {p word n states : M} (h : A.ValueRecord p word n states) :
    statusSort (runPrefix a b word n 1) = statusSort (nth states n) := by
  have hh : ∀ i ≤ n, statusSort (runPrefix a b word i 1) = statusSort (nth states i) := by
    intro i hi
    induction i using ISigma1.pi1_succ_induction
    · definability
    case zero => simp [h.2.2.1]
    case succ i ih =>
      have hil : i < n := Arithmetic.succ_le_iff_lt.mp hi
      have hp := ih (le_trans (by simp) hi)
      simpa only [prefix_succ] using A.valueStep_sorts p (nth word i)
        (runPrefix a b word i 1) (nth states i) (nth states (i + 1)) hp (h.2.2.2 i hil)
  exact hh n (by rfl)

/-- A singleton parser stack forces the value status to be a singleton
of that same sort, rather than an error or an unrelated value stack. -/
theorem valueRecord_singleton {p word states : M} (formula : Bool)
    (h : A.ValueRecord p word (len word) states)
    (hw : (carrier formula a b).val.Evalb ![word]) :
    ∃ value : M, nth states (len word) = adjoin ⟪value, if formula then 1 else 0⟫ 0 + 1 := by
  have he := A.valueRecord_sorts h
  have hp := ((carrier_eval formula a b word).mp hw).2
  change statusSort (run a b word 1) = statusSort (nth states (len word)) at he
  rw [hp] at he
  rcases zero_or_succ (nth states (len word)) with hz | ⟨stack, hstack⟩
  · simp [hz] at he
  · have hs : adjoin (if formula then 1 else 0) 0 = sorts stack := by
      simpa [hstack] using he
    rcases nil_or_adjoin stack with hz | ⟨block, tail, ht⟩
    · simp [hz] at hs
    · have hb : (if formula then 1 else 0) = π₂ block ∧ (0 : M) = sorts tail := by
        exact (adjoin_inj _ _ _ _).mp (by simpa [ht] using hs)
      have htail : tail = 0 := (sorts_eq_zero tail).mp hb.2.symm
      refine ⟨π₁ block, ?_⟩
      simpa [ht, htail, hb.1, pair_unpair] using hstack

end Models
end CategoricalEssentialIncompleteness.V46.SyntacticSyntax.SliceAlgebra
