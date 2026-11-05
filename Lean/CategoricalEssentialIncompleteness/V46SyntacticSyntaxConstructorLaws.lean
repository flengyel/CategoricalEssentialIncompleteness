/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46SyntacticSyntaxChildrenTrace
import CategoricalEssentialIncompleteness.V46SyntacticSyntaxRootEquations
import CategoricalEssentialIncompleteness.V46SyntacticSyntaxParserLaws

/-! # Actual constructor equations of finite-record evaluation -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open FailureOfComposition.CodedObjectMembership
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates

namespace CategoricalEssentialIncompleteness.V46.SyntacticSyntax.SliceAlgebra
open Coding Postfix
variable {T : ArithmeticTheory} {P X Y : Carrier} {a b : RawPolynomial}
variable (A : SliceAlgebra T P X Y a b)
section Models
variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] [M↓[ℒₒᵣ] ⊧* T]

/-- The final root record uses the unchanged coefficient labels from
mapRaw, consumes exactly its ordered value children, and stores the
actual supplied root-operation output. -/
theorem root_valueStep (formula : Bool) (p u v value : M)
    (hm : (mapRaw P (A.evaluationFormula false) (A.evaluationFormula true)
      (if formula then b else a)).val.Evalb ![p, u, v])
    (hop : (if formula then A.formulaOp else A.termOp).val.Evalb ![p, v, value]) :
    A.valueStepGraph.val.Evalb
      ![p, ⟪shape (if formula then b else a) u, if formula then 1 else 0⟫,
        childStack (if formula then b else a) v 0 + 1,
        adjoin ⟪value, if formula then 1 else 0⟫ 0 + 1] := by
  obtain ⟨hp, hsource, hfiber⟩ := A.mapRaw_evaluation_fiber (if formula then b else a) p u v hm
  have hs := mapRaw_shape P (A.evaluationFormula false) (A.evaluationFormula true)
    (if formula then b else a) p u v hm
  have hr := refill_shape (if formula then b else a) v 0
    (rawFiber_carrier P X Y A.termProjection.graph A.formulaProjection.graph _ p v hfiber)
  rw [← hs] at hr
  have hstack := A.fiber_childStack (if formula then b else a) p v 0 hfiber (by simp)
  have hold : (statusGraph P X Y A.termProjection.graph A.formulaProjection.graph).val.Evalb
      ![p, childStack (if formula then b else a) v 0 + 1] := by simp [hp, hstack]
  cases formula
  · obtain ⟨_, hv⟩ := A.term_support_model p v value hop
    have hnew : (statusGraph P X Y A.termProjection.graph A.formulaProjection.graph).val.Evalb
        ![p, adjoin ⟪value, 0⟫ 0 + 1] := by simp [rawFiber, hp, hv.1, hv.2]
    exact (A.valueStepGraph_term p (shape a u) (childStack a v 0) _).mpr
      ⟨shape_carrier a u hsource, hold, hnew, Or.inr ⟨v, 0, value, hr, hop, rfl⟩⟩
  · obtain ⟨_, hv⟩ := A.formula_support_model p v value hop
    have hnew : (statusGraph P X Y A.termProjection.graph A.formulaProjection.graph).val.Evalb
        ![p, adjoin ⟪value, 1⟫ 0 + 1] := by simp [rawFiber, hp, hv.1, hv.2]
    exact (A.valueStepGraph_formula p (shape b u) (childStack b v 0) _).mpr
      ⟨shape_carrier b u hsource, hold, hnew, Or.inr ⟨v, 0, value, hr, hop, rfl⟩⟩

/-- All child traces are framed over their existing tail and
concatenated arithmetically; one final positive root-operation trace is
then appended. This constructs a genuine witness of evaluation. -/
theorem evaluation_of_mapRaw (formula : Bool) (p u v value : M)
    (hm : (mapRaw P (A.evaluationFormula false) (A.evaluationFormula true)
      (if formula then b else a)).val.Evalb ![p, u, v])
    (hop : (if formula then A.formulaOp else A.termOp).val.Evalb ![p, v, value]) :
    (A.evaluationFormula formula).val.Evalb
      ![p, constructor formula (if formula then b else a) u, value] := by
  obtain ⟨hp, hsource, _⟩ := A.mapRaw_evaluation_fiber (if formula then b else a) p u v hm
  obtain ⟨states, htrace, hend⟩ := A.children_trace (if formula then b else a) p u v 0 hp hm (by simp)
  have htrace' : A.TraceRecord p (childrenWord (if formula then b else a) u) 1
      (len (childrenWord (if formula then b else a) u)) states := by simpa using htrace
  have hstep := A.root_valueStep formula p u v value hm hop
  rw [← hend] at hstep
  obtain ⟨whole, hwhole⟩ := A.traceRecord_snoc htrace' hstep
  have hcarrier : (carrier formula a b).val.Evalb ![constructor formula (if formula then b else a) u] := by
    cases formula
    · exact term_constructor_carrier a b u hsource
    · exact formula_constructor_carrier a b u hsource
  have hc := ((carrier_eval formula a b _).mp hcarrier).1
  apply (A.evaluationFormula_eval formula p _ value).mpr
  refine ⟨hcarrier, (A.loopEvaluationGraph_eval p _ _).mpr ⟨hp, hc,
    concat states (adjoin ⟪value, if formula then 1 else 0⟫ 0 + 1), ?_, ?_⟩⟩
  · apply (traceRecord_one A p _ _ _).mp
    simpa [constructor] using whole
  · simpa [constructor] using hwhole.symm

/-- The actual finite-record evaluator satisfies the displayed
constructor recursion equation on its genuine raw polynomial domain.
The reverse direction uses actual root-input existence and evaluator
functionality, not an assumed recursion law. -/
theorem evaluation_constructor (formula : Bool) (p u value : M)
    (hp : P.val.Evalb ![p])
    (hu : (rawCarrier (carrier false a b) (carrier true a b)
      (if formula then b else a)).val.Evalb ![u]) :
    ((A.evaluationFormula formula).val.Evalb
      ![p, constructor formula (if formula then b else a) u, value] ↔ ∃ v : M,
      (mapRaw P (A.evaluationFormula false) (A.evaluationFormula true)
        (if formula then b else a)).val.Evalb ![p, u, v] ∧
      (if formula then A.formulaOp else A.termOp).val.Evalb ![p, v, value]) := by
  constructor
  · intro he
    obtain ⟨v, hm⟩ := A.mapRaw_evaluation_exists (if formula then b else a) p u hp hu
    have hf := (A.mapRaw_evaluation_fiber (if formula then b else a) p u v hm).2.2
    have htotal : ∃! output : M,
        (if formula then A.formulaOp else A.termOp).val.Evalb ![p, v, output] := by
      cases formula
      · exact A.term_total_model p v hf
      · exact A.formula_total_model p v hf
    obtain ⟨output, hop, _⟩ := htotal
    have houtput := A.evaluation_of_mapRaw formula p u v output hm hop
    have hcarrier : (carrier formula a b).val.Evalb ![constructor formula (if formula then b else a) u] :=
      (A.evaluation_fiber formula p _ output houtput).2.1
    have heq := (A.evaluation_existsUnique formula p _ hp hcarrier).unique he houtput
    exact ⟨v, hm, by simpa [heq] using hop⟩
  · rintro ⟨v, hm, hop⟩
    exact A.evaluation_of_mapRaw formula p u v value hm hop

/-- The canonical constructor equations are proved from the actual
forward records; no evaluator equation is supplied as algebra data. -/
theorem evaluation_root_equations :
    A.RootEquations (M := M) (A.evaluationFormula false) (A.evaluationFormula true) := by
  constructor
  · intro p u value hp hu
    exact A.evaluation_constructor false p u value hp hu
  · intro p u value hp hu
    exact A.evaluation_constructor true p u value hp hu


end Models
end CategoricalEssentialIncompleteness.V46.SyntacticSyntax.SliceAlgebra
