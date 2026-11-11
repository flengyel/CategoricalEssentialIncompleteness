/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SyntacticSyntaxSimulation
public import CategoricalEssentialIncompleteness.V46SyntacticPredicatesLimits

/-! # Sigma-one evaluation maps on the literal two-sort postfix carriers -/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open FailureOfComposition.ProofSearch FailureOfComposition.CodedObjectMembership
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates

namespace CategoricalEssentialIncompleteness.V46.SyntacticSyntax.SliceAlgebra
open Coding Postfix
variable {T : ArithmeticTheory} {P X Y : Carrier} {a b : RawPolynomial}
variable (A : SliceAlgebra T P X Y a b)

/-- A literal accepted word is evaluated by its full finite state vector,
with one final tagged value of the requested sort. -/
def evaluationFormula (formula : Bool) : 𝚺₁.Semisentence 3 :=
  let C := carrier formula a b
  let E := A.loopEvaluationGraph
  match formula with
  | false => .mkSigma “p word value. !C.val word ∧ ∃ status block stack,
      !E.val p word status ∧ !pairDef.val block value 0 ∧
      !adjoinDef.val stack block 0 ∧ status = stack + 1”
  | true => .mkSigma “p word value. !C.val word ∧ ∃ status block stack,
      !E.val p word status ∧ !pairDef.val block value 1 ∧
      !adjoinDef.val stack block 0 ∧ status = stack + 1”

section Models
variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] [M↓[ℒₒᵣ] ⊧* T]

omit [M↓[ℒₒᵣ] ⊧* T] in
@[simp] theorem evaluationFormula_eval (formula : Bool) (p word value : M) :
    (A.evaluationFormula formula).val.Evalb ![p, word, value] ↔
      (carrier formula a b).val.Evalb ![word] ∧
        A.loopEvaluationGraph.val.Evalb
          ![p, word, adjoin ⟪value, if formula then 1 else 0⟫ 0 + 1] := by
  cases formula <;> simp [evaluationFormula]

/-- Internal PA record existence plus the parser/value sort simulation
produces an actual value for every accepted literal word. -/
theorem evaluation_existsUnique (formula : Bool) (p word : M)
    (hp : P.val.Evalb ![p]) (hw : (carrier formula a b).val.Evalb ![word]) :
    ∃! value : M, (A.evaluationFormula formula).val.Evalb ![p, word, value] := by
  have hc := ((carrier_eval formula a b word).mp hw).1
  obtain ⟨states, hs⟩ := A.valueRecord_exists p word hp hc
  obtain ⟨value, hv⟩ := A.valueRecord_singleton formula hs hw
  have hloop : A.loopEvaluationGraph.val.Evalb ![p, word, nth states (len word)] :=
    (A.loopEvaluationGraph_eval p word _).mpr ⟨hp, hc, states, hs, rfl⟩
  refine ⟨value, (A.evaluationFormula_eval formula p word value).mpr ⟨hw, by simpa [hv] using hloop⟩, ?_⟩
  intro z hz
  have hzloop := ((A.evaluationFormula_eval formula p word z).mp hz).2
  have hvloop := ((A.evaluationFormula_eval formula p word value).mp
    ((A.evaluationFormula_eval formula p word value).mpr ⟨hw, by simpa [hv] using hloop⟩)).2
  have he := (A.loopEvaluation_existsUnique p word hp hc).unique hzloop hvloop
  have hb := ((adjoin_inj _ _ _ _).mp (add_right_cancel he)).1
  simpa using congrArg (pi₁ : M → M) hb

omit [M↓[ℒₒᵣ] ⊧* T] in
/-- The final state's positive common-fiber assertion supplies the
actual target membership and its supplied projection to the parameter. -/
theorem evaluation_fiber (formula : Bool) (p word value : M)
    (h : (A.evaluationFormula formula).val.Evalb ![p, word, value]) :
    P.val.Evalb ![p] ∧ (carrier formula a b).val.Evalb ![word] ∧
      (if formula then A.FormulaFiber p value else A.TermFiber p value) := by
  obtain ⟨hw, hl⟩ := (A.evaluationFormula_eval formula p word value).mp h
  obtain ⟨hp, _, states, hs, hout⟩ := (A.loopEvaluationGraph_eval p word _).mp hl
  have hstate := hs.2.1 (len word) (by rw [hs.1]; simp)
  rw [← hout] at hstate
  have hstack : (fiberStackGraph P X Y A.termProjection.graph A.formulaProjection.graph).val.Evalb
      ![p, adjoin ⟪value, if formula then 1 else 0⟫ 0] := by
    simpa using ((statusGraph_eval P X Y A.termProjection.graph A.formulaProjection.graph p _).mp hstate).2
  have hblock := ((fiberStackGraph_adjoin P X Y A.termProjection.graph A.formulaProjection.graph
    p ⟪value, if formula then 1 else 0⟫ 0).mp hstack).1
  refine ⟨hp, hw, ?_⟩
  cases formula <;> simpa [rawFiber, TermFiber, FormulaFiber, hp] using hblock

end Models

/-- The categorical adapter pairs the arbitrary parameter with the
literal word; the finite record remains an existential graph witness. -/
def evaluationGraph (formula : Bool) : Graph :=
  let E := A.evaluationFormula formula
  .mkSigma “source value. ∃ p word, !pairDef.val source p word ∧ !E.val p word value”

variable [𝗣𝗔 ⪯ T]

def evaluationMorphism (formula : Bool) :
    GraphMorphism T (productCarrier P (carrier formula a b)) (if formula then Y else X) where
  graph := A.evaluationGraph formula
  support := by
    apply complete.{0} T
    intro M _ _
    let : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 := models_of_subtheory (U := T) inferInstance
    rw [models_iff, supportSentence_eval]
    intro source value h
    have he : ∃ p word : M, source = Arithmetic.pair p word ∧
        (A.evaluationFormula formula).val.Evalb ![p, word, value] := by
      simpa [evaluationGraph] using h
    obtain ⟨p, word, hsource, hv⟩ := he
    obtain ⟨hp, hw, hf⟩ := A.evaluation_fiber formula p word value hv
    refine ⟨(productCarrier_eval P (carrier formula a b) source).mpr
      ⟨p, word, hsource, hp, hw⟩, ?_⟩
    cases formula <;> exact hf.1
  total := by
    apply complete.{0} T
    intro M _ _
    let : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 := models_of_subtheory (U := T) inferInstance
    rw [models_iff, totalSentence_eval]
    intro source hs
    obtain ⟨p, word, hsource, hp, hw⟩ :=
      (productCarrier_eval P (carrier formula a b) source).mp hs
    obtain ⟨value, hv, hu⟩ := A.evaluation_existsUnique formula p word hp hw
    refine ⟨value, ?_, ?_⟩
    · have hWitness : ∃ p' word' : M, source = Arithmetic.pair p' word' ∧
          (A.evaluationFormula formula).val.Evalb ![p', word', value] := ⟨p, word, hsource, hv⟩
      simpa [evaluationGraph] using hWitness
    · intro z hz
      have he : ∃ p' word' : M, source = Arithmetic.pair p' word' ∧
          (A.evaluationFormula formula).val.Evalb ![p', word', z] := by
        simpa [evaluationGraph] using hz
      obtain ⟨p', word', he', hz'⟩ := he
      obtain ⟨hp', hw'⟩ := (pair_eq_pair_iff _ _ _ _).mp (he'.symm.trans hsource)
      subst p'
      subst word'
      exact hu z hz'

def evaluationOverSentence (formula : Bool) : ArithmeticSentence :=
  let E := A.evaluationFormula formula
  let ξ := if formula then A.formulaProjection.graph else A.termProjection.graph
  “∀ p word value, !E.val p word value → !ξ.val value p”

theorem evaluation_over (formula : Bool) : T ⊢ A.evaluationOverSentence formula := by
  apply complete.{0} T
  intro M _ _
  let : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 := models_of_subtheory (U := T) inferInstance
  have he : ∀ p word value : M, (A.evaluationFormula formula).val.Evalb ![p, word, value] →
      (if formula then A.formulaProjection.graph else A.termProjection.graph).val.Evalb ![value, p] := by
    intro p word value hv
    have hf := (A.evaluation_fiber formula p word value hv).2.2
    cases formula <;> exact hf.2
  simpa [models_iff, evaluationOverSentence] using he

end CategoricalEssentialIncompleteness.V46.SyntacticSyntax.SliceAlgebra
