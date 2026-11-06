/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46UniformTraceArithmetic
import CategoricalEssentialIncompleteness.ClassicalDiagonalArithmetic

/-! # Arithmetic codes for the chosen syntactic Turing diagonal

The numerical index represents the diagonal of the printed universal
program from Lemma 5.1. Its comparison with the actual uniform graph
holds at every element of every PA model.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open FailureOfComposition FailureOfComposition.ConcreteEvaluator
open FailureOfComposition.ProofSearch FailureOfComposition.TypedTuringMorphism

namespace CategoricalEssentialIncompleteness.V46.ArithmeticDiagonalCodes

/-- The actual printed diagonal applies the program encoded by its own
input index to that same input. -/
def diagonalGraph : Graph :=
  let G := UniformTrace.graph
  .mkSigma “x y. !G.val x x y”

theorem diagonalGraph_functional : 𝗣𝗔 ⊢ functionalSentence diagonalGraph := by
  apply complete.{0} 𝗣𝗔
  intro M _ _
  rw [models_iff,functionalSentence_eval]
  intro x y z hy hz
  have hy' : UniformTrace.graph.val.Evalb ![x,x,y] := by
    simpa [diagonalGraph] using hy
  have hz' : UniformTrace.graph.val.Evalb ![x,x,z] := by
    simpa [diagonalGraph] using hz
  exact UniformTrace.output_unique x x y z hy' hz'

/-- Functional Sigma-one search supplies the actual closed program index. -/
def diagonalIndex : ℕ := SyntacticSearch.searchIndex diagonalGraph

theorem diagonalIndex_uniform : Uniform 𝗣𝗔 (eventualGraph diagonalIndex) diagonalGraph :=
  SyntacticSearch.search_uniform_of_functional 𝗣𝗔 diagonalGraph diagonalGraph_functional

/-- The unary predicate uses the literal even/odd output arithmetic. -/
def outputPredicate (j : ℕ) : 𝚺₁.Semisentence 1 :=
  let G := UniformTrace.graph
  .mkSigma “x. ∃ m, !G.val !!diagonalIndex x (2 * m + !!j)”

abbrev alpha : 𝚺₁.Semisentence 1 := outputPredicate 0
abbrev beta : 𝚺₁.Semisentence 1 := outputPredicate 1

section Models
variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
local instance diagonalCodesLocalInstance1 : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ :=
  models_of_subtheory (U := 𝗣𝗔) inferInstance
local instance diagonalCodesLocalInstance2 : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 :=
  models_of_subtheory (U := 𝗜𝚺₁) inferInstance

omit [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] in
@[simp] theorem diagonalGraph_eval (x y : M) :
    diagonalGraph.val.Evalb ![x,y] ↔
      UniformTrace.graph.val.Evalb ![x,x,y] := by
  simp [diagonalGraph]

/-- The output graph at the actual chosen index agrees with the printed
universal diagonal at every input of every PA model. -/
theorem diagonal_graph (x y : M) :
    UniformTrace.graph.val.Evalb ![(diagonalIndex : M),x,y] ↔
      UniformTrace.graph.val.Evalb ![x,x,y] := by
  have hs := canonicalPartrecGraphFormula_eval_iff_eventualGraph
    (M := M) diagonalIndex x y
  simp only [numeral_eq_natCast_app] at hs
  have hu := consequence_iff.mp (Theory.Proof.sound diagonalIndex_uniform) M inferInstance
  rw [models_iff,uniformSentence_eval] at hu
  exact hs.trans ((hu x y).trans (diagonalGraph_eval x y))

@[simp] theorem outputPredicate_eval (j : ℕ) (x : M) :
    (outputPredicate j).val.Evalb ![x] ↔
      ∃ m : M, UniformTrace.graph.val.Evalb
        ![(diagonalIndex : M),x,2 * m + (j : M)] := by
  simp [outputPredicate,numeral_eq_natCast]

@[simp] theorem alpha_eval (x : M) :
    alpha.val.Evalb ![x] ↔
      ∃ m : M, UniformTrace.graph.val.Evalb ![(diagonalIndex : M),x,2 * m] := by
  simpa only [Nat.cast_zero,add_zero] using outputPredicate_eval 0 x

@[simp] theorem beta_eval (x : M) :
    beta.val.Evalb ![x] ↔
      ∃ m : M, UniformTrace.graph.val.Evalb ![(diagonalIndex : M),x,2 * m + 1] := by
  simpa only [Nat.cast_one] using outputPredicate_eval 1 x

theorem output_disjoint (x : M) :
    ¬(alpha.val.Evalb ![x] ∧ beta.val.Evalb ![x]) := by
  rintro ⟨ha,hb⟩
  obtain ⟨a,ha⟩ := (alpha_eval x).mp ha
  obtain ⟨b,hb⟩ := (beta_eval x).mp hb
  have he := UniformTrace.output_unique (diagonalIndex : M) x _ _ ha hb
  have hm := congrArg (fun w : M => w % 2) he
  simp at hm

end Models

def diagonalComparisonSentence : ArithmeticSentence :=
  let G := UniformTrace.graph
  let D := diagonalGraph
  let E := eventualGraph diagonalIndex
  “∀ x y, (!G.val !!diagonalIndex x y ↔ !D.val x y) ∧
    (!D.val x y ↔ !E.val x y)”

theorem diagonal_comparison_PA : 𝗣𝗔 ⊢ diagonalComparisonSentence := by
  apply complete.{0} 𝗣𝗔
  intro M _ _
  have hs := fun (x y : M) => canonicalPartrecGraphFormula_eval_iff_eventualGraph
    (M := M) diagonalIndex x y
  simp only [numeral_eq_natCast_app] at hs
  have h : ∀ x y : M,
      (UniformTrace.graph.val.Evalb ![(diagonalIndex : M),x,y] ↔
        diagonalGraph.val.Evalb ![x,y]) ∧
      (diagonalGraph.val.Evalb ![x,y] ↔
        (eventualGraph diagonalIndex).val.Evalb ![x,y]) := by
    intro x y
    have he := (diagonal_graph x y).trans (diagonalGraph_eval x y).symm
    exact ⟨he,he.symm.trans (hs x y)⟩
  simpa [models_iff,diagonalComparisonSentence,numeral_eq_natCast_app] using h

def diagonalSourceSentence : ArithmeticSentence :=
  let G := UniformTrace.graph
  “∀ x y, !G.val !!diagonalIndex x y ↔ !G.val x x y”

theorem diagonal_source_PA : 𝗣𝗔 ⊢ diagonalSourceSentence := by
  apply complete.{0} 𝗣𝗔
  intro M _ _
  simpa [models_iff,diagonalSourceSentence,numeral_eq_natCast_app] using
    (diagonal_graph (M := M))

def disjointSentence : ArithmeticSentence :=
  ∀¹ (∼(alpha.val ⋏ beta.val))

theorem disjoint_PA : 𝗣𝗔 ⊢ disjointSentence := by
  apply complete.{0} 𝗣𝗔
  intro M _ _
  simpa only [models_iff,disjointSentence,Semiformula.eval_all,
    LogicalConnective.HomClass.map_neg,LogicalConnective.HomClass.map_and,
    LogicalConnective.Prop.neg_eq,LogicalConnective.Prop.and_eq] using
      (output_disjoint (M := M))

/-- A standard successful computation yields a proof of its individual
numeral instance. This statement uses the actual newly chosen predicate. -/
theorem output_numeral_PA (j n : ℕ)
    (h : (outputPredicate j).val.Evalb (M := ℕ) ![n]) :
    𝗣𝗔 ⊢ ((outputPredicate j).val/[(↑n : ArithmeticSemiterm Empty 0)] :
      ArithmeticSentence) := by
  let : 𝗥₀ ⪯ 𝗣𝗔 := WeakerThan.trans (𝓣 := 𝗣𝗔⁻) inferInstance inferInstance
  apply sigma_one_completeness (by simp)
  simpa [models_iff] using h

/-- A standard odd computation yields a PA refutation of the alpha
instance by the proved uniform functionality and parity theorem. -/
theorem beta_numeral_refutes_alpha (n : ℕ)
    (h : beta.val.Evalb (M := ℕ) ![n]) :
    𝗣𝗔 ⊢ ∼(alpha.val/[(↑n : ArithmeticSemiterm Empty 0)] : ArithmeticSentence) := by
  have hb := output_numeral_PA 1 n h
  apply complete.{0} 𝗣𝗔
  intro M _ _
  rw [Semantics.Not.models_not,
    LocalConnectedness.ClassicalPrograms.numeralInstance_eval]
  intro ha
  have hbM := consequence_iff.mp (Theory.Proof.sound hb) M inferInstance
  rw [LocalConnectedness.ClassicalPrograms.numeralInstance_eval] at hbM
  exact output_disjoint _ ⟨ha,hbM⟩

end CategoricalEssentialIncompleteness.V46.ArithmeticDiagonalCodes
