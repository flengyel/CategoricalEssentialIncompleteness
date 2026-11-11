/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46UniformTraceTemplates

/-! # Uniform composition and specialization by genuine template compilation

The arbitrary program indices are data for fixed universal templates. The
parameter compiler builds actual program indices and has already been proved
correct in every PA model, including at nonstandard parameter values.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open FailureOfComposition FailureOfComposition.ProofSearch FailureOfComposition.ConcreteEvaluator

namespace CategoricalEssentialIncompleteness.V46.UniformTrace

def specializationTemplateGraph : Graph :=
  let G := graph
  let E := ExponentialPairing.graph
  .mkSigma “data output. ∃ params input e a paired,
    !pairDef.val data params input ∧ !pairDef.val params e a ∧
    !E.val paired a input ∧ !G.val e paired output”

def compositionTemplateGraph : Graph :=
  let G := graph
  .mkSigma “data output. ∃ params input f e middle,
    !pairDef.val data params input ∧ !pairDef.val params f e ∧
    !G.val e input middle ∧ !G.val f middle output”

section Models
variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
local instance buildersTemplateModelsSigma : M↓[ℒₒᵣ] ⊧* 𝗜𝚺 1 :=
  models_of_subtheory (U := 𝗣𝗔) inferInstance
local instance buildersTemplateModelsOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 :=
  models_of_subtheory (U := 𝗜𝚺 1) inferInstance


@[simp] theorem specializationTemplateGraph_model (data output : M) :
    specializationTemplateGraph.val.Evalb ![data, output] ↔
      graph.val.Evalb
        ![π₁ (π₁ data), ExponentialPairing.code (π₂ (π₁ data)) (π₂ data), output] := by
  obtain ⟨p, x, rfl⟩ : ∃ p x : M, data = ⟪p, x⟫ :=
    ⟨π₁ data, π₂ data, (pair_unpair data).symm⟩
  obtain ⟨e, a, rfl⟩ : ∃ e a : M, p = ⟪e, a⟫ :=
    ⟨π₁ p, π₂ p, (pair_unpair p).symm⟩
  simp [specializationTemplateGraph]

@[simp] theorem compositionTemplateGraph_model (data output : M) :
    compositionTemplateGraph.val.Evalb ![data, output] ↔ ∃ middle : M,
      graph.val.Evalb ![π₂ (π₁ data), π₂ data, middle] ∧
        graph.val.Evalb ![π₁ (π₁ data), middle, output] := by
  obtain ⟨p, x, rfl⟩ : ∃ p x : M, data = ⟪p, x⟫ :=
    ⟨π₁ data, π₂ data, (pair_unpair data).symm⟩
  obtain ⟨f, e, rfl⟩ : ∃ f e : M, p = ⟪f, e⟫ :=
    ⟨π₁ p, π₂ p, (pair_unpair p).symm⟩
  simp [compositionTemplateGraph]

end Models

theorem specializationTemplateGraph_functional :
    𝗣𝗔 ⊢ functionalSentence specializationTemplateGraph := by
  apply complete.{0} 𝗣𝗔
  intro M _ _
  rw [models_iff, functionalSentence_eval]
  intro data y z hy hz
  rw [specializationTemplateGraph_model] at hy hz
  exact output_unique _ _ y z hy hz

theorem compositionTemplateGraph_functional : 𝗣𝗔 ⊢ functionalSentence compositionTemplateGraph := by
  apply complete.{0} 𝗣𝗔
  intro M _ _
  rw [models_iff, functionalSentence_eval]
  intro data y z hy hz
  obtain ⟨a, ha, hay⟩ := (compositionTemplateGraph_model data y).mp hy
  obtain ⟨b, hb, hbz⟩ := (compositionTemplateGraph_model data z).mp hz
  have hab : a = b := output_unique _ _ a b ha hb
  subst b
  exact output_unique _ _ y z hay hbz

def specializationTemplateIndex : ℕ := SyntacticSearch.searchIndex specializationTemplateGraph
def compositionTemplateIndex : ℕ := SyntacticSearch.searchIndex compositionTemplateGraph

section Models
variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
local instance buildersBuilderDefinitionsSigma : M↓[ℒₒᵣ] ⊧* 𝗜𝚺 1 :=
  models_of_subtheory (U := 𝗣𝗔) inferInstance
local instance buildersBuilderDefinitionsOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 :=
  models_of_subtheory (U := 𝗜𝚺 1) inferInstance


noncomputable def specialize (e a : M) : M := templateIndex specializationTemplateIndex ⟪e, a⟫
noncomputable def compose (f e : M) : M := templateIndex compositionTemplateIndex ⟪f, e⟫

end Models

def specializationGraph : 𝚺₁.Semisentence 3 :=
  let B := templateIndexGraph specializationTemplateIndex
  .mkSigma “o e a. ∃ p, !pairDef.val p e a ∧ !B.val o p”

def compositionGraph : 𝚺₁.Semisentence 3 :=
  let B := templateIndexGraph compositionTemplateIndex
  .mkSigma “o f e. ∃ p, !pairDef.val p f e ∧ !B.val o p”

section Models
variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
local instance buildersLocalInstance1 : M↓[ℒₒᵣ] ⊧* 𝗜𝚺 1 :=
  models_of_subtheory (U := 𝗣𝗔) inferInstance
local instance buildersLocalInstance2 : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 :=
  models_of_subtheory (U := 𝗜𝚺 1) inferInstance

@[simp] theorem specializationGraph_eval (o e a : M) :
    specializationGraph.val.Evalb ![o, e, a] ↔ o = specialize e a := by
  simp [specializationGraph, specialize]

@[simp] theorem compositionGraph_eval (o f e : M) :
    compositionGraph.val.Evalb ![o, f, e] ↔ o = compose f e := by
  simp [compositionGraph, compose]

instance specialize_defined : 𝚺₁-Function₂ (specialize : M → M → M) via specializationGraph :=
  .mk fun v => by
    have hv : ![v 0, v 1, v 2] = v := (Matrix.fun_eq_vec_three v).symm
    simpa only [hv, Fin.succ_zero_eq_one, Fin.succ_one_eq_two] using
      specializationGraph_eval (v 0) (v 1) (v 2)
instance specialize_definable : 𝚺₁-Function₂ (specialize : M → M → M) :=
  specialize_defined.to_definable
instance specialize_definable' (Γ m) : Γ-[m + 1]-Function₂ (specialize : M → M → M) :=
  specialize_definable.of_sigmaOne
instance compose_defined : 𝚺₁-Function₂ (compose : M → M → M) via compositionGraph :=
  .mk fun v => by
    have hv : ![v 0, v 1, v 2] = v := (Matrix.fun_eq_vec_three v).symm
    simpa only [hv, Fin.succ_zero_eq_one, Fin.succ_one_eq_two] using
      compositionGraph_eval (v 0) (v 1) (v 2)
instance compose_definable : 𝚺₁-Function₂ (compose : M → M → M) := compose_defined.to_definable
instance compose_definable' (Γ m) : Γ-[m + 1]-Function₂ (compose : M → M → M) :=
  compose_definable.of_sigmaOne

theorem template_search_graph (R : Graph) (hR : 𝗣𝗔 ⊢ functionalSentence R)
    (a input output : M) :
    graph.val.Evalb ![templateIndex (SyntacticSearch.searchIndex R) a, input, output] ↔
      R.val.Evalb ![⟪a, input⟫, output] := by
  rw [templateIndex_graph]
  have hsection := canonicalPartrecGraphFormula_eval_iff_eventualGraph
    (M := M) (SyntacticSearch.searchIndex R) ⟪a, input⟫ output
  simp only [numeral_eq_natCast_app] at hsection
  have hU := SyntacticSearch.search_uniform_of_functional 𝗣𝗔 R hR
  have hmodel := consequence_iff.mp (Theory.Proof.sound hU) M inferInstance
  rw [models_iff, uniformSentence_eval] at hmodel
  exact hsection.trans (hmodel ⟪a, input⟫ output)

/-- All indices and the parameter are free model variables. The only
fixed index used inside the proof is the one closed search template. -/
theorem specialize_eval (e a input output : M) :
    graph.val.Evalb ![specialize e a, input, output] ↔
      graph.val.Evalb ![e, ExponentialPairing.code a input, output] := by
  have h := template_search_graph specializationTemplateGraph
    specializationTemplateGraph_functional ⟪e, a⟫ input output
  simpa only [specialize, specializationTemplateIndex, specializationTemplateGraph_model,
    pi₁_pair, pi₂_pair] using h

/-- Actual relational composition at arbitrary internal program indices. -/
theorem compose_eval (f e input output : M) :
    graph.val.Evalb ![compose f e, input, output] ↔ ∃ middle : M,
      graph.val.Evalb ![e, input, middle] ∧ graph.val.Evalb ![f, middle, output] := by
  have h := template_search_graph compositionTemplateGraph
    compositionTemplateGraph_functional ⟪f, e⟫ input output
  simpa only [compose, compositionTemplateIndex, compositionTemplateGraph_model,
    pi₁_pair, pi₂_pair] using h

end Models

def specializationSentence : ArithmeticSentence :=
  let S := specializationGraph
  let G := graph
  let E := ExponentialPairing.graph
  “∀ e a p x y, !S.val p e a → (!G.val p x y ↔ ∃ z, !E.val z a x ∧ !G.val e z y)”

theorem specialization_PA : 𝗣𝗔 ⊢ specializationSentence := by
  apply complete.{0} 𝗣𝗔
  intro M _ _
  have hmodel : ∀ e a p x y : M, specializationGraph.val.Evalb ![p, e, a] →
      (graph.val.Evalb ![p, x, y] ↔ ∃ z : M,
        ExponentialPairing.graph.val.Evalb ![z, a, x] ∧ graph.val.Evalb ![e, z, y]) := by
    intro e a p x y hp
    have he : p = specialize e a := (specializationGraph_eval p e a).mp hp
    subst p
    rw [specialize_eval]
    simp
  simpa [models_iff, specializationSentence] using hmodel

def compositionSentence : ArithmeticSentence :=
  let C := compositionGraph
  let G := graph
  “∀ f e p x z, !C.val p f e → (!G.val p x z ↔ ∃ y, !G.val e x y ∧ !G.val f y z)”

theorem composition_PA : 𝗣𝗔 ⊢ compositionSentence := by
  apply complete.{0} 𝗣𝗔
  intro M _ _
  have hmodel : ∀ f e p x z : M, compositionGraph.val.Evalb ![p, f, e] →
      (graph.val.Evalb ![p, x, z] ↔ ∃ y : M,
        graph.val.Evalb ![e, x, y] ∧ graph.val.Evalb ![f, y, z]) := by
    intro f e p x z hp
    have he : p = compose f e := (compositionGraph_eval p f e).mp hp
    subst p
    exact compose_eval f e x z
  simpa [models_iff, compositionSentence] using hmodel

def buildersTotalitySentence : ArithmeticSentence :=
  let S := specializationGraph
  let C := compositionGraph
  “(∀ e a, ∃ p, !S.val p e a ∧ ∀ q, !S.val q e a → q = p) ∧
    (∀ f e, ∃ p, !C.val p f e ∧ ∀ q, !C.val q f e → q = p)”

theorem builders_totality_PA : 𝗣𝗔 ⊢ buildersTotalitySentence := by
  apply complete.{0} 𝗣𝗔
  intro M _ _
  simp [models_iff, buildersTotalitySentence]

end CategoricalEssentialIncompleteness.V46.UniformTrace
