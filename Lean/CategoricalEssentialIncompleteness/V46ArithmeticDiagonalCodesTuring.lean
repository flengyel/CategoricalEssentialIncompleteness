/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46ArithmeticDiagonalCodesModels

/-! # A proved adapter from the old Turing map to the printed universal map

The two maps are not identified. The adapter is an actual PA-total
specializer program, with a categorical factorization proved from the
uniform graph equations at arbitrary internal indices and inputs.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.RestrictionCategory
open FailureOfComposition FailureOfComposition.ConcreteEvaluator
open FailureOfComposition.ProofSearch FailureOfComposition.TypedProgramCategory
open FailureOfComposition.TypedTuringMorphism FailureOfComposition.TypedNearProduct
open CategoricalEssentialIncompleteness.LocalConnectedness

namespace CategoricalEssentialIncompleteness.V46.ArithmeticDiagonalCodes

/-- This one fixed program presents the old Turing map with exponential
input coordinates. The old parameter remains input data. -/
def oldTauTemplateGraph : Graph :=
  let E := ExponentialPairing.graph
  let H := tauGraph
  .mkSigma “input y. ∃ q x z, !E.val input q x ∧ !pairDef.val z q x ∧ !H.val z y”

section Models
variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

@[simp] theorem oldTauTemplateGraph_eval (input y : M) :
    oldTauTemplateGraph.val.Evalb ![input,y] ↔
      ∃ q x : M, input = ExponentialPairing.code q x ∧
        (eventualGraph tauIndex).val.Evalb ![pair q x,y] := by
  simp only [eventualGraph_tauIndex_eval]
  simp [oldTauTemplateGraph]

theorem oldTauTemplateGraph_code (q x y : M) :
    oldTauTemplateGraph.val.Evalb ![ExponentialPairing.code q x,y] ↔
      (eventualGraph tauIndex).val.Evalb ![pair q x,y] := by
  rw [oldTauTemplateGraph_eval]
  constructor
  · rintro ⟨a,b,he,hy⟩
    obtain ⟨rfl,rfl⟩ := ExponentialPairing.code_injective he
    exact hy
  · intro hy
    exact ⟨q,x,rfl,hy⟩

end Models

theorem oldTauTemplateGraph_functional : 𝗣𝗔 ⊢ functionalSentence oldTauTemplateGraph := by
  apply complete.{0} 𝗣𝗔
  intro M _ _
  rw [models_iff,functionalSentence_eval]
  intro input y z hy hz
  obtain ⟨q,x,he,hy⟩ := (oldTauTemplateGraph_eval input y).mp hy
  obtain ⟨r,a,hf,hz⟩ := (oldTauTemplateGraph_eval input z).mp hz
  obtain ⟨rfl,rfl⟩ := ExponentialPairing.code_injective (he.symm.trans hf)
  exact eventualGraph_output_unique tauIndex (pair q x) y z hy hz

def oldTauTemplateIndex : ℕ := SyntacticSearch.searchIndex oldTauTemplateGraph

theorem oldTauTemplate_uniform :
    Uniform 𝗣𝗔 (eventualGraph oldTauTemplateIndex) oldTauTemplateGraph :=
  SyntacticSearch.search_uniform_of_functional 𝗣𝗔 oldTauTemplateGraph oldTauTemplateGraph_functional

/-- A genuine program computes q -> s(v,q); its PA totality was constructed
in Lemma 5.1 rather than supplied as a choice of parameter arrows. -/
def adapterIndex : ℕ := UniformTrace.specializerSectionIndex oldTauTemplateIndex

def adapter : omegaObject 𝗣𝗔 ⟶ omegaObject 𝗣𝗔 :=
  arrowOfIndex 𝗣𝗔 .omega .omega adapterIndex

section Models
variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
local instance diagonalTuringLocalInstance1 : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ :=
  models_of_subtheory (U := 𝗣𝗔) inferInstance
local instance diagonalTuringLocalInstance2 : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 :=
  models_of_subtheory (U := 𝗜𝚺₁) inferInstance

theorem adapter_program_graph (q r : M) :
    (eventualGraph adapterIndex).val.Evalb ![q,r] ↔
      r = UniformTrace.specialize (oldTauTemplateIndex : M) q := by
  have hs := canonicalPartrecGraphFormula_eval_iff_eventualGraph
    (M := M) adapterIndex q r
  simp only [numeral_eq_natCast_app] at hs
  exact hs.symm.trans (UniformTrace.specializerSection_eval oldTauTemplateIndex q r)

/-- The selected specialized index simulates precisely the old Turing
application at all parameters and inputs of an arbitrary PA model. -/
theorem adapter_application (q x y : M) :
    UniformTrace.graph.val.Evalb
      ![UniformTrace.specialize (oldTauTemplateIndex : M) q,x,y] ↔
      (eventualGraph tauIndex).val.Evalb ![pair q x,y] := by
  rw [UniformTrace.specialize_eval]
  have hs := canonicalPartrecGraphFormula_eval_iff_eventualGraph
    (M := M) oldTauTemplateIndex (ExponentialPairing.code q x) y
  simp only [numeral_eq_natCast_app] at hs
  have hu := consequence_iff.mp (Theory.Proof.sound oldTauTemplate_uniform) M inferInstance
  rw [models_iff,uniformSentence_eval] at hu
  exact hs.trans ((hu _ y).trans (oldTauTemplateGraph_code q x y))

theorem adapter_relation (q r : M) :
    SyntacticModel.programRelation 𝗣𝗔 M adapter.val q r ↔
      r = UniformTrace.specialize (oldTauTemplateIndex : M) q := by
  rw [adapter,arrowOfIndex_val,SyntacticModel.programRelation_class,
    eventualGraph_normalizeIndex_eval]
  simp only [CodedObjectMembership.memberFormula_omega_eval,true_and,and_true]
  exact adapter_program_graph q r

end Models

theorem adapter_total : isTotal adapter := by
  apply (arrowOfIndex_isTotal_iff_proves_typedTotality 𝗣𝗔 .omega .omega adapterIndex).mpr
  apply complete.{0} 𝗣𝗔
  intro M _ _
  rw [models_iff,typedTotalitySentence_eval]
  intro q _
  refine ⟨UniformTrace.specialize (oldTauTemplateIndex : M) q,?_⟩
  rw [eventualGraph_normalizeIndex_eval]
  exact ⟨CodedObjectMembership.memberFormula_omega_eval q,
    (adapter_program_graph q _).mpr rfl,CodedObjectMembership.memberFormula_omega_eval _⟩

/-- This is the source-category bridge, not an equality of the two
Turing maps and not a standard-model extensionality argument. -/
theorem adapter_factorization :
    CategoryTheory.PCategoryStruct.nearProd_map adapter (𝟙 (omegaObject 𝗣𝗔)) ≫ sourceTau = typedTau 𝗣𝗔 := by
  apply CodedHom.ext
  apply SyntacticPredicates.programClass_ext 𝗣𝗔
  intro M _ _ input y
  obtain ⟨q,x,he⟩ : ∃ q x : M, input = pair q x :=
    ⟨π₁ input,π₂ input,(pair_unpair input).symm⟩
  subst input
  rw [comp_val,SyntacticModel.programRelation_mul,typedTau_val,
    SyntacticModel.programRelation_class]
  change (∃ z : M,
    SyntacticModel.programRelation 𝗣𝗔 M
      (tensorClass 𝗣𝗔 adapter.val (𝟙 (omegaObject 𝗣𝗔) : omegaObject 𝗣𝗔 ⟶ _).val)
      (pair q x) z ∧ SyntacticModel.programRelation 𝗣𝗔 M sourceTau.val z y) ↔ _
  constructor
  · rintro ⟨z,hz,hy⟩
    obtain ⟨a,b,hzCode⟩ : ∃ a b : M, z = pair a b :=
      ⟨π₁ z,π₂ z,(pair_unpair z).symm⟩
    subst z
    obtain ⟨ha,hb⟩ := (PrintedObjectCoding.tensor_relation 𝗣𝗔 M _ _ q x a b).mp hz
    have ha' := (adapter_relation q a).mp ha
    rw [id_val] at hb
    have hb' := (SyntacticModel.object_relation 𝗣𝗔 M .omega x b).mp hb
    have hb'' := hb'.2
    subst a
    subst b
    exact (adapter_application q x y).mp ((sourceTau_relation M _ _ _).mp hy)
  · intro hy
    refine ⟨pair (UniformTrace.specialize (oldTauTemplateIndex : M) q) x,?_,?_⟩
    · apply (PrintedObjectCoding.tensor_relation 𝗣𝗔 M _ _ _ _ _ _).mpr
      constructor
      · exact (adapter_relation q _).mpr rfl
      · rw [id_val]
        exact (SyntacticModel.object_relation 𝗣𝗔 M .omega x x).mpr
          ⟨CodedObjectMembership.memberFormula_omega_eval x,rfl⟩
    · apply (sourceTau_relation M _ _ _).mpr
      exact (adapter_application q x y).mpr hy

/-- The literal printed universal map satisfies the actual categorical
Turing property, transferred along the constructed total adapter. -/
theorem sourceTau_isTuring : RecursionCategory.IsTuringMorphism sourceTau := by
  intro V phi
  obtain ⟨g,hg,he⟩ := typedTau_isTuringMorphism 𝗣𝗔 V phi
  refine ⟨g ≫ adapter,isTotal_comp hg adapter_total,?_⟩
  have hp := PCategory.nearProd_comp g adapter
    (𝟙 (omegaObject 𝗣𝗔)) (𝟙 (omegaObject 𝗣𝗔))
  rw [Category.id_comp] at hp
  rw [← hp,Category.assoc,adapter_factorization]
  exact he

theorem source_pair_inseparable : Inseparable a0 a1 :=
  SyntacticModel.syntactic_pair_inseparable_v46_of_model 𝗣𝗔 ℕ sourceTau sourceTau_isTuring
    (TypedRecursionCategory.omegaCoprodIso 𝗣𝗔).symm

end CategoricalEssentialIncompleteness.V46.ArithmeticDiagonalCodes
