/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ArithmeticIndexedProvabilityModels
public import CategoricalEssentialIncompleteness.V46UniformTrace

/-! # The indexed conclusion program and its arithmetic image presentation -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w t
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.Limits CategoryTheory.RestrictionCategory
open FailureOfComposition FailureOfComposition.ProofSearch FailureOfComposition.ConcreteEvaluator
open FailureOfComposition.CodedObjectMembership
open CategoricalEssentialIncompleteness.LocalConnectedness
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
namespace CategoricalEssentialIncompleteness.V46.ArithmeticIndexedProvability

private theorem inverse_conclusion {D : Type u} {C : Type v}
    [Category.{w} D] [Category.{t} C] (E : D ≌ C)
    {P : C} {X : D} (f : P ⟶ E.functor.obj X) :
    E.functor.map (E.inverse.map f ≫ E.unitIso.inv.app X) =
      E.counitIso.hom.app P ≫ f := by
  rw [E.functor.map_comp,← E.counit_app_functor X]
  exact E.counit_naturality f

/-- The presentation isomorphism is the counit of the fixed equivalence. -/
def proofPresentationIso (AxPA : Carrier) :
    (realization 𝗣𝗔).obj (proofCarrier AxPA) ≅ ArithmeticIndexedFamily.sentenceProof AxPA :=
  (predicateEquivalence 𝗣𝗔).counitIso.app (ArithmeticIndexedFamily.sentenceProof AxPA)

/-- The predicate morphism is exactly the conclusion in the source and product charts. -/
theorem rawConclusion_realization (AxPA : Carrier) :
    (realization 𝗣𝗔).map (rawConclusion AxPA) =
      (proofPresentationIso AxPA).hom ≫ ArithmeticIndexedFamily.sentenceConclusion AxPA ≫
        ArithmeticIndexedAxioms.productIso.inv :=
  inverse_conclusion (predicateEquivalence 𝗣𝗔)
    (ArithmeticIndexedFamily.sentenceConclusion AxPA ≫ ArithmeticIndexedAxioms.productIso.inv)

/-- The standard index is selected once from the actual family graph. -/
def conclusionIndex (AxPA : Carrier) : ℕ :=
  SyntacticSearch.searchIndex (chosenGraph 𝗣𝗔 (rawConclusion AxPA)).graph

def programProvability (AxPA : Carrier) : 𝚺₁.Semisentence 2 :=
  let G := UniformTrace.graph
  .mkSigma “e z. ∃ p w, !natPairFormula.val w e z ∧ !G.val !!(conclusionIndex AxPA) p w”

private theorem represented_search_graph {C D : Carrier} (f : GraphMorphism 𝗣𝗔 C D)
    (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] (x y : M) :
    UniformTrace.graph.val.Evalb ![(SyntacticSearch.searchIndex f.graph : M),x,y] ↔
      f.graph.val.Evalb ![x,y] := by
  have hs := canonicalPartrecGraphFormula_eval_iff_eventualGraph
    (M := M) (SyntacticSearch.searchIndex f.graph) x y
  simp only [numeral_eq_natCast_app] at hs
  exact hs.trans (SyntacticModel.uniform_model 𝗣𝗔 M
    (SyntacticSearch.search_uniform_of_functional 𝗣𝗔 f.graph f.functional) x y)

section Models
variable (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

theorem conclusionIndex_graph (AxPA : Carrier) (p w : M) :
    UniformTrace.graph.val.Evalb ![(conclusionIndex AxPA : M),p,w] ↔
      (chosenGraph 𝗣𝗔 (rawConclusion AxPA)).graph.val.Evalb ![p,w] :=
  represented_search_graph (chosenGraph 𝗣𝗔 (rawConclusion AxPA)) M p w

theorem conclusionIndex_domain (AxPA : Carrier) (p : M) :
    (∃ w : M, UniformTrace.graph.val.Evalb ![(conclusionIndex AxPA : M),p,w]) ↔
      (proofCarrier AxPA).val.Evalb ![p] := by
  refine (exists_congr (fun w => conclusionIndex_graph M AxPA p w)).trans ?_
  constructor
  · rintro ⟨w,hw⟩
    exact ((chosenGraph 𝗣𝗔 (rawConclusion AxPA)).support_model M p w hw).1
  · intro hp
    obtain ⟨w,hw,_⟩ := (chosenGraph 𝗣𝗔 (rawConclusion AxPA)).total_model M p hp
    exact ⟨w,hw⟩

theorem programProvability_eval (AxPA : Carrier) (e z : M) :
    (programProvability AxPA).val.Evalb ![e,z] ↔ (provability AxPA).val.Evalb ![e,z] := by
  rw [provability_image M AxPA e z]
  simp [programProvability,imageCarrier,numeral_eq_natCast_app,conclusionIndex_graph]

end Models

def conclusionIndexGraphSentence (AxPA : Carrier) : ArithmeticSentence :=
  let G := UniformTrace.graph
  let C := (chosenGraph 𝗣𝗔 (rawConclusion AxPA)).graph
  “∀ p w, !G.val !!(conclusionIndex AxPA) p w ↔ !C.val p w”

def conclusionIndexDomainSentence (AxPA : Carrier) : ArithmeticSentence :=
  let G := UniformTrace.graph
  let P := proofCarrier AxPA
  “∀ p, (∃ w, !G.val !!(conclusionIndex AxPA) p w) ↔ !P.val p”

def programProvabilityComparisonSentence (AxPA : Carrier) : ArithmeticSentence :=
  let R := programProvability AxPA
  let P := provability AxPA
  “∀ e z, !R.val e z ↔ !P.val e z”

theorem conclusionIndex_graph_PA (AxPA : Carrier) : 𝗣𝗔 ⊢ conclusionIndexGraphSentence AxPA := by
  apply complete.{0} 𝗣𝗔
  intro M _ _
  simpa [models_iff,conclusionIndexGraphSentence,numeral_eq_natCast_app] using conclusionIndex_graph M AxPA

theorem conclusionIndex_domain_PA (AxPA : Carrier) : 𝗣𝗔 ⊢ conclusionIndexDomainSentence AxPA := by
  apply complete.{0} 𝗣𝗔
  intro M _ _
  simpa [models_iff,conclusionIndexDomainSentence,numeral_eq_natCast_app] using
    conclusionIndex_domain M AxPA

theorem programProvability_comparison_PA (AxPA : Carrier) :
    𝗣𝗔 ⊢ programProvabilityComparisonSentence AxPA := by
  apply complete.{0} 𝗣𝗔
  intro M _ _
  simpa [models_iff,programProvabilityComparisonSentence] using programProvability_eval M AxPA

/-- The range of any total conclusion is its actual regular image,
with the constructed partial inverse of its image inclusion. -/
theorem total_range_regular_image (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    {P Q : TotalSplit T} (c : P ⟶ Q) :
    ∃ r : Q.obj ⟶ (image c).obj,
      (image.ι c).hom ≫ r = 𝟙 _ ∧ r ≫ (image.ι c).hom = rst r ∧
      (Ranges.range c.hom).hom = r ≫ (image.ι c).hom := by
  obtain ⟨r,hmr,hrm⟩ := totalSplit_mono_partial_inverse T (image.ι c)
  refine ⟨r,hmr,hrm,?_⟩
  have h := LocalConnectedness.V46.range_regularImage (factorThruImage c) (image.ι c) r hmr hrm
  have hfac : (factorThruImage c).hom ≫ (image.ι c).hom = c.hom :=
    congrArg (fun f : P ⟶ Q => f.hom) (image.fac c)
  simpa only [hfac] using h

/-- The indexed conclusion range splits through its actual image inclusion. -/
theorem sentence_range_regular_image (AxPA : Carrier) :
    ∃ r : (ArithmeticIndexedFamily.parameter ⨯ ArithmeticIndexedFamily.sentence).obj ⟶
        (image (ArithmeticIndexedFamily.sentenceConclusion AxPA)).obj,
      (image.ι (ArithmeticIndexedFamily.sentenceConclusion AxPA)).hom ≫ r = 𝟙 _ ∧
      r ≫ (image.ι (ArithmeticIndexedFamily.sentenceConclusion AxPA)).hom = rst r ∧
      (Ranges.range (ArithmeticIndexedFamily.sentenceConclusion AxPA).hom).hom =
        r ≫ (image.ι (ArithmeticIndexedFamily.sentenceConclusion AxPA)).hom :=
  total_range_regular_image 𝗣𝗔 (ArithmeticIndexedFamily.sentenceConclusion AxPA)

end CategoricalEssentialIncompleteness.V46.ArithmeticIndexedProvability
