/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ArithmeticIndexedProvabilityPresentation
public import CategoricalEssentialIncompleteness.V46ExponentialProducts

/-! # The indexed conclusion in the exponential product chart -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.Limits
open FailureOfComposition FailureOfComposition.ProofSearch FailureOfComposition.ConcreteEvaluator
open FailureOfComposition.CodedObjectMembership
open CategoricalEssentialIncompleteness.LocalConnectedness
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates

namespace CategoricalEssentialIncompleteness.V46.ArithmeticIndexedProvability
open NamedArithmeticSignature

private theorem represented_composition (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    {A B C : PredicateCategory T} (f : GraphMorphism T A B) (g : GraphMorphism T B C) :
    representedArrow T (f.composition g) = representedArrow T f ≫ representedArrow T g := rfl

def printedProductPredicate : PredicateCategory 𝗣𝗔 :=
  ExponentialProducts.carrier variableSymbols ArithmeticIndexedAxioms.sentencePredicate

def printedRepresentation (AxPA : Carrier) :
    GraphMorphism 𝗣𝗔 (proofCarrier AxPA) printedProductPredicate :=
  (chosenGraph 𝗣𝗔 (rawConclusion AxPA)).composition
    (ExponentialProducts.encode 𝗣𝗔 variableSymbols ArithmeticIndexedAxioms.sentencePredicate)

def printedConclusion (AxPA : Carrier) :
    @Quiver.Hom (PredicateCategory 𝗣𝗔) inferInstance (proofCarrier AxPA) printedProductPredicate :=
  representedArrow 𝗣𝗔 (printedRepresentation AxPA)

/-- This is a source-category equality through the proved code isomorphism. -/
theorem printedConclusion_eq (AxPA : Carrier) :
    printedConclusion AxPA = rawConclusion AxPA ≫
      (ExponentialProducts.rawProductIso 𝗣𝗔 variableSymbols ArithmeticIndexedAxioms.sentencePredicate).hom := by
  exact (represented_composition 𝗣𝗔 (chosenGraph 𝗣𝗔 (rawConclusion AxPA))
    (ExponentialProducts.encode 𝗣𝗔 variableSymbols ArithmeticIndexedAxioms.sentencePredicate)).trans
    (congrArg (fun f : @Quiver.Hom (PredicateCategory 𝗣𝗔) inferInstance
      (proofCarrier AxPA) ArithmeticIndexedAxioms.productPredicate =>
        f ≫ (ExponentialProducts.rawProductIso 𝗣𝗔 variableSymbols
          ArithmeticIndexedAxioms.sentencePredicate).hom)
      (chosenGraph_class 𝗣𝗔 (rawConclusion AxPA)))

/-- The product chart has the exponential code on its predicate side. -/
def printedProductIso :
    (realization 𝗣𝗔).obj printedProductPredicate ≅
      ArithmeticIndexedAxioms.parameter ⨯ ArithmeticIndexedAxioms.sentence :=
  ((realization 𝗣𝗔).mapIso (ExponentialProducts.rawProductIso 𝗣𝗔
    variableSymbols ArithmeticIndexedAxioms.sentencePredicate)).symm ≪≫
      ArithmeticIndexedAxioms.productIso

theorem printedConclusion_realization (AxPA : Carrier) :
    (realization 𝗣𝗔).map (printedConclusion AxPA) =
      (proofPresentationIso AxPA).hom ≫ ArithmeticIndexedFamily.sentenceConclusion AxPA ≫
        printedProductIso.inv := by
  calc
    _ = (realization 𝗣𝗔).map (rawConclusion AxPA ≫
        (ExponentialProducts.rawProductIso 𝗣𝗔 variableSymbols
          ArithmeticIndexedAxioms.sentencePredicate).hom) :=
      congrArg (fun f => (realization 𝗣𝗔).map f) (printedConclusion_eq AxPA)
    _ = (realization 𝗣𝗔).map (rawConclusion AxPA) ≫
        (realization 𝗣𝗔).map (ExponentialProducts.rawProductIso 𝗣𝗔 variableSymbols
          ArithmeticIndexedAxioms.sentencePredicate).hom := (realization 𝗣𝗔).map_comp _ _
    _ = ((proofPresentationIso AxPA).hom ≫ ArithmeticIndexedFamily.sentenceConclusion AxPA ≫
        ArithmeticIndexedAxioms.productIso.inv) ≫
        (realization 𝗣𝗔).map (ExponentialProducts.rawProductIso 𝗣𝗔 variableSymbols
          ArithmeticIndexedAxioms.sentencePredicate).hom :=
      congrArg (fun f => f ≫ (realization 𝗣𝗔).map
        (ExponentialProducts.rawProductIso 𝗣𝗔 variableSymbols ArithmeticIndexedAxioms.sentencePredicate).hom)
        (rawConclusion_realization AxPA)
    _ = _ := by
      simp only [printedProductIso,Iso.trans_inv,Iso.symm_inv,Functor.mapIso_hom,Category.assoc]

/-- A single index is selected from the represented conclusion graph. -/
def printedConclusionIndex (AxPA : Carrier) : ℕ :=
  SyntacticSearch.searchIndex (printedRepresentation AxPA).graph

def printedProvability (AxPA : Carrier) : 𝚺₁.Semisentence 2 :=
  let E := ExponentialPairing.graph
  let G := UniformTrace.graph
  .mkSigma “e z. ∃ p w, !E.val w e z ∧ !G.val !!(printedConclusionIndex AxPA) p w”

private theorem represented_index_graph {A B : Carrier} (f : GraphMorphism 𝗣𝗔 A B)
    (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] (p w : M) :
    UniformTrace.graph.val.Evalb ![(SyntacticSearch.searchIndex f.graph : M),p,w] ↔
      f.graph.val.Evalb ![p,w] := by
  have hs := canonicalPartrecGraphFormula_eval_iff_eventualGraph
    (M := M) (SyntacticSearch.searchIndex f.graph) p w
  simp only [numeral_eq_natCast_app] at hs
  exact hs.trans (SyntacticModel.uniform_model 𝗣𝗔 M
    (SyntacticSearch.search_uniform_of_functional 𝗣𝗔 f.graph f.functional) p w)

section Models
variable (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝚺 1 := models_of_subtheory (U := 𝗣𝗔) inferInstance
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := models_of_subtheory (U := 𝗜𝚺 1) inferInstance

private theorem encoded_image {A C D : Carrier}
    (f : GraphMorphism 𝗣𝗔 A (productCarrier C D)) (e z : M) :
    (imageCarrier (f.composition (ExponentialProducts.encode 𝗣𝗔 C D)).graph).val.Evalb
      ![ExponentialPairing.code e z] ↔
      (imageCarrier f.graph).val.Evalb ![Arithmetic.pair e z] := by
  rw [imageCarrier_eval,imageCarrier_eval]
  constructor
  · rintro ⟨p,hp⟩
    obtain ⟨v,hf,hencode⟩ := (comp_eval (ExponentialProducts.encode 𝗣𝗔 C D).graph f.graph
      ![p,ExponentialPairing.code e z]).mp hp
    obtain ⟨a,b,rfl,_,_,he⟩ := (ExponentialProducts.encodeGraph_eval C D v
      (ExponentialPairing.code e z)).mp hencode
    obtain ⟨rfl,rfl⟩ := ExponentialPairing.code_injective he
    exact ⟨p,hf⟩
  · rintro ⟨p,hp⟩
    have hsupport := (f.support_model M p (Arithmetic.pair e z) hp).2
    obtain ⟨a,b,he,ha,hb⟩ := (productCarrier_eval C D (Arithmetic.pair e z)).mp hsupport
    obtain ⟨rfl,rfl⟩ := (pair_eq_pair_iff _ _ _ _).mp he
    refine ⟨p,?_⟩
    exact (comp_eval (ExponentialProducts.encode 𝗣𝗔 C D).graph f.graph
      ![p,ExponentialPairing.code e z]).mpr
        ⟨Arithmetic.pair e z,hp,(ExponentialProducts.encodeGraph_pair C D e z _).mpr ⟨ha,hb,rfl⟩⟩

theorem printedConclusionIndex_graph (AxPA : Carrier) (p w : M) :
    UniformTrace.graph.val.Evalb ![(printedConclusionIndex AxPA : M),p,w] ↔
      (printedRepresentation AxPA).graph.val.Evalb ![p,w] :=
  represented_index_graph (printedRepresentation AxPA) M p w

theorem printedConclusionIndex_domain (AxPA : Carrier) (p : M) :
    (∃ w : M, UniformTrace.graph.val.Evalb ![(printedConclusionIndex AxPA : M),p,w]) ↔
      (proofCarrier AxPA).val.Evalb ![p] := by
  refine (exists_congr (fun w => printedConclusionIndex_graph M AxPA p w)).trans ?_
  constructor
  · rintro ⟨w,hw⟩
    exact ((printedRepresentation AxPA).support_model M p w hw).1
  · intro hp
    obtain ⟨w,hw,_⟩ := (printedRepresentation AxPA).total_model M p hp
    exact ⟨w,hw⟩

theorem printedProvability_code (AxPA : Carrier) (e z : M) :
    (printedProvability AxPA).val.Evalb ![e,z] ↔
      ∃ p : M, UniformTrace.graph.val.Evalb
        ![(printedConclusionIndex AxPA : M),p,ExponentialPairing.code e z] := by
  simp [printedProvability,numeral_eq_natCast_app]

theorem printedProvability_eval (AxPA : Carrier) (e z : M) :
    (printedProvability AxPA).val.Evalb ![e,z] ↔ (provability AxPA).val.Evalb ![e,z] := by
  have hp : (printedProvability AxPA).val.Evalb ![e,z] ↔
      (imageCarrier (printedRepresentation AxPA).graph).val.Evalb ![ExponentialPairing.code e z] := by
    simp [printedProvability,imageCarrier,numeral_eq_natCast_app,printedConclusionIndex_graph]
  exact hp.trans ((encoded_image M (chosenGraph 𝗣𝗔 (rawConclusion AxPA)) e z).trans
    (provability_image M AxPA e z).symm)

end Models

def printedConclusionIndexGraphSentence (AxPA : Carrier) : ArithmeticSentence :=
  let G := UniformTrace.graph
  let C := (printedRepresentation AxPA).graph
  “∀ p w, !G.val !!(printedConclusionIndex AxPA) p w ↔ !C.val p w”

def printedConclusionIndexDomainSentence (AxPA : Carrier) : ArithmeticSentence :=
  let G := UniformTrace.graph
  let P := proofCarrier AxPA
  “∀ p, (∃ w, !G.val !!(printedConclusionIndex AxPA) p w) ↔ !P.val p”

def printedProvabilityComparisonSentence (AxPA : Carrier) : ArithmeticSentence :=
  let R := printedProvability AxPA
  let P := provability AxPA
  “∀ e z, !R.val e z ↔ !P.val e z”

theorem printedConclusionIndex_graph_PA (AxPA : Carrier) :
    𝗣𝗔 ⊢ printedConclusionIndexGraphSentence AxPA := by
  apply complete.{0} 𝗣𝗔
  intro M _ _
  simpa [models_iff,printedConclusionIndexGraphSentence,numeral_eq_natCast_app] using
    printedConclusionIndex_graph M AxPA

theorem printedConclusionIndex_domain_PA (AxPA : Carrier) :
    𝗣𝗔 ⊢ printedConclusionIndexDomainSentence AxPA := by
  apply complete.{0} 𝗣𝗔
  intro M _ _
  simpa [models_iff,printedConclusionIndexDomainSentence,numeral_eq_natCast_app] using
    printedConclusionIndex_domain M AxPA

theorem printedProvability_comparison_PA (AxPA : Carrier) :
    𝗣𝗔 ⊢ printedProvabilityComparisonSentence AxPA := by
  apply complete.{0} 𝗣𝗔
  intro M _ _
  simpa [models_iff,printedProvabilityComparisonSentence] using printedProvability_eval M AxPA

end CategoricalEssentialIncompleteness.V46.ArithmeticIndexedProvability
