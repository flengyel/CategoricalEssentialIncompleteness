/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ArithmeticIndexedProvabilityPresentation


/-! # Statement checks in `V46ArithmeticIndexedProvabilityPresentationChecks` -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.Limits CategoryTheory.RestrictionCategory
open CategoricalEssentialIncompleteness.LocalConnectedness
namespace CategoricalEssentialIncompleteness.V46.ArithmeticIndexedProvability.Checks
open SyntacticPredicates
example (AxPA : Carrier) : 𝗣𝗔 ⊢ conclusionIndexGraphSentence AxPA := conclusionIndex_graph_PA AxPA
example (AxPA : Carrier) : 𝗣𝗔 ⊢ conclusionIndexDomainSentence AxPA := conclusionIndex_domain_PA AxPA
example (AxPA : Carrier) : 𝗣𝗔 ⊢ programProvabilityComparisonSentence AxPA :=
  programProvability_comparison_PA AxPA
example (AxPA : Carrier) :
    (realization 𝗣𝗔).map (rawConclusion AxPA) =
      (proofPresentationIso AxPA).hom ≫ ArithmeticIndexedFamily.sentenceConclusion AxPA ≫
        ArithmeticIndexedAxioms.productIso.inv := rawConclusion_realization AxPA
example (AxPA : Carrier) :
    𝗣𝗔 ⊢ (let G := UniformTrace.graph
      let C := (chosenGraph 𝗣𝗔 (rawConclusion AxPA)).graph
      “∀ p w, !G.val !!(conclusionIndex AxPA) p w ↔ !C.val p w”) := conclusionIndex_graph_PA AxPA
example (AxPA : Carrier) :
    ∃ r : (ArithmeticIndexedFamily.parameter ⨯ ArithmeticIndexedFamily.sentence).obj ⟶
        (image (ArithmeticIndexedFamily.sentenceConclusion AxPA)).obj,
      (image.ι (ArithmeticIndexedFamily.sentenceConclusion AxPA)).hom ≫ r = 𝟙 _ ∧
      r ≫ (image.ι (ArithmeticIndexedFamily.sentenceConclusion AxPA)).hom = rst r ∧
      (Ranges.range (ArithmeticIndexedFamily.sentenceConclusion AxPA).hom).hom =
        r ≫ (image.ι (ArithmeticIndexedFamily.sentenceConclusion AxPA)).hom :=
  sentence_range_regular_image AxPA
end CategoricalEssentialIncompleteness.V46.ArithmeticIndexedProvability.Checks
