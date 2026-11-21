/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ArithmeticLiteralCoordinates


/-! # The sentence chart in the canonical split-domain interpretation -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
namespace CategoricalEssentialIncompleteness.V46.ArithmeticLiteralCoordinates.Checks
open ArithmeticLiteralModel NamedArithmeticSignature

example (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] (Γ : Carrier)
    (s : PredicateInterpretation.CanonicalDomain 𝗣𝗔 M
      ((realization 𝗣𝗔).obj sentencePredicate)) :
    (SyntacticGeneratedAxioms.literalTheoremCarrier 𝗣𝗔 variableSymbols functionSymbols
      relationSymbols bound Γ).val.Evalb ![s.val.val] ↔
      ∃ p : PredicateInterpretation.CanonicalDomain 𝗣𝗔 M
        ((realization 𝗣𝗔).obj (proofObject Γ)),
        (PredicateInterpretation.canonicalDomainFunctor 𝗣𝗔 M).map
          ((realization 𝗣𝗔).map (conclusion Γ)) p = s :=
  theorem_iff_image M Γ s

example (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] (Γ : Carrier)
    (s : PredicateInterpretation.CanonicalDomain 𝗣𝗔 M
      ((realization 𝗣𝗔).obj sentencePredicate)) :
    s ∈ LocalConnectedness.PartialFunctions.support (theory M Γ) ↔
      (SyntacticGeneratedAxioms.literalTheoremCarrier 𝗣𝗔 variableSymbols functionSymbols
        relationSymbols bound Γ).val.Evalb ![s.val.val] := theory_support M Γ s

end CategoricalEssentialIncompleteness.V46.ArithmeticLiteralCoordinates.Checks
