/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ArithmeticIndexedAxioms

/-! # Indexed axiom predicate, product chart and numeral fibers -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates

namespace CategoricalEssentialIncompleteness.V46.ArithmeticIndexedAxiomsChecks
open ArithmeticIndexedAxioms

example (AxPA : Carrier) (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] (e z : M) :
    (axiomGraph AxPA).val.Evalb ![e,z] ↔
      NamedArithmeticLiteralTotal.literalPredicate.val.Evalb ![z] ∧
        (AxPA.val.Evalb ![z] ∨ ∃ y : M, UniformTrace.graph.val.Evalb ![e,z,y]) :=
  axiomGraph_eval M AxPA e z

example (AxPA : Carrier) (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] (e : ℕ) (z : M) :
    (carrier AxPA).val.Evalb ![⟪(e : M),z⟫] ↔ (fiberAxioms AxPA e).val.Evalb ![z] :=
  carrier_numeral M AxPA e z

example : (realization 𝗣𝗔).obj
      (productCarrier NamedArithmeticSignature.variableSymbols NamedArithmeticLiteralTotal.literalPredicate) ≅
    ArithmeticOmegaComparison.identityOmega 𝗣𝗔 ⨯ NamedArithmeticLiteralTotal.literalSentence :=
  productIso

example (AxPA : Carrier) : Mono (axioms AxPA) := inferInstance

end CategoricalEssentialIncompleteness.V46.ArithmeticIndexedAxiomsChecks
