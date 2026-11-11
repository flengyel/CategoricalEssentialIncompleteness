/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ArithmeticIndexedAxiomsExponential


/-! # Statement checks in `V46ArithmeticIndexedAxiomsExponentialChecks` -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
namespace CategoricalEssentialIncompleteness.V46.ArithmeticIndexedAxioms.Exponential.Checks
open NamedArithmeticSignature

example (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] (AxPA : Carrier) (e z : M) :
    (printedCarrier AxPA).val.Evalb ![ExponentialPairing.code e z] ↔
      ArithmeticIndexedAxioms.sentencePredicate.val.Evalb ![z] ∧
        (AxPA.val.Evalb ![z] ∨ ∃ y : M, UniformTrace.graph.val.Evalb ![e,z,y]) :=
  (printedCarrier_code M AxPA e z).trans (ArithmeticIndexedAxioms.axiomGraph_eval M AxPA e z)

example (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] (AxPA : Carrier) (e : ℕ) (z : M) :
    (printedCarrier AxPA).val.Evalb ![ExponentialPairing.code (e : M) z] ↔
      (ArithmeticIndexedAxioms.fiberAxioms AxPA e).val.Evalb ![z] :=
  printedCarrier_numeral M AxPA e z

example (AxPA : Carrier) : CategoryTheory.Iso (C := PredicateCategory 𝗣𝗔)
    (ArithmeticIndexedAxioms.carrier AxPA) (printedCarrier AxPA) := carrierIso AxPA

example (AxPA : Carrier) :
    (carrierIso AxPA).hom ≫ printedInclusion AxPA =
      ArithmeticIndexedAxioms.predicateInclusion AxPA ≫
        (ExponentialProducts.rawProductIso 𝗣𝗔 variableSymbols ArithmeticIndexedAxioms.sentencePredicate).hom :=
  mono_square AxPA

example (AxPA : Carrier) :
    (realization 𝗣𝗔).map (carrierIso AxPA).hom ≫
      ((realization 𝗣𝗔).map (printedInclusion AxPA) ≫ ArithmeticIndexedProvability.printedProductIso.hom) =
        ArithmeticIndexedAxioms.axioms AxPA := realized_square AxPA

example (AxPA : Carrier) : Mono (printedInclusion AxPA) := inferInstance
example (AxPA : Carrier) : Mono (printedAxioms AxPA) := inferInstance

end CategoricalEssentialIncompleteness.V46.ArithmeticIndexedAxioms.Exponential.Checks
