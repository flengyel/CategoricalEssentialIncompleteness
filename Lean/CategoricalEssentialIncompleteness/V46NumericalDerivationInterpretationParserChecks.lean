/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NumericalDerivationInterpretationParser


/-! # Literal parser comparison under coefficient relabeling -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.V46
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax.Coding
namespace CategoricalEssentialIncompleteness.V46.NumericalDerivationInterpretation.Parser
variable (f : Carrier → Carrier) (a b : RawPolynomial)
example : Postfix.stepGraph (a.mapCoefficients f) (b.mapCoefficients f) = Postfix.stepGraph a b := stepGraph_map f a b
example : Postfix.blueprint (a.mapCoefficients f) (b.mapCoefficients f) = Postfix.blueprint a b := blueprint_map f a b
example : Postfix.prefixGraph (a.mapCoefficients f) (b.mapCoefficients f) = Postfix.prefixGraph a b := prefixGraph_map f a b
example : Postfix.runGraph (a.mapCoefficients f) (b.mapCoefficients f) = Postfix.runGraph a b := runGraph_map f a b
variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
example (p : RawPolynomial) (formula : Bool) (u : M) :
    constructor formula (p.mapCoefficients f) u = constructor formula p u := constructor_map f p formula u
example (word n initial : M) :
    Postfix.runPrefix (a.mapCoefficients f) (b.mapCoefficients f) word n initial =
      Postfix.runPrefix a b word n initial := runPrefix_map f a b word n initial
example (word initial : M) :
    Postfix.run (a.mapCoefficients f) (b.mapCoefficients f) word initial =
      Postfix.run a b word initial := run_map f a b word initial
variable (h : ∀ C : Carrier, ∀ u : M, (f C).val.Evalb ![u] ↔ C.val.Evalb ![u])
example (formula : Bool) (word : M) :
    (Postfix.plainCarrier formula (a.mapCoefficients f) (b.mapCoefficients f)).val.Evalb ![word] ↔
      (Postfix.plainCarrier formula a b).val.Evalb ![word] := plainCarrier_map_iff f h formula a b word
example (formula : Bool) (word : M) :
    (Postfix.carrier formula a b).val.Evalb ![word] ↔
      (Postfix.plainCarrier formula (a.mapCoefficients f) (b.mapCoefficients f)).val.Evalb ![word] :=
  storedCarrier_map_plain f h formula a b word
end CategoricalEssentialIncompleteness.V46.NumericalDerivationInterpretation.Parser
