/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SyntacticSyntaxDecomposition


/-! # Root decomposition of accepted postfix words -/

@[expose] public section
noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax.Coding
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax.Postfix

namespace CategoricalEssentialIncompleteness.V46.SyntacticSyntax.DecompositionChecks
variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

example (formula : Bool) (a b : RawPolynomial) (word : M)
    (hw : (carrier formula a b).val.Evalb ![word]) :
    ∃ u : M, (rawCarrier (carrier false a b) (carrier true a b)
      (if formula then b else a)).val.Evalb ![u] ∧
      word = constructor formula (if formula then b else a) u :=
  carrier_decomposition formula a b word hw

example (formula : Bool) (a b q : RawPolynomial) (u v : M)
    (hu : (rawCarrier (carrier false a b) (carrier true a b) q).val.Evalb ![u])
    (hv : (rawCarrier (carrier false a b) (carrier true a b) q).val.Evalb ![v])
    (he : constructor formula q u = constructor formula q v) : u = v :=
  constructor_injective formula a b q u v hu hv he
end CategoricalEssentialIncompleteness.V46.SyntacticSyntax.DecompositionChecks
