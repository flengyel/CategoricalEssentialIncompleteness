/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SyntacticSyntaxParserLaws


/-! # Postfix constructors are accepted and preserve every stack frame -/

@[expose] public section
noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax.Coding
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax.Postfix

namespace CategoricalEssentialIncompleteness.V46.SyntacticSyntax.ParserLawsChecks
variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

example (a b : RawPolynomial) (word stack out tail : M)
    (h : run a b word (stack + 1) = out + 1) :
    run a b word (Words.append stack tail + 1) = Words.append out tail + 1 :=
  run_frame a b word stack out tail h

example (a b : RawPolynomial) (u : M)
    (h : (rawCarrier (carrier false a b) (carrier true a b) a).val.Evalb ![u]) :
    (carrier false a b).val.Evalb ![constructor false a u] := term_constructor_carrier a b u h

example (a b : RawPolynomial) (u : M)
    (h : (rawCarrier (carrier false a b) (carrier true a b) b).val.Evalb ![u]) :
    (carrier true a b).val.Evalb ![constructor true b u] := formula_constructor_carrier a b u h
end CategoricalEssentialIncompleteness.V46.SyntacticSyntax.ParserLawsChecks
