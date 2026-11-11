/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SyntacticSyntaxParameter

/-! # Checks for the actual polynomial parameter comparison -/

@[expose] public section

noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticLists
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax

variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
variable (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

example (P C D : PredicateCategory T) (a : SyntaxPolynomial (PredicateCategory T))
    (p : Obj T M P) (u : M)
    (z : Obj T M ((a.withParameters P).eval.obj
      (constantFamily P C, constantFamily P D)).left)
    (h : (constantRepresentation T P C D a).val.Evalb ![p.val, u, z.val]) :
    (baseRepresentation T C D a).val.Evalb
      ![u, ((F T M).map (parameterValueMap T P C D a) z).val] :=
  parameterValueMap_representation T M P C D a p u z h

example (P C D : PredicateCategory T) (a : SyntaxPolynomial (PredicateCategory T))
    (p : Obj T M P) (u : M) (h : (rawCarrier C D a).val.Evalb ![u]) :
    ∃ z : Obj T M ((a.withParameters P).eval.obj
      (constantFamily P C, constantFamily P D)).left,
      (constantRepresentation T P C D a).val.Evalb ![p.val, u, z.val] ∧
        (F T M).map ((a.withParameters P).eval.obj
          (constantFamily P C, constantFamily P D)).hom z = p :=
  constantRepresentation_exists T M P C D a p u h
