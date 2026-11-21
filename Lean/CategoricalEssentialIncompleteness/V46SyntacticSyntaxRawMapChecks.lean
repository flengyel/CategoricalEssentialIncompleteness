/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SyntacticSyntaxRawMap

/-! # Checks for the polynomial rawmap comparison -/

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

example (P C D : PredicateCategory T) (A B : Over P)
    (f : constantFamily P C ⟶ A) (g : constantFamily P D ⟶ B)
    (a : SyntaxPolynomial (PredicateCategory T)) (p : Obj T M P) (u : M)
    (h : (rawCarrier C D a).val.Evalb ![u]) :
    ∃ v : M, (mapRaw P (rawArrow T f) (rawArrow T g) a).val.Evalb ![p.val, u, v] :=
  mapRaw_arrow_exists T M f g a p u h
