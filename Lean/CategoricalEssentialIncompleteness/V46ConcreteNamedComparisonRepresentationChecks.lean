/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ConcreteNamedComparisonRepresentation

/-! # Forward chart eliminators have the actual chosen categorical points -/

@[expose] public section
noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticLists
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax
open CategoricalEssentialIncompleteness.V46.ConcreteNamedComparison
variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
variable (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
example (X Y : PredicateCategory T) (a b : SyntaxPolynomial (PredicateCategory T))
    (u : M) (z : Obj T M ((a.product b).eval.obj (X,Y)))
    (hz : (baseRepresentation T X Y (.product a b)).val.Evalb ![u,z.val]) :
    ∃ v w : M, u = Arithmetic.pair v w ∧
      (baseRepresentation T X Y a).val.Evalb
        ![v,((F T M).map (prod.fst : a.eval.obj (X,Y) ⨯ b.eval.obj (X,Y) ⟶ _) z).val] ∧
      (baseRepresentation T X Y b).val.Evalb
        ![w,((F T M).map (prod.snd : a.eval.obj (X,Y) ⨯ b.eval.obj (X,Y) ⟶ _) z).val] :=
  representation_product_points T M X Y a b u z hz
