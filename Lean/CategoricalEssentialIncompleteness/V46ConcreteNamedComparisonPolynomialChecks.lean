/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ConcreteNamedComparisonPolynomial

/-! # Forward chart comparison without a polynomial encoder inverse -/

@[expose] public section

noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory
open CategoricalEssentialIncompleteness.V46
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticLists
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax
open CategoricalEssentialIncompleteness.V46.ConcreteNamedComparison
variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
variable (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

example {X Y C D : PredicateCategory T} (f : X ⟶ C) (g : Y ⟶ D) (φ ψ : M → M)
    (hf : ∀ x : Obj T M X, ((F T M).map f x).val = φ x.val)
    (hg : ∀ y : Obj T M Y, ((F T M).map g y).val = ψ y.val)
    (q : SyntaxPolynomial (PredicateCategory T)) (u : M) (z : Obj T M (q.eval.obj (X,Y)))
    (hz : (baseRepresentation T X Y q).val.Evalb ![u,z.val]) :
    (baseRepresentation T C D q).val.Evalb
      ![ConcreteNamedSubstitution.mapChildren φ ψ q u,
        ((F T M).map (q.eval.map ((f,g) : (X,Y) ⟶ (C,D))) z).val] :=
  representation_map T M f g φ ψ hf hg q u z hz
