/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NumericalArithmeticPA
public import CategoricalEssentialIncompleteness.V46SyntacticLists
public import Foundation.FirstOrder.Arithmetic.TA.Basic

/-! # Unchanged PA graphs in the standard true arithmetic presentation -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates

namespace CategoricalEssentialIncompleteness.V46.NumericalArithmetic

/-- The arithmetic programs and graph coordinates are unchanged. Only
support and totality proofs are weakened to the full standard theory. -/
def liftGraph {C D : Carrier} (f : GraphMorphism 𝗣𝗔 C D) : GraphMorphism 𝗧𝗔 C D where
  graph := f.graph
  support := WeakerThan.pbl (𝓢 := 𝗣𝗔) (𝓣 := 𝗧𝗔) f.support
  total := WeakerThan.pbl (𝓢 := 𝗣𝗔) (𝓣 := 𝗧𝗔) f.total

@[simp] theorem liftGraph_graph {C D : Carrier} (f : GraphMorphism 𝗣𝗔 C D) :
    (liftGraph f).graph = f.graph := rfl

theorem liftGraph_value {C D : Carrier} (f : GraphMorphism 𝗣𝗔 C D)
    (x : PredicateInterpretation.Obj ℕ C) :
    PredicateInterpretation.value 𝗧𝗔 ℕ (liftGraph f) x =
      PredicateInterpretation.value 𝗣𝗔 ℕ f x := by
  apply (PredicateInterpretation.value_eq_iff 𝗧𝗔 ℕ (liftGraph f) x _).mpr
  exact PredicateInterpretation.value_graph 𝗣𝗔 ℕ f x

theorem liftGraph_map {C D : Carrier} (f : GraphMorphism 𝗣𝗔 C D)
    (x : PredicateInterpretation.Obj ℕ C) :
    (PredicateInterpretation.functor 𝗧𝗔 ℕ).map (representedArrow 𝗧𝗔 (liftGraph f)) x =
      (PredicateInterpretation.functor 𝗣𝗔 ℕ).map (representedArrow 𝗣𝗔 f) x :=
  liftGraph_value f x

end CategoricalEssentialIncompleteness.V46.NumericalArithmetic
