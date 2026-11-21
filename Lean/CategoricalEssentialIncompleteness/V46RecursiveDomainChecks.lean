/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46RecursiveUltrapowerComparison

/-! Chosen domains and their comparison on recursively interpreted carriers. -/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment Filter CategoryTheory
open CategoricalEssentialIncompleteness.V46

example (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] (M : Type) [ORingStructure M]
    [M↓[ℒₒᵣ] ⊧* T] :
    PredicateInterpretation.recursiveDomainFunctor T M ≅
      PredicateInterpretation.canonicalDomainFunctor T M :=
  PredicateInterpretation.recursiveDomainComparison T M

example (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] (M : Type) [ORingStructure M]
    [M↓[ℒₒᵣ] ⊧* T] {X Y : SyntacticPredicates.TotalSplit T} (f : X ⟶ Y)
    (x : PredicateInterpretation.RecursiveDomain T M X)
    (y : PredicateInterpretation.RecursiveDomain T M Y) :
    (PredicateInterpretation.recursiveDomainFunctor T M).map f x = y ↔
      y.val ∈ (CategoricalEssentialIncompleteness.LocalConnectedness.SyntacticModel.modelFunctor
        T M).map f.hom.hom x.val :=
  PredicateInterpretation.recursiveDomainFunctor_graph T M f x y

example {I : Type} (U : Ultrafilter I) :
    PredicateInterpretation.recursiveDomainFunctor 𝗣𝗔 ℕ ⋙ Ultrapower.functor U ≅
      PredicateInterpretation.recursiveDomainFunctor 𝗣𝗔 (ArithmeticUltrapower.Model U) :=
  ArithmeticUltrapower.recursiveComparison U
