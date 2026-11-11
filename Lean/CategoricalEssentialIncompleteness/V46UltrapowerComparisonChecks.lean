/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46UltrapowerComparison

/-! The arithmetic comparison is checked on every total-split morphism. -/

@[expose] public section

noncomputable section

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic Filter CategoryTheory
open CategoricalEssentialIncompleteness.V46

example {I : Type} (U : Ultrafilter I) :
    PredicateInterpretation.functor 𝗣𝗔 ℕ ⋙ Ultrapower.functor U ≅
      PredicateInterpretation.functor 𝗣𝗔 (ArithmeticUltrapower.Model U) :=
  ArithmeticUltrapower.predicateComparison U

example {I : Type} (U : Ultrafilter I) :
    PredicateInterpretation.totalFunctor 𝗣𝗔 ℕ ⋙ Ultrapower.functor U ≅
      PredicateInterpretation.totalFunctor 𝗣𝗔 (ArithmeticUltrapower.Model U) :=
  ArithmeticUltrapower.comparison U

example {I : Type} (U : Ultrafilter I)
    {X Y : SyntacticPredicates.TotalSplit 𝗣𝗔} (f : X ⟶ Y) :
    (Ultrapower.functor U).map ((PredicateInterpretation.totalFunctor 𝗣𝗔 ℕ).map f) ≫
        (ArithmeticUltrapower.comparison U).hom.app Y =
      (ArithmeticUltrapower.comparison U).hom.app X ≫
        (PredicateInterpretation.totalFunctor 𝗣𝗔 (ArithmeticUltrapower.Model U)).map f :=
  ArithmeticUltrapower.comparison_naturality U f

example {I : Type} (U : Ultrafilter I) :
    PredicateInterpretation.canonicalDomainFunctor 𝗣𝗔 ℕ ⋙ Ultrapower.functor U ≅
      PredicateInterpretation.canonicalDomainFunctor 𝗣𝗔 (ArithmeticUltrapower.Model U) :=
  ArithmeticUltrapower.canonicalComparison U

example {I : Type} (U : Ultrafilter I)
    {X Y : SyntacticPredicates.TotalSplit 𝗣𝗔} (f : X ⟶ Y) :
    (Ultrapower.functor U).map
        ((PredicateInterpretation.canonicalDomainFunctor 𝗣𝗔 ℕ).map f) ≫
        (ArithmeticUltrapower.canonicalComparison U).hom.app Y =
      (ArithmeticUltrapower.canonicalComparison U).hom.app X ≫
        (PredicateInterpretation.canonicalDomainFunctor 𝗣𝗔 (ArithmeticUltrapower.Model U)).map f :=
  ArithmeticUltrapower.canonicalComparison_naturality U f
