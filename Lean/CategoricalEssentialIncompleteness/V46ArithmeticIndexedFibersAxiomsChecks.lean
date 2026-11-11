/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ArithmeticIndexedFibersAxioms


/-! # Statement checks in `V46ArithmeticIndexedFibersAxiomsChecks` -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
namespace CategoricalEssentialIncompleteness.V46.ArithmeticIndexedFibers
example (AxPA : Carrier) (e : ℕ) :
    IsPullback (fiberToFamilyPredicate AxPA e) (fiberSentencePredicate AxPA e)
      (ArithmeticIndexedAxioms.predicateInclusion AxPA)
      (rawNumeralPair ArithmeticIndexedAxioms.sentencePredicate e) := predicateAxiom_pullback AxPA e
example (e : ℕ) :
    (realization 𝗣𝗔).map (rawNumeralPair ArithmeticIndexedAxioms.sentencePredicate e) ≫
      ArithmeticIndexedAxioms.productIso.hom =
      prod.lift (terminal.from ArithmeticIndexedAxioms.sentence ≫ numeral e)
        (𝟙 ArithmeticIndexedAxioms.sentence) := (realized_rawNumeralPair e).trans (fiberMap_primitive e ArithmeticIndexedAxioms.sentence)
example (AxPA : Carrier) (e : ℕ) :
    IsPullback (fiberToFamily AxPA e) (fiberAxioms AxPA e)
      (ArithmeticIndexedAxioms.axioms AxPA)
      (prod.lift (terminal.from ArithmeticIndexedAxioms.sentence ≫ numeral e)
        (𝟙 ArithmeticIndexedAxioms.sentence)) := by
  have hk : fiberMap e ArithmeticIndexedAxioms.sentence =
      prod.lift (terminal.from ArithmeticIndexedAxioms.sentence ≫ numeral e)
        (𝟙 ArithmeticIndexedAxioms.sentence) := fiberMap_primitive e ArithmeticIndexedAxioms.sentence
  rw [← hk]
  exact axiom_pullback AxPA e
end CategoricalEssentialIncompleteness.V46.ArithmeticIndexedFibers
