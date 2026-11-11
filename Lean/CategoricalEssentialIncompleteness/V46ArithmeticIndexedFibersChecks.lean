/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ArithmeticIndexedFibers


/-! # Statement checks in `V46ArithmeticIndexedFibersChecks` -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
namespace CategoricalEssentialIncompleteness.V46.ArithmeticIndexedFibers
example (AxPA : Carrier) (e : ℕ) :
    Endofunctor.Algebra (ArithmeticIndexedFamily.rules AxPA).inference ≌
      Endofunctor.Algebra (singleRules AxPA e).inference ×
        Endofunctor.Algebra (complementRules AxPA e).inference := algebraEquivalence AxPA e
example (AxPA : Carrier) (e : ℕ) : IsInitial (fiberAlgebra AxPA e) := fiberInitial AxPA e
example (AxPA : Carrier) (e : ℕ) :
    (fiberAlgebra AxPA e).a = Over.mk (pullback.snd
      (ArithmeticIndexedFamily.conclusion AxPA) (fiberMap e ArithmeticIndexedFamily.formula)) := rfl
example (AxPA : Carrier) (e : ℕ) :
    individualAlgebra AxPA e ≅ fiberAlgebra AxPA e := individualFiberAlgebraIso AxPA e
example (AxPA : Carrier) (e : ℕ) :
    IsPullback (derivationMap AxPA e) (individualAlgebra AxPA e).a.hom
      (ArithmeticIndexedFamily.conclusion AxPA)
      (prod.lift (terminal.from ArithmeticIndexedFamily.formula ≫ numeral e)
        (𝟙 ArithmeticIndexedFamily.formula)) := by
  simpa only [fiberMap,fiberMap_primitive] using derivation_pullback AxPA e
example (AxPA : Carrier) (e : ℕ) :
    IsPullback (sentenceMap AxPA e) (individualSentenceConclusion AxPA e)
      (ArithmeticIndexedFamily.sentenceConclusion AxPA)
      (prod.lift (terminal.from ArithmeticIndexedFamily.sentence ≫ numeral e)
        (𝟙 ArithmeticIndexedFamily.sentence)) := by
  simpa only [fiberMap,fiberMap_primitive] using sentence_pullback AxPA e
example (AxPA : Carrier) (e : ℕ) :
    imageSubobject (individualSentenceConclusion AxPA e) =
      (Subobject.pullback (prod.lift (terminal.from ArithmeticIndexedFamily.sentence ≫ numeral e)
        (𝟙 ArithmeticIndexedFamily.sentence))).obj
          (ArithmeticIndexedFamily.sentenceTheory AxPA) := by
  simpa only [fiberMap,fiberMap_primitive] using sentenceTheory_fiber AxPA e
end CategoricalEssentialIncompleteness.V46.ArithmeticIndexedFibers
