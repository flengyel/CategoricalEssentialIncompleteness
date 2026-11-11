/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ExponentialProducts

/-! Both product code translations are T-provable total graph morphisms. -/

@[expose] public section
noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46
open SyntacticPredicates
section Theory
variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]

example (C D : PredicateCategory T) :
    GraphMorphism T (productCarrier C D) (ExponentialProducts.carrier C D) :=
  ExponentialProducts.encode T C D

example (C D : PredicateCategory T) :
    GraphMorphism T (ExponentialProducts.carrier C D) (productCarrier C D) :=
  ExponentialProducts.decode T C D

example (C D : PredicateCategory T) :
    CategoryTheory.Iso (C := PredicateCategory T)
      (productCarrier C D) (ExponentialProducts.carrier C D) :=
  ExponentialProducts.rawProductIso T C D

example (C D : PredicateCategory T) :
    CategoryTheory.Iso (C := PredicateCategory T) (C ⨯ D) (ExponentialProducts.carrier C D) :=
  ExponentialProducts.productIso T C D

end Theory

example {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (C D : Carrier) (a b target : M) :
    (ExponentialProducts.encodeGraph C D).val.Evalb ![Arithmetic.pair a b, target] ↔
      C.val.Evalb ![a] ∧ D.val.Evalb ![b] ∧ target = ExponentialPairing.code a b :=
  ExponentialProducts.encodeGraph_pair C D a b target
