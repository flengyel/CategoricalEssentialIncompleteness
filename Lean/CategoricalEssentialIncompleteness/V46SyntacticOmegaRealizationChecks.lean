/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SyntacticOmegaRealization


/-! # Total numerical morphisms on the identity splitting of the number object -/

@[expose] public section
noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory
open CategoricalEssentialIncompleteness.V46
open SyntacticPredicates NamedArithmeticSignature SyntacticOmegaRealization
example (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] {C : PredicateCategory T}
    (f : GraphMorphism T variableSymbols C) :
    ArithmeticOmegaComparison.identityOmega T ⟶ (realization T).obj C := realizeFromOmega T f
example (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] {C : PredicateCategory T}
    (f : GraphMorphism T variableSymbols C) :
    (realizeFromOmega T f).hom.hom = f.toTotal.hom.hom := realizeFromOmega_underlying T f
example (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] {C : PredicateCategory T}
    (f : GraphMorphism T variableSymbols C) (M : Type)
    [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T]
    (x : PredicateInterpretation.CanonicalDomain T M (ArithmeticOmegaComparison.identityOmega T))
    (y : PredicateInterpretation.CanonicalDomain T M ((realization T).obj C)) :
    (PredicateInterpretation.canonicalDomainFunctor T M).map (realizeFromOmega T f) x = y ↔
      f.graph.val.Evalb ![x.val.val,y.val.val] := realizeFromOmega_graph T f M x y
