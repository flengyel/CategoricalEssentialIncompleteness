/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SyntacticSyntaxCoding

/-! Ordered postfix child words and root constructor records. -/

@[expose] public section
noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax
open Coding
variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
example (p : RawPolynomial) (o u : M) :
    (constructorGraph false p).val.Evalb ![o, u] ↔ o = constructor false p u :=
  constructorGraph_eval false p o u
example (p : RawPolynomial) (o u : M) :
    (constructorGraph true p).val.Evalb ![o, u] ↔ o = constructor true p u :=
  constructorGraph_eval true p o u
example (p : RawPolynomial) (u : M) :
    len (constructor false p u) = len (childrenWord p u) + 1 := constructor_length false p u
