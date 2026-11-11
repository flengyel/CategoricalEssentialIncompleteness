/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import FailureOfComposition.NumericalDomainOrder.Soundness
public import FailureOfComposition.NumericalProductProofs.Structural.Codes

/-!
# Arithmetic graph of the domain-order scheme code

The graph below composes the accepted internal graphs for program composition,
the equality tag, the right-instance tag, and implication coding.  It therefore
tracks the actual formula code at every PA-model element rather than merely the
external standard builder.
-/

@[expose] public section

set_option autoImplicit false

open Encodable FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.Entailment Metamath.Feferman
open scoped FFL.FirstOrder.Arithmetic
open Arith.Feferman.Structural Arith.Feferman.Specialization

namespace FailureOfComposition.NumericalDomainOrder

open NumericalProductProofs UniformIndexQuotient

noncomputable def domainOrderAxiomCodeValue
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (s r i : V) : V :=
  impValue (equalityCodeValue (compIndexValue s r) r)
    (impValue (rightInstanceCodeValue r i i)
      (rightInstanceCodeValue s i i))

noncomputable def domainOrderAxiomCodeGraph : 𝚺₁.Semisentence 4 := .mkSigma
  “y s r i.
    ∃ c, !compIndexGraph c s r ∧
    ∃ a, !equalityCodeGraph a c r ∧
    ∃ b, !rightInstanceCodeGraph b r i i ∧
    ∃ d, !rightInstanceCodeGraph d s i i ∧
    ∃ u, !impGraph u b d ∧
      !impGraph y a u”

theorem domainOrderAxiomCodeGraph_iff
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (y s r i : V) :
    Semiformula.Evalb (M := V) ![y, s, r, i]
        domainOrderAxiomCodeGraph.val ↔
      y = domainOrderAxiomCodeValue s r i := by
  simp [domainOrderAxiomCodeGraph, domainOrderAxiomCodeValue,
    compIndexGraph_iff, equalityCodeGraph_iff,
    rightInstanceCodeGraph_iff, impGraph_iff_impValue]

theorem domainOrderAxiomCodeGraph_total
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (s r i : V) :
    ∃ y : V, Semiformula.Evalb (M := V) ![y, s, r, i]
      domainOrderAxiomCodeGraph.val :=
  ⟨domainOrderAxiomCodeValue s r i,
    (domainOrderAxiomCodeGraph_iff _ _ _ _).mpr rfl⟩

theorem domainOrderAxiomCodeGraph_functional
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    {y z s r i : V}
    (hy : Semiformula.Evalb (M := V) ![y, s, r, i]
      domainOrderAxiomCodeGraph.val)
    (hz : Semiformula.Evalb (M := V) ![z, s, r, i]
      domainOrderAxiomCodeGraph.val) :
    y = z :=
  (domainOrderAxiomCodeGraph_iff y s r i).mp hy |>.trans
    ((domainOrderAxiomCodeGraph_iff z s r i).mp hz).symm

theorem domainOrderAxiomCodeValue_nat (s r i : ℕ) :
    domainOrderAxiomCodeValue s r i = domainOrderAxiomCode s r i := by
  simp [domainOrderAxiomCodeValue, compIndexValue_nat,
    equalityCodeValue_nat, rightInstanceCodeValue_nat, impValue_nat,
    domainOrderAxiomCode_eq_imp]

end FailureOfComposition.NumericalDomainOrder
