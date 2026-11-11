/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SyntacticDerivationTuples

/-! Typed finite premise tuples with independently varying conclusions. -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticDerivation
variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
variable {F G : Carrier} (f : GraphMorphism T F G) (n : ℕ)
example : GraphMorphism T (tupleCarrier F n) (tupleCarrier G n) := tupleMorphism f n
example (F : PredicateCategory T) :
    GraphMorphism T (finitePower (D := PredicateCategory T) F n) (tupleCarrier F n) :=
  finitePowerEncoder T F n
example (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (x : M) (hx : (tupleCarrier F n).val.Evalb ![x]) :
    ∃! y : M, (tupleGraph f.graph n).val.Evalb ![x, y] := tupleGraph_total f M n x hx
example (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (a b c d : M) :
    (tupleGraph f.graph 2).val.Evalb ![Arithmetic.pair a b, Arithmetic.pair c d] ↔
      f.graph.val.Evalb ![a, c] ∧ f.graph.val.Evalb ![b, d] := by
  simp only [tupleGraph_product, Nat.zero_add, tupleGraph_one]
  constructor
  · rintro ⟨a', b', c', d', h₁, h₂, ha, hb⟩
    have h₁a : a = a' := by simpa only [pi₁_pair] using congrArg pi₁ h₁
    have h₁b : b = b' := by simpa only [pi₂_pair] using congrArg pi₂ h₁
    have h₂a : c = c' := by simpa only [pi₁_pair] using congrArg pi₁ h₂
    have h₂b : d = d' := by simpa only [pi₂_pair] using congrArg pi₂ h₂
    simpa only [h₁a, h₁b, h₂a, h₂b] using And.intro ha hb
  · rintro ⟨ha, hb⟩
    exact ⟨a, b, c, d, rfl, rfl, ha, hb⟩
