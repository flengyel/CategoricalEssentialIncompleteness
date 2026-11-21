/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SyntacticSyntaxCandidate

/-! # Slice maps act on every valid raw polynomial input -/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.Limits
open FailureOfComposition.ProofSearch FailureOfComposition.CodedObjectMembership
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticLists

namespace CategoricalEssentialIncompleteness.V46.SyntacticSyntax
variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
variable (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
variable {P C D : PredicateCategory T} {A B : Over P}

/-- Totality of the two slice morphisms extends through the finite polynomial AST. The
source is guarded by the coefficient and child-word predicates; neither a chosen
evaluator nor a fold law occurs as a premise. -/
theorem mapRaw_arrow_exists (f : constantFamily P C ⟶ A) (g : constantFamily P D ⟶ B)
    (a : SyntaxPolynomial (PredicateCategory T)) (p : Obj T M P) (u : M)
    (h : (rawCarrier C D a).val.Evalb ![u]) :
    ∃ v : M, (mapRaw P (rawArrow T f) (rawArrow T g) a).val.Evalb ![p.val, u, v] := by
  induction a generalizing u with
  | term =>
      obtain ⟨v, hv, _⟩ := rawArrow_existsUnique T M f p ⟨u, h⟩
      exact ⟨v.val, hv⟩
  | formula =>
      obtain ⟨v, hv, _⟩ := rawArrow_existsUnique T M g p ⟨u, h⟩
      exact ⟨v.val, hv⟩
  | coefficient E =>
      refine ⟨u, ?_⟩
      change E.val.Evalb ![u] at h
      simpa [mapRaw] using And.intro p.property h
  | unit =>
      have hu : u = 0 := by simpa [rawCarrier] using h
      subst u
      refine ⟨0, ?_⟩
      simpa [mapRaw] using p.property
  | product a b ia ib =>
      obtain ⟨x, y, he, hx, hy⟩ := (rawCarrier_product_eval C D a b u).mp h
      obtain ⟨x', hx'⟩ := ia x hx
      obtain ⟨y', hy'⟩ := ib y hy
      exact ⟨Arithmetic.pair x' y',
        (mapRaw_product_eval P (rawArrow T f) (rawArrow T g) a b p.val u _).mpr
          ⟨x, y, x', y', he, rfl, hx', hy'⟩⟩
  | sum a b ia ib =>
      rcases (rawCarrier_sum_eval C D a b u).mp h with
        ⟨x, he, hx⟩ | ⟨y, he, hy⟩
      · obtain ⟨x', hx'⟩ := ia x hx
        exact ⟨Arithmetic.pair x' 0,
          (mapRaw_sum_eval P (rawArrow T f) (rawArrow T g) a b p.val u _).mpr
            (Or.inl ⟨x, x', he, rfl, hx'⟩)⟩
      · obtain ⟨y', hy'⟩ := ib y hy
        exact ⟨Arithmetic.pair y' 1,
          (mapRaw_sum_eval P (rawArrow T f) (rawArrow T g) a b p.val u _).mpr
            (Or.inr ⟨y, y', he, rfl, hy'⟩)⟩

end CategoricalEssentialIncompleteness.V46.SyntacticSyntax
