/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46SyntacticSyntaxRaw

/-! # Pointwise graph equivalence is retained by the exact raw polynomial -/

noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates

namespace CategoricalEssentialIncompleteness.V46.SyntacticSyntax
variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

/-- This is equivalence of the graph formulas on all scalar inputs,
including unsupported inputs, before any algebra law is invoked. -/
theorem mapRaw_congr_model (P : Carrier) (hT hF eT eF : TernaryGraph)
    (ht : ∀ p u v : M, hT.val.Evalb ![p, u, v] ↔ eT.val.Evalb ![p, u, v])
    (hf : ∀ p u v : M, hF.val.Evalb ![p, u, v] ↔ eF.val.Evalb ![p, u, v])
    (a : RawPolynomial) (p u v : M) :
    (mapRaw P hT hF a).val.Evalb ![p, u, v] ↔
      (mapRaw P eT eF a).val.Evalb ![p, u, v] := by
  induction a generalizing u v with
  | term => exact ht p u v
  | formula => exact hf p u v
  | coefficient C => rfl
  | unit => rfl
  | product a b ia ib =>
      constructor
      · intro h
        obtain ⟨x, y, x', y', hu, hv, hx, hy⟩ :=
          (mapRaw_product_eval P hT hF a b p u v).mp h
        exact (mapRaw_product_eval P eT eF a b p u v).mpr
          ⟨x, y, x', y', hu, hv, (ia x x').mp hx, (ib y y').mp hy⟩
      · intro h
        obtain ⟨x, y, x', y', hu, hv, hx, hy⟩ :=
          (mapRaw_product_eval P eT eF a b p u v).mp h
        exact (mapRaw_product_eval P hT hF a b p u v).mpr
          ⟨x, y, x', y', hu, hv, (ia x x').mpr hx, (ib y y').mpr hy⟩
  | sum a b ia ib =>
      constructor
      · intro h
        rcases (mapRaw_sum_eval P hT hF a b p u v).mp h with
          ⟨x, x', hu, hv, hx⟩ | ⟨y, y', hu, hv, hy⟩
        · exact (mapRaw_sum_eval P eT eF a b p u v).mpr
            (Or.inl ⟨x, x', hu, hv, (ia x x').mp hx⟩)
        · exact (mapRaw_sum_eval P eT eF a b p u v).mpr
            (Or.inr ⟨y, y', hu, hv, (ib y y').mp hy⟩)
      · intro h
        rcases (mapRaw_sum_eval P eT eF a b p u v).mp h with
          ⟨x, x', hu, hv, hx⟩ | ⟨y, y', hu, hv, hy⟩
        · exact (mapRaw_sum_eval P hT hF a b p u v).mpr
            (Or.inl ⟨x, x', hu, hv, (ia x x').mpr hx⟩)
        · exact (mapRaw_sum_eval P hT hF a b p u v).mpr
            (Or.inr ⟨y, y', hu, hv, (ib y y').mpr hy⟩)

end CategoricalEssentialIncompleteness.V46.SyntacticSyntax
