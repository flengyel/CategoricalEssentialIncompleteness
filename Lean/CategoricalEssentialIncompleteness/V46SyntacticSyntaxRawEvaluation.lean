/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SyntacticSyntaxInterpretation

/-! # Finite-polynomial action on literal-word evaluation graphs -/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open FailureOfComposition.CodedObjectMembership
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates

namespace CategoricalEssentialIncompleteness.V46.SyntacticSyntax.Coding
section Models
variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

/-- Mapping recursive values preserves every root tag and coefficient
label; only the recursively erased positions can change. -/
theorem mapRaw_shape (P : Carrier) (hT hF : TernaryGraph) (q : RawPolynomial)
    (p u v : M) (h : (mapRaw P hT hF q).val.Evalb ![p, u, v]) : shape q u = shape q v := by
  induction q generalizing u v with
  | term => rfl
  | formula => rfl
  | coefficient C =>
      have he : P.val.Evalb ![p] ∧ C.val.Evalb ![u] ∧ v = u := by simpa [mapRaw] using h
      simpa [shape] using he.2.2.symm
  | unit => rfl
  | product a b ia ib =>
      obtain ⟨x, y, z, w, rfl, rfl, hx, hy⟩ := (mapRaw_product_eval P hT hF a b p u v).mp h
      simp [shape, ia x z hx, ib y w hy]
  | sum a b ia ib =>
      rcases (mapRaw_sum_eval P hT hF a b p u v).mp h with
        ⟨x, z, rfl, rfl, hx⟩ | ⟨y, w, rfl, rfl, hy⟩
      · simp [shape, ia x z hx]
      · simp [shape, ib y w hy]
end Models
end CategoricalEssentialIncompleteness.V46.SyntacticSyntax.Coding

namespace CategoricalEssentialIncompleteness.V46.SyntacticSyntax.SliceAlgebra
open Coding Postfix
variable {T : ArithmeticTheory} {P X Y : Carrier} {a b : RawPolynomial}
variable (A : SliceAlgebra T P X Y a b)
section Models
variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] [M↓[ℒₒᵣ] ⊧* T]

/-- Every selected child has a finite-record value in its supplied parameter fiber. The
induction is over the fixed finite polynomial, rather than over an external list of
model children. -/
theorem mapRaw_evaluation_exists (q : RawPolynomial) (p u : M)
    (hp : P.val.Evalb ![p])
    (hu : (rawCarrier (carrier false a b) (carrier true a b) q).val.Evalb ![u]) :
    ∃ v : M, (mapRaw P (A.evaluationFormula false) (A.evaluationFormula true) q).val.Evalb ![p, u, v] := by
  induction q generalizing u with
  | term =>
      obtain ⟨v, hv, _⟩ := A.evaluation_existsUnique false p u hp hu
      exact ⟨v, hv⟩
  | formula =>
      obtain ⟨v, hv, _⟩ := A.evaluation_existsUnique true p u hp hu
      exact ⟨v, hv⟩
  | coefficient C => exact ⟨u, by simpa [mapRaw, rawCarrier] using And.intro hp hu⟩
  | unit =>
      have hu0 : u = 0 := by simpa [rawCarrier] using hu
      exact ⟨0, by simp [mapRaw, hp, hu0]⟩
  | product c d ic id =>
      obtain ⟨x, y, rfl, hx, hy⟩ :=
        (rawCarrier_product_eval (carrier false a b) (carrier true a b) c d u).mp hu
      obtain ⟨v, hv⟩ := ic x hx
      obtain ⟨w, hw⟩ := id y hy
      exact ⟨⟪v, w⟫, (mapRaw_product_eval P _ _ c d p _ _).mpr ⟨x, y, v, w, rfl, rfl, hv, hw⟩⟩
  | sum c d ic id =>
      rcases (rawCarrier_sum_eval (carrier false a b) (carrier true a b) c d u).mp hu with
        ⟨x, rfl, hx⟩ | ⟨y, rfl, hy⟩
      · obtain ⟨v, hv⟩ := ic x hx
        exact ⟨⟪v, 0⟫, (mapRaw_sum_eval P _ _ c d p _ _).mpr (Or.inl ⟨x, v, rfl, rfl, hv⟩)⟩
      · obtain ⟨w, hw⟩ := id y hy
        exact ⟨⟪w, 1⟫, (mapRaw_sum_eval P _ _ c d p _ _).mpr (Or.inr ⟨y, w, rfl, rfl, hw⟩)⟩

omit [M↓[ℒₒᵣ] ⊧* T] in
/-- The polynomial output is in exactly the common source fiber needed
by the arbitrary root operation. All membership witnesses are positive. -/
theorem mapRaw_evaluation_fiber (q : RawPolynomial) (p u v : M)
    (h : (mapRaw P (A.evaluationFormula false) (A.evaluationFormula true) q).val.Evalb ![p, u, v]) :
    P.val.Evalb ![p] ∧
      (rawCarrier (carrier false a b) (carrier true a b) q).val.Evalb ![u] ∧
      (rawFiber P X Y A.termProjection.graph A.formulaProjection.graph q).val.Evalb ![p, v] := by
  induction q generalizing u v with
  | term =>
      obtain ⟨hp, hu, hf⟩ := A.evaluation_fiber false p u v h
      exact ⟨hp, hu, (rawFiber_term_eval P X Y _ _ p v).mpr ⟨hp, hf.1, hf.2⟩⟩
  | formula =>
      obtain ⟨hp, hu, hf⟩ := A.evaluation_fiber true p u v h
      exact ⟨hp, hu, (rawFiber_formula_eval P X Y _ _ p v).mpr ⟨hp, hf.1, hf.2⟩⟩
  | coefficient C =>
      have he : P.val.Evalb ![p] ∧ C.val.Evalb ![u] ∧ v = u := by simpa [mapRaw] using h
      rcases he with ⟨hp, hc, rfl⟩
      exact ⟨hp, hc, by simp [rawFiber, hp, hc]⟩
  | unit =>
      have he : P.val.Evalb ![p] ∧ u = 0 ∧ v = 0 := by simpa [mapRaw] using h
      exact ⟨he.1, by simpa [rawCarrier] using he.2.1, by simp [rawFiber, he.1, he.2.2]⟩
  | product c d ic id =>
      obtain ⟨x, y, z, w, rfl, rfl, hx, hy⟩ := (mapRaw_product_eval P _ _ c d p u v).mp h
      obtain ⟨hp, hxu, hxv⟩ := ic x z hx
      obtain ⟨_, hyu, hyv⟩ := id y w hy
      exact ⟨hp, (rawCarrier_product_eval _ _ c d _).mpr ⟨x, y, rfl, hxu, hyu⟩,
        (rawFiber_product_eval P X Y _ _ c d p _).mpr ⟨z, w, rfl, hxv, hyv⟩⟩
  | sum c d ic id =>
      rcases (mapRaw_sum_eval P _ _ c d p u v).mp h with
        ⟨x, z, rfl, rfl, hx⟩ | ⟨y, w, rfl, rfl, hy⟩
      · obtain ⟨hp, hxu, hxv⟩ := ic x z hx
        exact ⟨hp, (rawCarrier_sum_eval _ _ c d _).mpr (Or.inl ⟨x, rfl, hxu⟩),
          (rawFiber_sum_eval P X Y _ _ c d p _).mpr (Or.inl ⟨z, rfl, hxv⟩)⟩
      · obtain ⟨hp, hyu, hyv⟩ := id y w hy
        exact ⟨hp, (rawCarrier_sum_eval _ _ c d _).mpr (Or.inr ⟨y, rfl, hyu⟩),
          (rawFiber_sum_eval P X Y _ _ c d p _).mpr (Or.inr ⟨w, rfl, hyv⟩)⟩

end Models
end CategoricalEssentialIncompleteness.V46.SyntacticSyntax.SliceAlgebra
