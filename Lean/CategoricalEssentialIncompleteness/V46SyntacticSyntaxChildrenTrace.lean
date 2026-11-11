/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SyntacticSyntaxTraceConcat
public import CategoricalEssentialIncompleteness.V46SyntacticSyntaxRawEvaluation

/-! # Framed traces for the actual ordered child blocks of a constructor -/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open FailureOfComposition.CodedObjectMembership
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates

namespace CategoricalEssentialIncompleteness.V46.SyntacticSyntax.SliceAlgebra
open Coding Postfix
variable {T : ArithmeticTheory} {P X Y : Carrier} {a b : RawPolynomial}
variable (A : SliceAlgebra T P X Y a b)
section Models
variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

/-- Raw values in the common parameter fiber produce a typed child
stack over any already typed ambient tail. -/
theorem fiber_childStack (q : RawPolynomial) (p v tail : M)
    (hv : (rawFiber P X Y A.termProjection.graph A.formulaProjection.graph q).val.Evalb ![p, v])
    (ht : (fiberStackGraph P X Y A.termProjection.graph A.formulaProjection.graph).val.Evalb ![p, tail]) :
    (fiberStackGraph P X Y A.termProjection.graph A.formulaProjection.graph).val.Evalb ![p, childStack q v tail] := by
  induction q generalizing v tail with
  | term =>
      apply (fiberStackGraph_adjoin P X Y A.termProjection.graph A.formulaProjection.graph p ⟪v, 0⟫ tail).mpr
      exact ⟨by simpa using hv, ht⟩
  | formula =>
      apply (fiberStackGraph_adjoin P X Y A.termProjection.graph A.formulaProjection.graph p ⟪v, 1⟫ tail).mpr
      exact ⟨by simpa using hv, ht⟩
  | coefficient C => exact ht
  | unit => exact ht
  | product c d ic id =>
      obtain ⟨x, y, rfl, hx, hy⟩ := (rawFiber_product_eval P X Y _ _ c d p v).mp hv
      simpa [childStack] using id y (childStack c x tail) hy (ic x tail hx ht)
  | sum c d ic id =>
      rcases (rawFiber_sum_eval P X Y _ _ c d p v).mp hv with
        ⟨x, rfl, hx⟩ | ⟨y, rfl, hy⟩
      · simpa [childStack] using ic x tail hx ht
      · simpa [childStack] using id y tail hy ht

/-- Evaluation's existential witness is an actual finite forward
record, including its displayed final singleton value. -/
theorem evaluation_record (formula : Bool) (p word value : M)
    (h : (A.evaluationFormula formula).val.Evalb ![p, word, value]) :
    ∃ states : M, A.ValueRecord p word (len word) states ∧
      nth states (len word) = adjoin ⟪value, if formula then 1 else 0⟫ 0 + 1 := by
  have hl := ((A.evaluationFormula_eval formula p word value).mp h).2
  obtain ⟨_, _, states, hs, he⟩ := (A.loopEvaluationGraph_eval p word _).mp hl
  exact ⟨states, hs, he.symm⟩

theorem evaluation_framed_record (formula : Bool) (p word value tail : M)
    (h : (A.evaluationFormula formula).val.Evalb ![p, word, value])
    (ht : (fiberStackGraph P X Y A.termProjection.graph A.formulaProjection.graph).val.Evalb ![p, tail]) :
    ∃ states : M, A.TraceRecord p word (tail + 1) (len word) states ∧
      nth states (len word) = adjoin ⟪value, if formula then 1 else 0⟫ tail + 1 := by
  obtain ⟨states, hs, he⟩ := A.evaluation_record formula p word value h
  have hn : nth states (len word) ≠ 0 := by simp [he]
  refine ⟨frameVector states tail, A.valueRecord_frame hs hn ht, ?_⟩
  rw [nth_frameVector states tail (len word) (by rw [hs.1]; simp), he]
  simp

/-- Actual child values from mapRaw yield one actual framed trace for
all child blocks, in their printed left-to-right order. The finite
polynomial induction concatenates arithmetic computation records. -/
theorem children_trace (q : RawPolynomial) (p u v tail : M)
    (hp : P.val.Evalb ![p])
    (hm : (mapRaw P (A.evaluationFormula false) (A.evaluationFormula true) q).val.Evalb ![p, u, v])
    (ht : (fiberStackGraph P X Y A.termProjection.graph A.formulaProjection.graph).val.Evalb ![p, tail]) :
    ∃ states : M,
      A.TraceRecord p (childrenWord q u) (tail + 1) (len (childrenWord q u)) states ∧
        nth states (len (childrenWord q u)) = childStack q v tail + 1 := by
  induction q generalizing u v tail with
  | term => simpa [childrenWord, childStack] using A.evaluation_framed_record false p u v tail hm ht
  | formula => simpa [childrenWord, childStack] using A.evaluation_framed_record true p u v tail hm ht
  | coefficient C =>
      refine ⟨adjoin (tail + 1) 0, ?_, by simp [childrenWord, childStack]⟩
      simpa [childrenWord] using TraceRecord.zero A p 0 (tail + 1) (by simp [hp, ht])
  | unit =>
      refine ⟨adjoin (tail + 1) 0, ?_, by simp [childrenWord, childStack]⟩
      simpa [childrenWord] using TraceRecord.zero A p 0 (tail + 1) (by simp [hp, ht])
  | product c d ic id =>
      obtain ⟨x, y, z, w, rfl, rfl, hx, hy⟩ := (mapRaw_product_eval P _ _ c d p u v).mp hm
      obtain ⟨first, hf, hfe⟩ := ic x z tail hx ht
      have hcf := (A.mapRaw_evaluation_fiber c p x z hx).2.2
      have hct := A.fiber_childStack c p z tail hcf ht
      obtain ⟨second, hs, hse⟩ := id y w (childStack c z tail) hy hct
      have hs' : A.TraceRecord p (childrenWord d y) (nth first (len (childrenWord c x)))
          (len (childrenWord d y)) second := by rw [hfe]; exact hs
      obtain ⟨combined, hc, hce⟩ := A.traceRecord_concat hf hs'
      refine ⟨combined, ?_, ?_⟩
      · simpa [childrenWord] using hc
      · simpa [childrenWord, childStack, hse] using hce
  | sum c d ic id =>
      rcases (mapRaw_sum_eval P _ _ c d p u v).mp hm with
        ⟨x, z, rfl, rfl, hx⟩ | ⟨y, w, rfl, rfl, hy⟩
      · simpa [childrenWord, childStack] using ic x z tail hx ht
      · simpa [childrenWord, childStack] using id y w tail hy ht

end Models
end CategoricalEssentialIncompleteness.V46.SyntacticSyntax.SliceAlgebra
