/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SyntacticSyntaxFibers

/-! # Root-operation graphs of arbitrary categorical syntax algebras -/

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
variable {P : PredicateCategory T} (X : Over P × Over P)
variable (a : SyntaxPolynomial (PredicateCategory T)) {Z : Over P}

/-- Decode a given operation in the slice through the polynomial representation. This
defines a Sigma-one graph without choosing a fold. -/
def decodedOperation (f : (a.withParameters P).eval.obj X ⟶ Z) : TernaryGraph :=
  let R := fiberRepresentation T P X a
  let g := (chosenGraph T f.left).graph
  .mkSigma “p u v. ∃ z, !R.val p u z ∧ !g.val z v”

@[simp] theorem decodedOperation_eval {M : Type} [ORingStructure M]
    (f : (a.withParameters P).eval.obj X ⟶ Z) (p u v : M) :
    (decodedOperation T X a f).val.Evalb ![p, u, v] ↔
      ∃ z : M, (fiberRepresentation T P X a).val.Evalb ![p, u, z] ∧
        (chosenGraph T f.left).graph.val.Evalb ![z, v] := by
  simp [decodedOperation]

/-- The algebra morphism supplies the full output-fiber condition; there is no assumption
that its target is a constant family. -/
theorem decodedOperation_support (f : (a.withParameters P).eval.obj X ⟶ Z) :
    T ⊢ operationSupportSentence P X.1.left X.2.left Z.left
      (chosenGraph T X.1.hom).graph (chosenGraph T X.2.hom).graph
        (chosenGraph T Z.hom).graph a (decodedOperation T X a f) := by
  apply complete.{0} T
  intro M _ _
  let : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 := models_of_subtheory (U := T) inferInstance
  have hs : ∀ p u v : M, (decodedOperation T X a f).val.Evalb ![p, u, v] →
      (rawFiber P X.1.left X.2.left (chosenGraph T X.1.hom).graph
        (chosenGraph T X.2.hom).graph a).val.Evalb ![p, u] ∧ Z.left.val.Evalb ![v] ∧
          (chosenGraph T Z.hom).graph.val.Evalb ![v, p] := by
    intro p u v h
    obtain ⟨z, hz, hgv⟩ := (decodedOperation_eval T X a f p u v).mp h
    obtain ⟨hu, _, hzp⟩ := fiberRepresentation_support T M P X a p u z hz
    exact ⟨hu, ((chosenGraph T f.left).support_model M z v hgv).2,
      overGraph_target T M f z v p hgv hzp⟩
  simpa [models_iff, operationSupportSentence] using hs


/-- Totality and uniqueness are derived from the unique source point and the given
operation morphism, in every model of T. -/
theorem decodedOperation_total (f : (a.withParameters P).eval.obj X ⟶ Z) :
    T ⊢ operationTotalSentence P X.1.left X.2.left
      (chosenGraph T X.1.hom).graph (chosenGraph T X.2.hom).graph
        a (decodedOperation T X a f) := by
  apply complete.{0} T
  intro M _ _
  let : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 := models_of_subtheory (U := T) inferInstance
  have ht : ∀ p u : M,
      (rawFiber P X.1.left X.2.left (chosenGraph T X.1.hom).graph
        (chosenGraph T X.2.hom).graph a).val.Evalb ![p, u] →
          ∃! v : M, (decodedOperation T X a f).val.Evalb ![p, u, v] := by
    intro p u hu
    let pp : Obj T M P := ⟨p, rawFiber_parameter P X.1.left X.2.left
      (chosenGraph T X.1.hom).graph (chosenGraph T X.2.hom).graph a p u hu⟩
    obtain ⟨z, hz, hzu⟩ := fiberRepresentation_existsUnique T M P X a pp u hu
    obtain ⟨v, hv, _⟩ := (chosenGraph T f.left).total_model M z.val z.property
    refine ⟨v, (decodedOperation_eval T X a f p u v).mpr ⟨z.val, hz, hv⟩, ?_⟩
    intro v' hv'
    obtain ⟨z', hz', hg'⟩ := (decodedOperation_eval T X a f p u v').mp hv'
    have hs := (fiberRepresentation_support T M P X a p u z' hz').2.1
    have he := congrArg Subtype.val (hzu ⟨z', hs⟩ hz')
    dsimp at he
    rw [he] at hg'
    exact graph_functional_model (chosenGraph T f.left) z.val v' v hg' hv
  simpa [models_iff, operationTotalSentence] using ht

/-- Every two-sorted algebra in an arbitrary parameter slice has concrete Sigma-one root
operations satisfying the arithmetic fiber laws. The data contain no chosen evaluator
and no initiality assertion. -/
def decode (P : PredicateCategory T) (a b : SyntaxPolynomial (PredicateCategory T))
    (B : Endofunctor.Algebra (SyntaxPolynomial.jointFunctor
      (a.withParameters P) (b.withParameters P))) :
    SliceAlgebra T P B.a.1.left B.a.2.left a b where
  termProjection := chosenGraph T B.a.1.hom
  formulaProjection := chosenGraph T B.a.2.hom
  termOp := decodedOperation T B.a a B.str.1
  formulaOp := decodedOperation T B.a b B.str.2
  term_support := decodedOperation_support T B.a a B.str.1
  formula_support := decodedOperation_support T B.a b B.str.2
  term_total := decodedOperation_total T B.a a B.str.1
  formula_total := decodedOperation_total T B.a b B.str.2

end CategoricalEssentialIncompleteness.V46.SyntacticSyntax
