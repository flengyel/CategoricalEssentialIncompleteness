/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46SyntacticSyntaxCandidate
import CategoricalEssentialIncompleteness.V46SyntacticSyntaxOperationLaws

/-! # Scalar readings of actual candidate maps and decoded operations -/

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
variable (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T]

/-- Output membership follows from the graph itself, so the scalar
reading imposes no separate target-membership premise. -/
theorem rawArrow_value_iff {P C : PredicateCategory T} {X : Over P}
    (f : constantFamily P C ⟶ X) (p : Obj T M P) (u v : M)
    (z : Obj T M (P ⨯ C))
    (hz : (constantLeaf T P C).val.Evalb ![p.val, u, z.val]) :
    (rawArrow T f).val.Evalb ![p.val, u, v] ↔ v = ((F T M).map f.left z).val := by
  have hh : (chosenGraph T (prod.fst : P ⨯ C ⟶ P)).graph.val.Evalb ![z.val, p.val] ∧
      (chosenGraph T (prod.snd : P ⨯ C ⟶ C)).graph.val.Evalb ![z.val, u] := by
    simpa [constantLeaf] using hz
  let uu : Obj T M C :=
    ⟨u, ((chosenGraph T (prod.snd : P ⨯ C ⟶ C)).support_model M z.val u hh.2).2⟩
  constructor
  · intro h
    have hs := rawArrow_support T M f p.val u v h
    let vv : Obj T M X.left := ⟨v, hs.2.2.1⟩
    have he := (rawArrow_model T M f p uu z vv hz).mp h
    exact (congrArg Subtype.val he).symm
  · intro h
    subst v
    exact (rawArrow_model T M f p uu z ((F T M).map f.left z) hz).mpr rfl

/-- The same scalar reading applies to a given actual algebra operation
on its uniquely represented polynomial point. -/
theorem decodedOperation_value_iff {P : PredicateCategory T}
    (X : Over P × Over P) (a : SyntaxPolynomial (PredicateCategory T)) {Z : Over P}
    (f : (a.withParameters P).eval.obj X ⟶ Z) (p : Obj T M P) (u v : M)
    (z : Obj T M ((a.withParameters P).eval.obj X).left)
    (hz : (fiberRepresentation T P X a).val.Evalb ![p.val, u, z.val]) :
    (decodedOperation T X a f).val.Evalb ![p.val, u, v] ↔
      v = ((F T M).map f.left z).val := by
  let : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 := models_of_subtheory (U := T) inferInstance
  constructor
  · intro h
    obtain ⟨z', _, hv⟩ := (decodedOperation_eval T X a f p.val u v).mp h
    let vv : Obj T M Z.left :=
      ⟨v, ((chosenGraph T f.left).support_model M z' v hv).2⟩
    have he := (decodedOperation_model T M X a f p u z vv hz).mp h
    exact (congrArg Subtype.val he).symm
  · intro h
    subst v
    exact (decodedOperation_model T M X a f p u z ((F T M).map f.left z) hz).mpr rfl

end CategoricalEssentialIncompleteness.V46.SyntacticSyntax
