/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SyntacticSyntaxFold
public import CategoricalEssentialIncompleteness.V46SyntacticSyntaxCandidateValues
public import CategoricalEssentialIncompleteness.V46SyntacticSyntaxRawMapLaws

/-! # The actual fold's ternary graphs are exactly the finite-record evaluators -/

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
variable {P : PredicateCategory T} (a b : SyntaxPolynomial (PredicateCategory T))
variable (B : Endofunctor.Algebra (SyntaxPolynomial.jointFunctor
  (a.withParameters P) (b.withParameters P)))
variable (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T]

theorem termFold_pairPoint (p : Obj T M P) (w : Obj T M (termCarrier a b))
    (x : Obj T M B.a.1.left) :
    (F T M).map (termFold T a b B).left (pairPoint T M p w) = x ↔
      ((decode T P a b B).evaluationFormula false).val.Evalb ![p.val, w.val, x.val] := by
  change (F T M).map (termFoldMap T a b B) (pairPoint T M p w) = x ↔ _
  have h := termFoldMap_eval T a b B M (pairPoint T M p w) x
  rw [pairPoint_fst, pairPoint_snd] at h
  exact h

theorem formulaFold_pairPoint (p : Obj T M P) (w : Obj T M (formulaCarrier a b))
    (x : Obj T M B.a.2.left) :
    (F T M).map (formulaFold T a b B).left (pairPoint T M p w) = x ↔
      ((decode T P a b B).evaluationFormula true).val.Evalb ![p.val, w.val, x.val] := by
  change (F T M).map (formulaFoldMap T a b B) (pairPoint T M p w) = x ↔ _
  have h := formulaFoldMap_eval T a b B M (pairPoint T M p w) x
  rw [pairPoint_fst, pairPoint_snd] at h
  exact h

/-- The equivalence is unconditional on scalar inputs: both sides have
their actual parameter, accepted-word and output support built in. -/
theorem termFold_rawArrow (p w x : M) :
    (rawArrow T (termFold T a b B)).val.Evalb ![p, w, x] ↔
      ((decode T P a b B).evaluationFormula false).val.Evalb ![p, w, x] := by
  let : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 := models_of_subtheory (U := T) inferInstance
  constructor
  · intro h
    obtain ⟨hp, hw, hx, _⟩ := rawArrow_support T M (termFold T a b B) p w x h
    let pp : Obj T M P := ⟨p, hp⟩
    let ww : Obj T M (termCarrier a b) := ⟨w, hw⟩
    let xx : Obj T M B.a.1.left := ⟨x, hx⟩
    have hc := (constantLeaf_model T M P (termCarrier a b) pp ww
      (pairPoint T M pp ww)).mpr ⟨pairPoint_fst T M pp ww, pairPoint_snd T M pp ww⟩
    have he := (rawArrow_model T M (termFold T a b B) pp ww
      (pairPoint T M pp ww) xx hc).mp h
    exact (termFold_pairPoint T a b B M pp ww xx).mp he
  · intro h
    obtain ⟨hp, hw, hx⟩ := (decode T P a b B).evaluation_fiber false p w x h
    let pp : Obj T M P := ⟨p, hp⟩
    let ww : Obj T M (termCarrier a b) := ⟨w, hw⟩
    let xx : Obj T M B.a.1.left := ⟨x, hx.1⟩
    have hc := (constantLeaf_model T M P (termCarrier a b) pp ww
      (pairPoint T M pp ww)).mpr ⟨pairPoint_fst T M pp ww, pairPoint_snd T M pp ww⟩
    exact (rawArrow_model T M (termFold T a b B) pp ww
      (pairPoint T M pp ww) xx hc).mpr ((termFold_pairPoint T a b B M pp ww xx).mpr h)

theorem formulaFold_rawArrow (p w x : M) :
    (rawArrow T (formulaFold T a b B)).val.Evalb ![p, w, x] ↔
      ((decode T P a b B).evaluationFormula true).val.Evalb ![p, w, x] := by
  let : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 := models_of_subtheory (U := T) inferInstance
  constructor
  · intro h
    obtain ⟨hp, hw, hx, _⟩ := rawArrow_support T M (formulaFold T a b B) p w x h
    let pp : Obj T M P := ⟨p, hp⟩
    let ww : Obj T M (formulaCarrier a b) := ⟨w, hw⟩
    let xx : Obj T M B.a.2.left := ⟨x, hx⟩
    have hc := (constantLeaf_model T M P (formulaCarrier a b) pp ww
      (pairPoint T M pp ww)).mpr ⟨pairPoint_fst T M pp ww, pairPoint_snd T M pp ww⟩
    have he := (rawArrow_model T M (formulaFold T a b B) pp ww
      (pairPoint T M pp ww) xx hc).mp h
    exact (formulaFold_pairPoint T a b B M pp ww xx).mp he
  · intro h
    obtain ⟨hp, hw, hx⟩ := (decode T P a b B).evaluation_fiber true p w x h
    let pp : Obj T M P := ⟨p, hp⟩
    let ww : Obj T M (formulaCarrier a b) := ⟨w, hw⟩
    let xx : Obj T M B.a.2.left := ⟨x, hx.1⟩
    have hc := (constantLeaf_model T M P (formulaCarrier a b) pp ww
      (pairPoint T M pp ww)).mpr ⟨pairPoint_fst T M pp ww, pairPoint_snd T M pp ww⟩
    exact (rawArrow_model T M (formulaFold T a b B) pp ww
      (pairPoint T M pp ww) xx hc).mpr ((formulaFold_pairPoint T a b B M pp ww xx).mpr h)


/-- Polynomial application may read either the actual fold graphs or
the proved evaluator graphs, on all scalar inputs. -/
theorem fold_mapRaw (q : RawPolynomial) (p u v : M) :
    (mapRaw P (rawArrow T (termFold T a b B)) (rawArrow T (formulaFold T a b B))
      q).val.Evalb ![p, u, v] ↔
        (mapRaw P ((decode T P a b B).evaluationFormula false)
          ((decode T P a b B).evaluationFormula true) q).val.Evalb ![p, u, v] := by
  let : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 := models_of_subtheory (U := T) inferInstance
  exact mapRaw_congr_model P (rawArrow T (termFold T a b B))
    (rawArrow T (formulaFold T a b B)) ((decode T P a b B).evaluationFormula false)
    ((decode T P a b B).evaluationFormula true)
    (termFold_rawArrow T a b B M) (formulaFold_rawArrow T a b B M) q p u v

end CategoricalEssentialIncompleteness.V46.SyntacticSyntax
