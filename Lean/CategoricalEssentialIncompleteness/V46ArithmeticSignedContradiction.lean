/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ArithmeticSignedTheoryTruth

/-! # A common internal support excludes contradictory signed derivations -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.Limits
open FailureOfComposition.CodedObjectMembership
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticLists

namespace CategoricalEssentialIncompleteness.V46.ArithmeticSignedTheoryTruth
open CoveredDerivationInvariant SyntacticDerivation SyntacticSyntax
local notation "N" => (PrintedObjectCoding.Number : PredicateCategory 𝗣𝗔)
variable {V : PredicateCategory 𝗣𝗔}
variable (S : CategoricalSyntax V (fun _ => ⊥_ (PredicateCategory 𝗣𝗔)) (fun _ => N) 0)
variable (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
local notation "P" => listObject 𝗣𝗔 N
local notation "Q" => derivationAlgebra 𝗣𝗔 (rules S)
local notation "v" => SignedFiniteFormulaValuation.valuation 𝗣𝗔 S

/-- The same concatenated support serves both derivations, including
when their internal codes and support lengths are nonstandard. -/
def jointSupport (p q : Obj 𝗣𝗔 M (Q).a.left) : Obj 𝗣𝗔 M P :=
  ⟨SyntacticSyntax.Words.append ((F 𝗣𝗔 M).map (support S) p).val
    ((F 𝗣𝗔 M).map (support S) q).val,
    (listCarrier_eval N _).mpr (by intro i hi; exact memberFormula_omega_eval _)⟩

theorem jointSupport_alpha (p q : Obj 𝗣𝗔 M (Q).a.left) :
    (FiniteSigmaOne.allEntriesCondition ArithmeticDiagonalCodes.alpha).Evalb
      ![(jointSupport S M p q).val] := by
  apply (ArithmeticSignedFiniteSupport.all_entries_append _ _ _).mpr
  exact ⟨SignedDerivation.canonical_support 𝗣𝗔 S.logicalAxioms S.sentenceInclusion (axioms S)
      S.quantifierConstructor S.implicationConstructor p,
    SignedDerivation.canonical_support 𝗣𝗔 S.logicalAxioms S.sentenceInclusion (axioms S)
      S.quantifierConstructor S.implicationConstructor q⟩

theorem joint_left_truth (p q : Obj 𝗣𝗔 M (Q).a.left) :
    TrueAt 𝗣𝗔 M v (jointSupport S M p q) ((F 𝗣𝗔 M).map (Q).a.hom p) :=
  internal_truth S M _ (jointSupport_alpha S M p q) p
    (ArithmeticFiniteCoverage.covers_append_left _ _)

theorem joint_right_truth (p q : Obj 𝗣𝗔 M (Q).a.left) :
    TrueAt 𝗣𝗔 M v (jointSupport S M p q) ((F 𝗣𝗔 M).map (Q).a.hom q) :=
  internal_truth S M _ (jointSupport_alpha S M p q) q
    (ArithmeticFiniteCoverage.covers_append_right _ _)

/-- A formula and its negation cannot both be true at the same support. -/
theorem trueAt_not_negation (l : Obj 𝗣𝗔 M P) (f : Obj 𝗣𝗔 M S.algebra.a.2)
    (hf : TrueAt 𝗣𝗔 M v l f)
    (hn : TrueAt 𝗣𝗔 M v l ((F 𝗣𝗔 M).map S.negationConstructor f)) : False := by
  obtain ⟨w, hp, hw⟩ := modelProduct_exists 𝗣𝗔 M P S.algebra.a.2 l f
  have hf' := hf w hp hw
  have hn' : (F 𝗣𝗔 M).map
      (ParameterizedBooleanValuation.evaluate S P (SignedFiniteFormulaValuation.atomAssignment 𝗣𝗔 N)
        prod.fst (prod.snd ≫ S.negationConstructor)) w =
      (F 𝗣𝗔 M).map (Two.constant _ true) w := by
    apply (trueAt_lift 𝗣𝗔 M v prod.fst (prod.snd ≫ S.negationConstructor) w).mp
    rw [Functor.map_comp_apply, hp, hw]
    exact hn
  rw [ParameterizedBooleanValuation.evaluate_negation] at hn'
  have hv : ParameterizedBooleanValuation.evaluate S P
      (SignedFiniteFormulaValuation.atomAssignment 𝗣𝗔 N) prod.fst prod.snd = v := by
    rw [ParameterizedBooleanValuation.evaluate, prod.lift_fst_snd, Category.id_comp]
    rfl
  rw [hv] at hn'
  have hfalse := ConcreteNamedComparison.model_unary 𝗣𝗔 M Bool.not v w true hf'
  have he : (F 𝗣𝗔 M).map (Two.constant (P ⨯ S.algebra.a.2) false) w =
      (F 𝗣𝗔 M).map (Two.constant (P ⨯ S.algebra.a.2) true) w := hfalse.symm.trans hn'
  change (F 𝗣𝗔 M).map (terminal.from _ ≫ coprod.inl) w =
    (F 𝗣𝗔 M).map (terminal.from _ ≫ coprod.inr) w at he
  rw [Functor.map_comp_apply, Functor.map_comp_apply] at he
  exact modelSum_disjoint 𝗣𝗔 M (⊤_ (PredicateCategory 𝗣𝗔)) (⊤_ (PredicateCategory 𝗣𝗔)) _ _ he

/-- In every model of Peano arithmetic, no two internal derivations conclude
a formula and its negation. -/
theorem no_contradictory_derivations (p q : Obj 𝗣𝗔 M (Q).a.left)
    (h : (F 𝗣𝗔 M).map (Q).a.hom q =
      (F 𝗣𝗔 M).map S.negationConstructor ((F 𝗣𝗔 M).map (Q).a.hom p)) : False := by
  have hq := joint_right_truth S M p q
  rw [h] at hq
  exact trueAt_not_negation S M _ _ (joint_left_truth S M p q) hq

end CategoricalEssentialIncompleteness.V46.ArithmeticSignedTheoryTruth
