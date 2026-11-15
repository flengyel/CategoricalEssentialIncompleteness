/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SignedDerivationInternalTruth
public import CategoricalEssentialIncompleteness.V46ArithmeticSignedAtoms

/-! # The internal truth invariant for the arithmetic diagonal axioms -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticLists

namespace CategoricalEssentialIncompleteness.V46.ArithmeticSignedTheoryTruth
open CoveredDerivationInvariant SyntacticDerivation SyntacticSyntax ArithmeticSignedAtoms
local notation "N" => (PrintedObjectCoding.Number : PredicateCategory 𝗣𝗔)
variable {V : PredicateCategory 𝗣𝗔}
variable (S : CategoricalSyntax V (fun _ => ⊥_ (PredicateCategory 𝗣𝗔)) (fun _ => N) 0)

def axioms : Limits.coprod (C := PredicateCategory 𝗣𝗔)
    ArithmeticDiagonalCodes.alpha ArithmeticDiagonalCodes.beta ⟶ S.sentenceObject :=
  coprod.desc (numberInclusion ArithmeticDiagonalCodes.alpha ≫ NullaryInterpretation.atomSentence S)
    (numberInclusion ArithmeticDiagonalCodes.beta ≫ NullaryInterpretation.atomSentence S ≫ S.sentenceNegation)

def rules : RulePresentation S.algebra.a.2 2 :=
  firstOrderRules S.logicalAxioms S.sentenceInclusion (axioms S)
    S.quantifierConstructor S.implicationConstructor

def support : (derivationAlgebra 𝗣𝗔 (rules S)).a.left ⟶
    listObject 𝗣𝗔 ArithmeticDiagonalCodes.alpha :=
  SignedDerivation.positiveSupport 𝗣𝗔 S.logicalAxioms S.sentenceInclusion (axioms S)
    S.quantifierConstructor S.implicationConstructor

variable (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
local notation "P" => listObject 𝗣𝗔 N
local notation "v" => SignedFiniteFormulaValuation.valuation 𝗣𝗔 S
local notation "leaf" => SignedDerivation.positiveLeafAssignment 𝗣𝗔 S.logicalParameters
  ArithmeticDiagonalCodes.alpha ArithmeticDiagonalCodes.beta

/-- The actual singleton fold has the canonical one-entry vector code. -/
theorem singleton_value (C : PredicateCategory 𝗣𝗔) (a : Obj 𝗣𝗔 M C) :
    ((F 𝗣𝗔 M).map (stableListAlgebra 𝗣𝗔 C).singleton a).val = adjoin a.val 0 := by
  change ((F 𝗣𝗔 M).map
    (prod.lift (𝟙 C) (terminal.from C ≫ (algebra 𝗣𝗔 C).nil) ≫ (algebra 𝗣𝗔 C).cons) a).val = _
  rw [Functor.map_comp_apply, cons_value]
  erw [ConcreteNamedComparison.model_lift_fst, ConcreteNamedComparison.model_lift_snd,
    Functor.map_id_apply, Functor.map_comp_apply, nil_value]

private theorem logical_true (l : Obj 𝗣𝗔 M P) (a : Obj 𝗣𝗔 M S.logicalParameters) :
    TrueAt 𝗣𝗔 M v l ((F 𝗣𝗔 M).map S.logicalAxioms a) := by
  obtain ⟨q, hp, ha⟩ := modelProduct_exists 𝗣𝗔 M P S.logicalParameters l a
  have h := ParameterizedBooleanModelTruth.logical_point 𝗣𝗔 M S P
    (SignedFiniteFormulaValuation.atomAssignment 𝗣𝗔 N)
    (prod.fst : P ⨯ S.logicalParameters ⟶ P) prod.snd q
  have ht := (trueAt_lift 𝗣𝗔 M v prod.fst (prod.snd ≫ S.logicalAxioms) q).mpr h
  rw [Functor.map_comp_apply, hp, ha] at ht
  exact ht

/-- All actual nullary labels are true on a covering alpha-support. -/
theorem leaf_truth (l : Obj 𝗣𝗔 M P)
    (hl : (FiniteSigmaOne.allEntriesCondition ArithmeticDiagonalCodes.alpha).Evalb ![l.val])
    (a : Obj 𝗣𝗔 M ((rules S).instances 0))
    (hc : ArithmeticFiniteCoverage.Covers ((F 𝗣𝗔 M).map leaf a).val l.val) :
    TrueAt 𝗣𝗔 M v l ((F 𝗣𝗔 M).map ((rules S).conclusion 0) a) := by
  rcases modelSum_cases 𝗣𝗔 M S.logicalParameters
    (Limits.coprod (C := PredicateCategory 𝗣𝗔)
      ArithmeticDiagonalCodes.alpha ArithmeticDiagonalCodes.beta) a with ⟨x, hx⟩ | ⟨ab, hab⟩
  · rw [← hx]
    have he : (coprod.inl : S.logicalParameters ⟶ (rules S).instances 0) ≫
        (rules S).conclusion 0 = S.logicalAxioms := by
      simp [rules, firstOrderRules]
    have h := ConcreteNamedComparison.parameterPoint_diagram 𝗣𝗔 M coprod.inl
      ((rules S).conclusion 0) (𝟙 _) S.logicalAxioms
      (by simpa only [Category.id_comp] using he) x
    simp only [Functor.map_id_apply] at h
    exact h.symm ▸ logical_true S M l x
  · rcases modelSum_cases 𝗣𝗔 M ArithmeticDiagonalCodes.alpha ArithmeticDiagonalCodes.beta ab with
      ⟨x, hx⟩ | ⟨x, hx⟩
    · let j : @Quiver.Hom (PredicateCategory 𝗣𝗔) inferInstance
        ArithmeticDiagonalCodes.alpha ((rules S).instances 0) := coprod.inl ≫ coprod.inr
      have hj : (F 𝗣𝗔 M).map j x = a := by
        dsimp only [j]
        erw [Functor.map_comp_apply, hx, hab]
      have hs : j ≫ leaf = (stableListAlgebra 𝗣𝗔 ArithmeticDiagonalCodes.alpha).singleton := by
        simp [j, SignedDerivation.positiveLeafAssignment]
      have hs' := ConcreteNamedComparison.parameterPoint_diagram 𝗣𝗔 M j leaf (𝟙 _)
        (stableListAlgebra 𝗣𝗔 ArithmeticDiagonalCodes.alpha).singleton
        (by simpa only [Category.id_comp] using hs) x
      simp only [Functor.map_id_apply, hj] at hs'
      have hm : MemVec x.val l.val := by
        have hcov := hc
        erw [hs'] at hcov
        erw [singleton_value, ArithmeticFiniteCoverage.covers_adjoin] at hcov
        exact hcov.1
      have he : j ≫ (rules S).conclusion 0 =
          numberInclusion ArithmeticDiagonalCodes.alpha ≫ NullaryInterpretation.atomFormula S := by
        simp [j, rules, firstOrderRules, axioms, Category.assoc]
      have he' := ConcreteNamedComparison.parameterPoint_diagram 𝗣𝗔 M j ((rules S).conclusion 0)
        (𝟙 _) (numberInclusion ArithmeticDiagonalCodes.alpha ≫ NullaryInterpretation.atomFormula S)
        (by simpa only [Category.id_comp] using he) x
      simp only [Functor.map_id_apply, hj] at he'
      exact he'.symm ▸ positive_true M S l x hm
    · let j : @Quiver.Hom (PredicateCategory 𝗣𝗔) inferInstance
        ArithmeticDiagonalCodes.beta ((rules S).instances 0) := coprod.inr ≫ coprod.inr
      have hj : (F 𝗣𝗔 M).map j x = a := by
        dsimp only [j]
        erw [Functor.map_comp_apply, hx, hab]
      have he : j ≫ (rules S).conclusion 0 =
          numberInclusion ArithmeticDiagonalCodes.beta ≫ NullaryInterpretation.atomFormula S ≫
            S.negationConstructor := by
        simp [j, rules, firstOrderRules, axioms, Category.assoc,
          CategoricalSyntax.sentenceNegation_inclusion]
      have he' := ConcreteNamedComparison.parameterPoint_diagram 𝗣𝗔 M j ((rules S).conclusion 0)
        (𝟙 _) (numberInclusion ArithmeticDiagonalCodes.beta ≫ NullaryInterpretation.atomFormula S ≫
          S.negationConstructor) (by simpa only [Category.id_comp] using he) x
      simp only [Functor.map_id_apply, hj] at he'
      exact he'.symm ▸ negative_true M S l x hl

/-- Every internal derivation of the diagonal signed calculus is true on
any alpha-support covering its positive leaves. -/
theorem internal_truth (l : Obj 𝗣𝗔 M P)
    (hl : (FiniteSigmaOne.allEntriesCondition ArithmeticDiagonalCodes.alpha).Evalb ![l.val])
    (q : Obj 𝗣𝗔 M (derivationAlgebra 𝗣𝗔 (rules S)).a.left)
    (hc : ArithmeticFiniteCoverage.Covers ((F 𝗣𝗔 M).map (support S) q).val l.val) :
    TrueAt 𝗣𝗔 M v l ((F 𝗣𝗔 M).map (derivationAlgebra 𝗣𝗔 (rules S)).a.hom q) := by
  exact SignedDerivation.truth_from_leaves 𝗣𝗔 M S (axioms S) P
    (SignedFiniteFormulaValuation.atomAssignment 𝗣𝗔 N) l (leaf_truth S M l hl) q hc

end CategoricalEssentialIncompleteness.V46.ArithmeticSignedTheoryTruth
