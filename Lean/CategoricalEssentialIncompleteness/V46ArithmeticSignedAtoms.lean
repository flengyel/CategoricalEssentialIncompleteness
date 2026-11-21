/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SignedFiniteFormulaValuation
public import CategoricalEssentialIncompleteness.V46CoveredDerivationInvariant
public import CategoricalEssentialIncompleteness.V46PrintedObjectCoding

/-! # Diagonal labels and their finite-support truth values -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.Limits
open FailureOfComposition.CodedObjectMembership
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticLists

namespace CategoricalEssentialIncompleteness.V46.ArithmeticSignedAtoms
open CoveredDerivationInvariant

/-- Every arithmetic predicate has its numerical inclusion into the number object. This
inclusion retains the literal code. -/
def numberInclusion (C : PredicateCategory 𝗣𝗔) :
    C ⟶ (PrintedObjectCoding.Number : PredicateCategory 𝗣𝗔) :=
  representedArrow 𝗣𝗔 (GraphMorphism.inclusion (T := 𝗣𝗔) (C := C) (D := PrintedObjectCoding.Number)
    (by
      apply complete.{0} 𝗣𝗔
      intro M _ _
      rw [models_iff, inclusionSentence_eval]
      intro x _
      exact memberFormula_omega_eval x))

variable (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

theorem numberInclusion_value (C : PredicateCategory 𝗣𝗔) (a : Obj 𝗣𝗔 M C) :
    ((F 𝗣𝗔 M).map (numberInclusion C) a).val = a.val := by
  have h := (PredicateInterpretation.map_class_eq_iff 𝗣𝗔 M
    (GraphMorphism.inclusion (T := 𝗣𝗔) (C := C) (D := PrintedObjectCoding.Number) _) a
    ((F 𝗣𝗔 M).map (numberInclusion C) a)).mp rfl
  exact (GraphMorphism.identityGraph_eval C _ _).mp h |>.2

variable {V : PredicateCategory 𝗣𝗔}
local notation "N" => (PrintedObjectCoding.Number : PredicateCategory 𝗣𝗔)
variable (S : CategoricalSyntax V (fun _ => ⊥_ (PredicateCategory 𝗣𝗔)) (fun _ => N) 0)
local notation "P" => listObject 𝗣𝗔 N
local notation "v" => SignedFiniteFormulaValuation.valuation 𝗣𝗔 S

private theorem frame_atom (negative : Bool) :
    prod.lift (prod.fst : P ⨯ N ⟶ P)
      (prod.snd ≫ (if negative then
        NullaryInterpretation.atomFormula S ≫ S.negationConstructor
        else NullaryInterpretation.atomFormula S)) =
      ((constantFamilyFunctor P).map (if negative then
        NullaryInterpretation.atomFormula S ≫ S.negationConstructor
        else NullaryInterpretation.atomFormula S)).left := by
  change prod.lift prod.fst (prod.snd ≫ _) = prod.map (𝟙 P) _
  apply prod.hom_ext
  · simp
  · simp

/-- A covered positive diagonal label gives a true atom at that support. -/
theorem positive_true (l : Obj 𝗣𝗔 M P) (a : Obj 𝗣𝗔 M ArithmeticDiagonalCodes.alpha)
    (ha : MemVec a.val l.val) :
    TrueAt 𝗣𝗔 M v l ((F 𝗣𝗔 M).map
      (numberInclusion ArithmeticDiagonalCodes.alpha ≫ NullaryInterpretation.atomFormula S) a) := by
  let x := (F 𝗣𝗔 M).map (numberInclusion ArithmeticDiagonalCodes.alpha) a
  obtain ⟨q, hp, hx⟩ := modelProduct_exists 𝗣𝗔 M P N l x
  have hm : MemVec ((F 𝗣𝗔 M).map (prod.snd : P ⨯ N ⟶ N) q).val
      ((F 𝗣𝗔 M).map (prod.fst : P ⨯ N ⟶ P) q).val := by
    rw [hp, hx]
    exact (numberInclusion_value M _ a) ▸ ha
  have h := SignedFiniteFormulaValuation.positive_atom 𝗣𝗔 S q hm
  have ht : TrueAt 𝗣𝗔 M v ((F 𝗣𝗔 M).map (prod.fst : P ⨯ N ⟶ P) q)
      ((F 𝗣𝗔 M).map (prod.snd ≫ NullaryInterpretation.atomFormula S) q) := by
    apply (trueAt_lift 𝗣𝗔 M v prod.fst (prod.snd ≫ NullaryInterpretation.atomFormula S) q).mpr
    have he := frame_atom S false
    erw [he, Functor.map_comp_apply]
    exact h
  rw [Functor.map_comp_apply, hp, hx] at ht
  simpa only [Functor.map_comp_apply] using ht

/-- PA disjointness discharges every negative diagonal leaf on an
arbitrary internal alpha-support. -/
theorem negative_true (l : Obj 𝗣𝗔 M P) (b : Obj 𝗣𝗔 M ArithmeticDiagonalCodes.beta)
    (hl : (FiniteSigmaOne.allEntriesCondition ArithmeticDiagonalCodes.alpha).Evalb ![l.val]) :
    TrueAt 𝗣𝗔 M v l ((F 𝗣𝗔 M).map
      (numberInclusion ArithmeticDiagonalCodes.beta ≫ NullaryInterpretation.atomFormula S ≫
        S.negationConstructor) b) := by
  let x := (F 𝗣𝗔 M).map (numberInclusion ArithmeticDiagonalCodes.beta) b
  obtain ⟨q, hp, hx⟩ := modelProduct_exists 𝗣𝗔 M P N l x
  have hs : (FiniteSigmaOne.allEntriesCondition ArithmeticDiagonalCodes.alpha).Evalb
      ![((F 𝗣𝗔 M).map (prod.fst : P ⨯ N ⟶ P) q).val] := by rw [hp]; exact hl
  have hn : ArithmeticDiagonalCodes.beta.val.Evalb
      ![((F 𝗣𝗔 M).map (prod.snd : P ⨯ N ⟶ N) q).val] := by
    rw [hx]
    exact (numberInclusion_value M _ b).symm ▸ b.property
  have h := SignedFiniteFormulaValuation.diagonal_negative_axiom 𝗣𝗔 S q hs hn
  have ht : TrueAt 𝗣𝗔 M v ((F 𝗣𝗔 M).map (prod.fst : P ⨯ N ⟶ P) q)
      ((F 𝗣𝗔 M).map (prod.snd ≫
        (NullaryInterpretation.atomFormula S ≫ S.negationConstructor)) q) := by
    apply (trueAt_lift 𝗣𝗔 M v prod.fst
      (prod.snd ≫ (NullaryInterpretation.atomFormula S ≫ S.negationConstructor)) q).mpr
    have he := frame_atom S true
    erw [he, Functor.map_comp_apply]
    exact h
  rw [Functor.map_comp_apply, hp, hx] at ht
  simpa only [Functor.map_comp_apply] using ht

end CategoricalEssentialIncompleteness.V46.ArithmeticSignedAtoms
