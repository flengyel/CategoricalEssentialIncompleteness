/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ConcreteNamedComparisonBooleans

/-! # Reflection of literal membership by the Boolean comparison -/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.Limits
open FailureOfComposition.ProofSearch FailureOfComposition.CodedObjectMembership
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticLists
namespace CategoricalEssentialIncompleteness.V46.ConcreteNamedComparison
variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
variable (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

/-- The chosen categorical truth-value point reflects, as well as
preserves, the numerical membership result. -/
theorem membershipArrow_point_iff (V : PredicateCategory T)
    (q : Obj T M (V ⨯ listObject T V)) (b : Bool) :
    (F T M).map (membershipArrow T V) q =
        (F T M).map (Two.constant (V ⨯ listObject T V) b) q ↔
      ConcreteNamedSubstitution.member
        ((F T M).map (prod.fst : V ⨯ listObject T V ⟶ V) q).val
        ((F T M).map (prod.snd : V ⨯ listObject T V ⟶ listObject T V) q).val =
          if b then 1 else 0 := by
  constructor
  · intro h
    have hr : (F T M).map (rawMembership T V) q =
        (F T M).map (rawBooleanConstant T (V ⨯ listObject T V) b) q := by
      apply ((F T M).mapIso (SyntacticDecidableVariables.booleanIso T)).toEquiv.injective
      change (F T M).map (SyntacticDecidableVariables.booleanIso T).hom
          ((F T M).map (rawMembership T V) q) =
        (F T M).map (SyntacticDecidableVariables.booleanIso T).hom
          ((F T M).map (rawBooleanConstant T (V ⨯ listObject T V) b) q)
      rw [← Functor.map_comp_apply,← Functor.map_comp_apply,rawBooleanConstant_iso]
      exact h
    have hv := congrArg Subtype.val hr
    rw [rawMembership_value,rawBooleanConstant_value] at hv
    exact ((pair_eq_pair_iff _ _ _ _).mp hv).2
  · exact membershipArrow_point T M V q b

end CategoricalEssentialIncompleteness.V46.ConcreteNamedComparison
