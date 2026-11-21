/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46LogicalSchemes
public import CategoricalEssentialIncompleteness.V46NamedBooleanReflection
public import CategoricalEssentialIncompleteness.V46ConcreteNamedComparisonMembership
public import CategoricalEssentialIncompleteness.V46ConcreteNamedComparisonPlainOccurrences
public import CategoricalEssentialIncompleteness.V46SyntacticNamedHilbertOperations

/-! # The distribution parameter fiber in every arithmetic model -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticLists
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax
namespace CategoricalEssentialIncompleteness.V46.NumericalArithmetic.DistributionModels
open ConcreteNamedComparison
variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
  (V : PredicateCategory T) (σ π : ℕ → PredicateCategory T) (d : ℕ)
  (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
local notation "S" => plainCategoricalSyntax T V σ π d
local notation "Y" => (Postfix.plainCarrier true
  (SyntaxPolynomial.termExpression V σ d) (SyntaxPolynomial.formulaExpression V π d) : PredicateCategory T)
local notation "G" => F T M
local notation "B" => V ⨯ (Y ⨯ Y)

private def names : B ⟶ V ⨯ listObject T V :=
  prod.lift prod.fst (prod.snd ≫ prod.fst ≫ (S).formulaOccurrences)

/-- The categorical membership test is reflected by its numerical flag,
with the original name and the first formula in their original order. -/
theorem absence_iff (q : Obj T M B) :
    (G).map (S).distributionAbsence q = (G).map (Two.constant B false) q ↔
      ConcreteNamedSubstitution.member
        ((G).map (prod.fst (C := PredicateCategory T) : B ⟶ V) q).val
        (ConcreteNamedSubstitution.freeVariables (M := M) V σ π d
          ((G).map (prod.fst (C := PredicateCategory T) («X» := Y) («Y» := Y))
            ((G).map (prod.snd (C := PredicateCategory T) : B ⟶ Y ⨯ Y) q)).val) = 0 := by
  let z := (G).map (names T V σ π d) q
  have hc := model_constant_comp T M (names T V σ π d) q false
  have hm := membershipArrow_point_iff T M V z false
  have hx : ((G).map (prod.fst (C := PredicateCategory T) : V ⨯ listObject T V ⟶ V) z).val =
      ((G).map (prod.fst (C := PredicateCategory T) : B ⟶ V) q).val := by
    exact congrArg Subtype.val (model_lift_fst T M _ _ q)
  have hf : ((G).map (prod.snd (C := PredicateCategory T) : V ⨯ listObject T V ⟶ listObject T V) z).val =
      ConcreteNamedSubstitution.freeVariables (M := M) V σ π d
        ((G).map (prod.fst (C := PredicateCategory T) («X» := Y) («Y» := Y))
          ((G).map (prod.snd (C := PredicateCategory T) : B ⟶ Y ⨯ Y) q)).val := by
    exact (congrArg Subtype.val (model_lift_snd T M _ _ q)).trans
      ((congrArg Subtype.val ((G).map_comp_apply
        (prod.snd (C := PredicateCategory T) : B ⟶ Y ⨯ Y) ((prod.fst (C := PredicateCategory T) («X» := Y) («Y» := Y)) ≫ (S).formulaOccurrences) q)).trans
        ((congrArg Subtype.val ((G).map_comp_apply (prod.fst (C := PredicateCategory T) («X» := Y) («Y» := Y))
          (S).formulaOccurrences ((G).map (prod.snd (C := PredicateCategory T) : B ⟶ Y ⨯ Y) q))).trans
            (ConcreteNamedComparison.plain_formulaOccurrences_value T V σ π d M _)))
  have he : (G).map (S).distributionAbsence q = (G).map (membershipArrow T V) z := by
    change (G).map (names T V σ π d ≫ (S).lists.membership (S).decidableVariables) q = _
    have hj : (S).lists.membership (S).decidableVariables = membershipArrow T V :=
      (membershipArrow_eq T V).symm
    exact (congrArg (fun f : @Quiver.Hom (PredicateCategory T) inferInstance
      (V ⨯ listObject T V) (Two (PredicateCategory T)) =>
        (G).map (names T V σ π d ≫ f) q) hj).trans
          ((G).map_comp_apply (names T V σ π d) (membershipArrow T V) q)
  constructor
  · intro h
    have hm' := hm.mp (he.symm.trans (h.trans hc.symm))
    simpa only [hx,hf,Bool.false_eq_true,ite_false] using hm'
  · intro h
    have h' : ConcreteNamedSubstitution.member
        ((G).map (prod.fst (C := PredicateCategory T) : V ⨯ listObject T V ⟶ V) z).val
        ((G).map (prod.snd (C := PredicateCategory T) : V ⨯ listObject T V ⟶ listObject T V) z).val =
          if false then (1 : M) else 0 := by
      simpa only [hx,hf,Bool.false_eq_true,ite_false] using h
    exact he.trans ((hm.mpr h').trans hc)

/-- No extra witness is appended to a distribution label. The label is
the point of its prescribed Boolean fiber, including nonstandard points. -/
theorem parameter_image_iff (q : Obj T M B) :
    (∃ r : Obj T M (S).distributionParameters,
      (G).map (S).distributionInclusion r = q) ↔
      ConcreteNamedSubstitution.member
        ((G).map (prod.fst (C := PredicateCategory T) : B ⟶ V) q).val
        (ConcreteNamedSubstitution.freeVariables (M := M) V σ π d
          ((G).map (prod.fst (C := PredicateCategory T) («X» := Y) («Y» := Y))
            ((G).map (prod.snd (C := PredicateCategory T) : B ⟶ Y ⨯ Y) q)).val) = 0 := by
  rw [← absence_iff T V σ π d M q]
  constructor
  · rintro ⟨r,rfl⟩
    have h := congrArg (fun f => (G).map f r) (S).distribution_absence
    rw [CategoryTheory.Functor.map_comp_apply] at h
    exact h.trans (model_constant_comp T M (S).distributionInclusion r false).symm
  · intro h
    exact SyntacticNamedHilbert.booleanFiber_point_exists T M (S).distributionAbsence false q h

end CategoricalEssentialIncompleteness.V46.NumericalArithmetic.DistributionModels
