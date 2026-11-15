/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46CoveredDerivationInvariant
public import CategoricalEssentialIncompleteness.V46SignedDerivationFiniteSupport
public import CategoricalEssentialIncompleteness.V46ConcreteNamedComparisonLists
public import CategoricalEssentialIncompleteness.V46ConcreteNamedComparisonParameterPoints

/-! # Support and conclusion coordinates of the original signed rules -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticLists

namespace CategoricalEssentialIncompleteness.V46.SignedDerivation
open SyntacticDerivation SyntacticDerivation.StandardInduction
variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
variable {L A B V S Fm : PredicateCategory T}
variable (logical : L ⟶ Fm) (sentence : S ⟶ Fm) (axioms : A ⨿ B ⟶ S)
variable (all : V ⨯ Fm ⟶ Fm) (imp : Fm ⨯ Fm ⟶ Fm)
local notation "R" => firstOrderRules logical sentence axioms all imp
local notation "P" => derivationAlgebra T R
local notation "K" => stableListAlgebra T A
local notation "supp" => positiveSupport T logical sentence axioms all imp

@[simp] theorem unary_child :
    typedChild T R (1 : Fin 3) (0 : Fin 1) = pullback.snd ((R).premises 1) (finitePowerMap (P).a.hom 1) := by
  change pullback.snd ((R).premises 1) (finitePowerMap (P).a.hom 1) ≫
    (𝟙 (P).a.left ≫ 𝟙 (P).a.left) = _
  erw [Category.id_comp, Category.comp_id]

@[simp] theorem binary_first_child :
    typedChild T R (2 : Fin 3) (0 : Fin 2) =
      pullback.snd ((R).premises 2) (finitePowerMap (P).a.hom 2) ≫ prod.fst := by
  change pullback.snd ((R).premises 2) (finitePowerMap (P).a.hom 2) ≫
    (prod.map (𝟙 (P).a.left) (𝟙 (P).a.left) ≫ (prod.fst ≫ 𝟙 (P).a.left)) = _
  erw [prod.map_id_id, Category.id_comp, Category.comp_id]
  rfl

@[simp] theorem binary_second_child :
    typedChild T R (2 : Fin 3) (1 : Fin 2) =
      pullback.snd ((R).premises 2) (finitePowerMap (P).a.hom 2) ≫ prod.snd := by
  change pullback.snd ((R).premises 2) (finitePowerMap (P).a.hom 2) ≫
    (prod.map (𝟙 (P).a.left) (𝟙 (P).a.left) ≫ prod.snd) = _
  erw [prod.map_id_id, Category.id_comp]
  rfl

@[reassoc] theorem unary_child_conclusion :
    typedChild T R (1 : Fin 3) (0 : Fin 1) ≫ (P).a.hom =
      pullback.fst ((R).premises 1) (finitePowerMap (P).a.hom 1) ≫ prod.snd := by
  rw [unary_child]
  exact (pullback.condition (f := (R).premises 1) (g := finitePowerMap (P).a.hom 1)).symm

@[reassoc] theorem binary_first_child_conclusion :
    typedChild T R (2 : Fin 3) (0 : Fin 2) ≫ (P).a.hom =
      pullback.fst ((R).premises 2) (finitePowerMap (P).a.hom 2) ≫ prod.fst := by
  rw [binary_first_child]
  have hc : pullback.fst ((R).premises 2) (finitePowerMap (P).a.hom 2) ≫
      prod.lift (prod.fst : Fm ⨯ Fm ⟶ Fm) imp =
      pullback.snd ((R).premises 2) (finitePowerMap (P).a.hom 2) ≫
        prod.map (P).a.hom (P).a.hom := pullback.condition
  have h := congrArg (fun f => f ≫ (prod.fst : Fm ⨯ Fm ⟶ Fm)) hc
  simpa only [Category.assoc, prod.lift_fst, prod.map_fst] using h.symm

@[reassoc] theorem binary_second_child_conclusion :
    typedChild T R (2 : Fin 3) (1 : Fin 2) ≫ (P).a.hom =
      pullback.fst ((R).premises 2) (finitePowerMap (P).a.hom 2) ≫ imp := by
  rw [binary_second_child]
  have hc : pullback.fst ((R).premises 2) (finitePowerMap (P).a.hom 2) ≫
      prod.lift (prod.fst : Fm ⨯ Fm ⟶ Fm) imp =
      pullback.snd ((R).premises 2) (finitePowerMap (P).a.hom 2) ≫
        prod.map (P).a.hom (P).a.hom := pullback.condition
  have h := congrArg (fun f => f ≫ (prod.snd : Fm ⨯ Fm ⟶ Fm)) hc
  simpa only [Category.assoc, prod.lift_snd, prod.map_snd] using h.symm

@[reassoc] theorem unary_parent_conclusion :
    derivationConstructor T R 1 ≫ (P).a.hom =
      pullback.fst ((R).premises 1) (finitePowerMap (P).a.hom 1) ≫ all := by
  rw [derivationConstructor_conclusion]
  rfl

@[reassoc] theorem binary_parent_conclusion :
    derivationConstructor T R 2 ≫ (P).a.hom =
      pullback.fst ((R).premises 2) (finitePowerMap (P).a.hom 2) ≫ prod.snd := by
  rw [derivationConstructor_conclusion]
  rfl

/-- The nullary matching pullback adds no data to a rule label. -/
@[reassoc] theorem nullary_label_constructor :
    pullback.fst ((R).premises 0) (finitePowerMap (P).a.hom 0) ≫ nullaryDerivation T R =
      derivationConstructor T R 0 := by
  have h : pullback.fst ((R).premises 0) (finitePowerMap (P).a.hom 0) ≫
      (R).nullaryRule (P).a = 𝟙 _ := by
    apply pullback.hom_ext
    · simp [Category.assoc, RulePresentation.nullaryRule]
    · exact terminal.hom_ext _ _
  rw [nullaryDerivation, ← Category.assoc, h, Category.id_comp]

variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

omit [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] in
/-- Generalization retains exactly the child's positive support. -/
theorem unary_support_value
    (r : Obj T M ((R).ruleObject (P).a 1)) :
    ((F T M).map supp ((F T M).map (derivationConstructor T R 1) r)).val =
      ((F T M).map supp ((F T M).map (typedChild T R (1 : Fin 3) (0 : Fin 1)) r)).val := by
  have h : derivationConstructor T R 1 ≫ supp = typedChild T R (1 : Fin 3) (0 : Fin 1) ≫ supp := by
    rw [unary_child]
    exact canonical_unary_collect T logical sentence axioms all imp
  exact congrArg Subtype.val (ConcreteNamedComparison.parameterPoint_diagram T M
    (derivationConstructor T R 1) supp (typedChild T R (1 : Fin 3) (0 : Fin 1)) supp h r)

/-- The binary node concatenates the two ordered children's supports. -/
theorem binary_support_value
    (r : Obj T M ((R).ruleObject (P).a 2)) :
    ((F T M).map supp ((F T M).map (derivationConstructor T R 2) r)).val =
      SyntacticSyntax.Words.append
        ((F T M).map supp ((F T M).map (typedChild T R (2 : Fin 3) (0 : Fin 2)) r)).val
        ((F T M).map supp ((F T M).map (typedChild T R (2 : Fin 3) (1 : Fin 2)) r)).val := by
  have h : derivationConstructor T R 2 ≫ supp =
      prod.lift (typedChild T R (2 : Fin 3) (0 : Fin 2) ≫ supp)
        (typedChild T R (2 : Fin 3) (1 : Fin 2) ≫ supp) ≫ (K).append := by
    rw [canonical_binary_collect, binary_first_child, binary_second_child]
    have hh : pullback.snd ((R).premises 2) (finitePowerMap (P).a.hom 2) ≫
        prod.map supp supp =
      prod.lift ((pullback.snd ((R).premises 2) (finitePowerMap (P).a.hom 2) ≫ prod.fst) ≫ supp)
        ((pullback.snd ((R).premises 2) (finitePowerMap (P).a.hom 2) ≫ prod.snd) ≫ supp) := by
      apply prod.hom_ext
      · erw [Category.assoc, prod.map_fst, prod.lift_fst]
        exact (Category.assoc _ _ _).symm
      · erw [Category.assoc, prod.map_snd, prod.lift_snd]
        exact (Category.assoc _ _ _).symm
    exact (Category.assoc _ _ _).symm.trans (congrArg (fun f => f ≫ (K).append) hh)
  have he := congrArg Subtype.val (ConcreteNamedComparison.parameterPoint_diagram T M
    (derivationConstructor T R 2) supp
    (prod.lift (typedChild T R (2 : Fin 3) (0 : Fin 2) ≫ supp)
      (typedChild T R (2 : Fin 3) (1 : Fin 2) ≫ supp)) (K).append h r)
  rw [ConcreteNamedComparison.append_value] at he
  erw [ConcreteNamedComparison.model_lift_fst, ConcreteNamedComparison.model_lift_snd] at he
  simp only [Functor.map_comp_apply] at he
  exact he

end CategoricalEssentialIncompleteness.V46.SignedDerivation
