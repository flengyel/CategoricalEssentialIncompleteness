/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SignedDerivationTruthGeometry
public import CategoricalEssentialIncompleteness.V46ParameterizedBooleanModelTruth

/-! # Internal Boolean soundness of the original first-order proof algebra -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticLists

namespace CategoricalEssentialIncompleteness.V46.SignedDerivation
open SyntacticDerivation SyntacticDerivation.StandardInduction CoveredDerivationInvariant
open ParameterizedBooleanValuation
variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
variable (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
variable {V X A B : PredicateCategory T}
variable (S : CategoricalSyntax V (fun _ => ⊥_ (PredicateCategory T)) (fun _ => X) 0)
variable (axioms : A ⨿ B ⟶ S.sentenceObject)
variable (P : PredicateCategory T)
variable (d : constantFamily P X ⟶ constantFamily P (Two (PredicateCategory T)))
local notation "R" => firstOrderRules S.logicalAxioms S.sentenceInclusion axioms
  S.quantifierConstructor S.implicationConstructor
local notation "Q" => derivationAlgebra T R
local notation "supp" => positiveSupport T S.logicalAxioms S.sentenceInclusion axioms
  S.quantifierConstructor S.implicationConstructor
local notation "val" => value S P d
local notation "leaf" => positiveLeafAssignment T S.logicalParameters A B

/-- Internal soundness with explicit truth conditions on the assigned leaves.
The induction covers every actual proof code in the arithmetic model. -/
theorem truth_from_leaves (l : Obj T M P)
    (hleaf : ∀ a : Obj T M ((R).instances 0),
      ArithmeticFiniteCoverage.Covers ((F T M).map leaf a).val l.val →
        TrueAt T M val l ((F T M).map ((R).conclusion 0) a)) :
    ∀ q : Obj T M (Q).a.left,
      ArithmeticFiniteCoverage.Covers ((F T M).map supp q).val l.val →
        TrueAt T M val l ((F T M).map (Q).a.hom q) := by
  apply CoveredDerivationInvariant.model_rule_induction T M val l R supp
  intro i
  have hi : i = 0 ∨ i = 1 ∨ i = 2 := by fin_cases i <;> decide
  rcases hi with rfl | rfl | rfl
  · intro r ih hc
    let a : Obj T M ((R).instances 0) := (F T M).map
      (pullback.fst ((R).premises 0) (finitePowerMap (Q).a.hom 0)) r
    have hp : (F T M).map (nullaryDerivation T R) a =
        (F T M).map (derivationConstructor T R 0) r := by
      have h := congrArg (fun f => (F T M).map f r)
        (nullary_label_constructor T S.logicalAxioms S.sentenceInclusion axioms
          S.quantifierConstructor S.implicationConstructor)
      simp only [Functor.map_comp_apply] at h
      exact h
    have hs : ((F T M).map supp ((F T M).map (derivationConstructor T R 0) r)).val =
        ((F T M).map leaf a).val := by
      rw [← hp]
      have h := ConcreteNamedComparison.parameterPoint_diagram T M
        (nullaryDerivation T R) supp (𝟙 _) leaf
        (by simpa only [Category.id_comp] using
          (canonical_nullary_collect T S.logicalAxioms S.sentenceInclusion axioms
            S.quantifierConstructor S.implicationConstructor)) a
      simp only [Functor.map_id_apply] at h
      exact congrArg Subtype.val h
    have hcon : (F T M).map (Q).a.hom
        ((F T M).map (derivationConstructor T R 0) r) =
        (F T M).map ((R).conclusion 0) a := by
      rw [← hp]
      exact ConcreteNamedComparison.parameterPoint_diagram T M
        (nullaryDerivation T R) (Q).a.hom (𝟙 _) ((R).conclusion 0)
        (by simpa only [Category.id_comp] using nullaryDerivation_conclusion T R) a
        |>.trans (by rw [Functor.map_id_apply])
    erw [hs] at hc
    exact hcon.symm ▸ hleaf a hc
  · intro r ih hc
    have hs := unary_support_value T S.logicalAxioms S.sentenceInclusion axioms
      S.quantifierConstructor S.implicationConstructor r
    erw [hs] at hc
    have ht := ih (0 : Fin 1) hc
    obtain ⟨w, hp, hr⟩ := modelProduct_exists T M P ((R).ruleObject (Q).a 1) l r
    let p : P ⨯ (R).ruleObject (Q).a 1 ⟶ P := prod.fst
    let a : P ⨯ (R).ruleObject (Q).a 1 ⟶ V ⨯ S.algebra.a.2 :=
      prod.snd ≫ pullback.fst ((R).premises 1) (finitePowerMap (Q).a.hom 1)
    have hbody : (F T M).map (a ≫ prod.snd) w =
        (F T M).map (Q).a.hom ((F T M).map (typedChild T R (1 : Fin 3) (0 : Fin 1)) r) := by
      have he := ConcreteNamedComparison.parameterPoint_diagram T M
        (typedChild T R (1 : Fin 3) (0 : Fin 1)) (Q).a.hom
        (pullback.fst ((R).premises 1) (finitePowerMap (Q).a.hom 1)) prod.snd
        (unary_child_conclusion T S.logicalAxioms S.sentenceInclusion axioms
          S.quantifierConstructor S.implicationConstructor) r
      dsimp only [a]
      rw [Category.assoc, Functor.map_comp_apply, hr, Functor.map_comp_apply]
      exact he.symm
    have hf : (F T M).map (evaluate S P d p (a ≫ prod.snd)) w =
        (F T M).map (Two.constant _ true) w := by
      apply (trueAt_lift T M val p (a ≫ prod.snd) w).mp
      rw [hbody]
      have hp' : (F T M).map p w = l := hp
      rw [hp']
      exact ht
    have hout := ParameterizedBooleanModelTruth.generalization_point T M S P d p
      (a ≫ prod.fst) (a ≫ prod.snd) w hf
    have he : prod.lift (a ≫ prod.fst) (a ≫ prod.snd) ≫ S.quantifierConstructor =
        prod.snd ≫ derivationConstructor T R 1 ≫ (Q).a.hom := by
      rw [← prod.comp_lift, prod.lift_fst_snd, Category.comp_id]
      dsimp only [a]
      rw [unary_parent_conclusion]
      exact Category.assoc _ _ _
    rw [he] at hout
    have htrue := (trueAt_lift T M val p
      (prod.snd ≫ derivationConstructor T R 1 ≫ (Q).a.hom) w).mpr hout
    simp only [p, Functor.map_comp_apply, hp, hr] at htrue
    exact htrue
  · intro r ih hc
    have hs := binary_support_value T S.logicalAxioms S.sentenceInclusion axioms
      S.quantifierConstructor S.implicationConstructor r
    erw [hs, ArithmeticFiniteCoverage.covers_append] at hc
    have h₀ := ih (0 : Fin 2) hc.1
    have h₁ := ih (1 : Fin 2) hc.2
    obtain ⟨w, hp, hr⟩ := modelProduct_exists T M P ((R).ruleObject (Q).a 2) l r
    let p : P ⨯ (R).ruleObject (Q).a 2 ⟶ P := prod.fst
    let a : P ⨯ (R).ruleObject (Q).a 2 ⟶ S.algebra.a.2 ⨯ S.algebra.a.2 :=
      prod.snd ≫ pullback.fst ((R).premises 2) (finitePowerMap (Q).a.hom 2)
    have hfirst : (F T M).map (a ≫ prod.fst) w =
        (F T M).map (Q).a.hom ((F T M).map (typedChild T R (2 : Fin 3) (0 : Fin 2)) r) := by
      have he := ConcreteNamedComparison.parameterPoint_diagram T M
        (typedChild T R (2 : Fin 3) (0 : Fin 2)) (Q).a.hom
        (pullback.fst ((R).premises 2) (finitePowerMap (Q).a.hom 2)) prod.fst
        (binary_first_child_conclusion T S.logicalAxioms S.sentenceInclusion axioms
          S.quantifierConstructor S.implicationConstructor) r
      dsimp only [a]
      rw [Category.assoc, Functor.map_comp_apply, hr, Functor.map_comp_apply]
      exact he.symm
    have himp : (F T M).map (a ≫ S.implicationConstructor) w =
        (F T M).map (Q).a.hom ((F T M).map (typedChild T R (2 : Fin 3) (1 : Fin 2)) r) := by
      have he := ConcreteNamedComparison.parameterPoint_diagram T M
        (typedChild T R (2 : Fin 3) (1 : Fin 2)) (Q).a.hom
        (pullback.fst ((R).premises 2) (finitePowerMap (Q).a.hom 2)) S.implicationConstructor
        (binary_second_child_conclusion T S.logicalAxioms S.sentenceInclusion axioms
          S.quantifierConstructor S.implicationConstructor) r
      dsimp only [a]
      rw [Category.assoc, Functor.map_comp_apply, hr, Functor.map_comp_apply]
      exact he.symm
    have hf : (F T M).map (evaluate S P d p (a ≫ prod.fst)) w =
        (F T M).map (Two.constant _ true) w := by
      apply (trueAt_lift T M val p (a ≫ prod.fst) w).mp
      rw [hfirst]
      have hp' : (F T M).map p w = l := hp
      rw [hp']
      exact h₀
    have hi : (F T M).map
        (evaluate S P d p (prod.lift (a ≫ prod.fst) (a ≫ prod.snd) ≫ S.implicationConstructor)) w =
        (F T M).map (Two.constant _ true) w := by
      rw [← prod.comp_lift, prod.lift_fst_snd, Category.comp_id]
      apply (trueAt_lift T M val p (a ≫ S.implicationConstructor) w).mp
      rw [himp]
      have hp' : (F T M).map p w = l := hp
      rw [hp']
      exact h₁
    have hout := ParameterizedBooleanModelTruth.modus_ponens_point T M S P d p
      (a ≫ prod.fst) (a ≫ prod.snd) w hf hi
    have he : a ≫ prod.snd = prod.snd ≫ derivationConstructor T R 2 ≫ (Q).a.hom := by
      dsimp only [a]
      rw [binary_parent_conclusion]
      exact Category.assoc _ _ _
    rw [he] at hout
    have htrue := (trueAt_lift T M val p
      (prod.snd ≫ derivationConstructor T R 2 ≫ (Q).a.hom) w).mpr hout
    simp only [p, Functor.map_comp_apply, hp, hr] at htrue
    exact htrue

end CategoricalEssentialIncompleteness.V46.SignedDerivation
