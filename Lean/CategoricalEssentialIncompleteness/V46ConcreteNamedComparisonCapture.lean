/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ConcreteNamedComparisonOccurrences
public import CategoricalEssentialIncompleteness.V46ConcreteNamedComparisonMembership
public import CategoricalEssentialIncompleteness.V46NamedBooleanReflection

/-! # The capture classifier reflects the numerical absence test -/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticLists
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax

namespace CategoricalEssentialIncompleteness.V46.ConcreteNamedComparison
variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
variable (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
local instance namedComparisonCaptureModelDecidableEq : DecidableEq M := Classical.decEq M

theorem membership_lift_point {X : PredicateCategory T} (V : PredicateCategory T)
    (x : X ⟶ V) (f : X ⟶ listObject T V) (q : Obj T M X) (b : Bool)
    (hb : ConcreteNamedSubstitution.member ((F T M).map x q).val ((F T M).map f q).val =
      if b then 1 else 0) :
    (F T M).map (prod.lift x f ≫ membershipArrow T V) q =
      (F T M).map (Two.constant X b) q := by
  let z := (F T M).map (prod.lift x f) q
  have hz : ConcreteNamedSubstitution.member
      ((F T M).map (prod.fst : V ⨯ listObject T V ⟶ V) z).val
      ((F T M).map (prod.snd : V ⨯ listObject T V ⟶ _) z).val = if b then 1 else 0 := by
    erw [model_lift_fst T M x f q,model_lift_snd T M x f q]
    exact hb
  exact (by simpa only [Functor.map_comp_apply] using
    (membershipArrow_point T M V z b hz).trans (model_constant_comp T M (prod.lift x f) q b))

def absenceOr {X : PredicateCategory T} (V : PredicateCategory T)
    (x y : X ⟶ V) (body replacement : X ⟶ listObject T V) : X ⟶ Two (PredicateCategory T) :=
  Two.binary Bool.or
    (Two.unary Bool.not (prod.lift x body ≫ membershipArrow T V))
    (Two.unary Bool.not (prod.lift y replacement ≫ membershipArrow T V))

/-- The finite truth-table calculation remains opaque in its four input morphisms.
Concrete syntax/product graphs are not unfolded under the conditional. -/
theorem absenceOr_point {X : PredicateCategory T} (V : PredicateCategory T)
    (x y : X ⟶ V) (body replacement : X ⟶ listObject T V) (q : Obj T M X) :
    (F T M).map (absenceOr T V x y body replacement) q =
      (F T M).map (Two.constant X
        (if ConcreteNamedSubstitution.member ((F T M).map x q).val ((F T M).map body q).val = 0 ∨
          ConcreteNamedSubstitution.member ((F T M).map y q).val ((F T M).map replacement q).val = 0
          then true else false)) q := by
  obtain ⟨a,ha⟩ : ∃ a : Bool,
      ConcreteNamedSubstitution.member ((F T M).map x q).val ((F T M).map body q).val =
        if a then 1 else 0 := by
    rcases ConcreteNamedSubstitution.member_boolean
      ((F T M).map x q).val ((F T M).map body q).val with h | h
    · exact ⟨false,h⟩
    · exact ⟨true,h⟩
  obtain ⟨b,hb⟩ : ∃ b : Bool,
      ConcreteNamedSubstitution.member ((F T M).map y q).val ((F T M).map replacement q).val =
        if b then 1 else 0 := by
    rcases ConcreteNamedSubstitution.member_boolean
      ((F T M).map y q).val ((F T M).map replacement q).val with h | h
    · exact ⟨false,h⟩
    · exact ⟨true,h⟩
  have hx := model_unary T M Bool.not (prod.lift x body ≫ membershipArrow T V) q a
    (membership_lift_point T M V x body q a ha)
  have hy := model_unary T M Bool.not (prod.lift y replacement ≫ membershipArrow T V) q b
    (membership_lift_point T M V y replacement q b hb)
  have h := model_binary T M Bool.or
    (Two.unary Bool.not (prod.lift x body ≫ membershipArrow T V))
    (Two.unary Bool.not (prod.lift y replacement ≫ membershipArrow T V)) q (!a) (!b) hx hy
  change (F T M).map (absenceOr T V x y body replacement) q = _ at h
  have hbool : (Bool.or (!a) (!b)) =
      (if ConcreteNamedSubstitution.member ((F T M).map x q).val ((F T M).map body q).val = 0 ∨
        ConcreteNamedSubstitution.member ((F T M).map y q).val ((F T M).map replacement q).val = 0
        then true else false) := by
    cases a <;> cases b <;> simp_all
  exact h.trans (congrArg (fun c => (F T M).map (Two.constant X c) q) hbool)

variable (V : PredicateCategory T) (σ π : ℕ → PredicateCategory T) (d : ℕ)

theorem captureAllowed_point
    (q : Obj T M ((categoricalSyntax T V σ π d).substitutionParameters ⨯
      (V ⨯ (categoricalSyntax T V σ π d).substitutionCarriers.2))) :
    (F T M).map (categoricalSyntax T V σ π d).captureAllowed q =
      (F T M).map (Two.constant _
        (if ConcreteNamedSubstitution.member
            ((F T M).map (prod.fst ≫ prod.fst) q).val
            (ConcreteNamedSubstitution.freeVariables V σ π d
              ((F T M).map (prod.snd ≫ prod.snd ≫ prod.fst) q).val) = 0 ∨
          ConcreteNamedSubstitution.member
            ((F T M).map (prod.snd ≫ prod.fst) q).val
            (ConcreteNamedSubstitution.freeVariables V σ π d
              ((F T M).map (prod.fst ≫ prod.snd) q).val) = 0
          then true else false)) q := by
  let S := categoricalSyntax T V σ π d
  let x := (prod.fst ≫ prod.fst : S.substitutionParameters ⨯ (V ⨯ S.substitutionCarriers.2) ⟶ V)
  let y := (prod.snd ≫ prod.fst : S.substitutionParameters ⨯ (V ⨯ S.substitutionCarriers.2) ⟶ V)
  let body := (prod.snd ≫ prod.snd ≫ prod.fst :
    S.substitutionParameters ⨯ (V ⨯ S.substitutionCarriers.2) ⟶ S.algebra.a.2)
  let replacement := (prod.fst ≫ prod.snd :
    S.substitutionParameters ⨯ (V ⨯ S.substitutionCarriers.2) ⟶ S.algebra.a.1)
  have h := absenceOr_point T M V x y (body ≫ S.formulaOccurrences) (replacement ≫ S.termOccurrences) q
  have he : S.captureAllowed = absenceOr T V x y
      (body ≫ S.formulaOccurrences) (replacement ≫ S.termOccurrences) := by
    have hm : S.lists.membership S.decidableVariables = membershipArrow T V :=
      (membershipArrow_eq T V).symm
    dsimp only [x,y,body,replacement]
    simp only [CategoricalSyntax.captureAllowed,absenceOr,hm,Category.assoc]
    all_goals rfl

  erw [he]
  have hb : ((F T M).map (body ≫ S.formulaOccurrences) q).val =
      ConcreteNamedSubstitution.freeVariables V σ π d ((F T M).map body q).val := by
    erw [Functor.map_comp_apply]
    exact formulaOccurrences_value T V σ π d M _
  have ht : ((F T M).map (replacement ≫ S.termOccurrences) q).val =
      ConcreteNamedSubstitution.freeVariables V σ π d ((F T M).map replacement q).val := by
    erw [Functor.map_comp_apply]
    exact termOccurrences_value T V σ π d M _
  erw [hb,ht] at h
  exact h

end CategoricalEssentialIncompleteness.V46.ConcreteNamedComparison
