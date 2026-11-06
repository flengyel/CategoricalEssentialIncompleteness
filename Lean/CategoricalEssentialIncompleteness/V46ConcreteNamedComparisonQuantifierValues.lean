/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46ConcreteNamedComparisonCapture
import CategoricalEssentialIncompleteness.V46ConcreteNamedComparisonCanonicalCoordinates
import CategoricalEssentialIncompleteness.V46ConcreteNamedComparisonOptionBranches

/-! # The actual quantifier conditional uses originals and propagates genuine options -/

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
variable (V : PredicateCategory T) (σ π : ℕ → PredicateCategory T) (d : ℕ)
variable (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
local instance namedComparisonQuantifierValuesDecidableEq : DecidableEq M := Classical.decEq M
local notation "S" => categoricalSyntax T V σ π d
local notation "P" => CategoricalSyntax.substitutionParameters (categoricalSyntax T V σ π d)
local notation "Y" => (syntaxCarrier V σ π d true : PredicateCategory T)
local notation "Q" => P ⨯ (V ⨯ Prod.snd (CategoricalSyntax.substitutionCarriers (categoricalSyntax T V σ π d)))

theorem quantifierSubstitutionResult_value (q : Obj T M Q) :
    let x := ((F T M).map (prod.fst ≫ prod.fst : Q ⟶ V) q).val
    let y := ((F T M).map (prod.snd ≫ prod.fst : Q ⟶ V) q).val
    let old := ((F T M).map (prod.snd ≫ prod.snd ≫ prod.fst : Q ⟶ Y) q).val
    let replacement := ((F T M).map (prod.fst ≫ prod.snd : Q ⟶ (S).algebra.a.1) q).val
    let child := (F T M).map (prod.snd ≫ prod.snd ≫ prod.snd : Q ⟶ OptionSyntax.obj Y) q
    optionCode T M Y ((F T M).map (S).quantifierSubstitutionResult q) =
      if y = x then ConcreteNamedSubstitution.ok
        (Coding.constructor true (SyntaxPolynomial.formulaExpression V π d)
          (quantifierInput (Arithmetic.pair y old)))
      else if (ConcreteNamedSubstitution.member x (ConcreteNamedSubstitution.freeVariables V σ π d old) = 0 ∨
          ConcreteNamedSubstitution.member y (ConcreteNamedSubstitution.freeVariables V σ π d replacement) = 0) ∧
          π₂ (optionCode T M Y child) = 1 then
        ConcreteNamedSubstitution.ok (Coding.constructor true (SyntaxPolynomial.formulaExpression V π d)
          (quantifierInput (Arithmetic.pair y (π₁ (optionCode T M Y child))))) else 0 := by
  let x := ((F T M).map (prod.fst ≫ prod.fst : Q ⟶ V) q).val
  let y := ((F T M).map (prod.snd ≫ prod.fst : Q ⟶ V) q).val
  let old := ((F T M).map (prod.snd ≫ prod.snd ≫ prod.fst : Q ⟶ Y) q).val
  let replacement := ((F T M).map (prod.fst ≫ prod.snd : Q ⟶ (S).algebra.a.1) q).val
  let child := (F T M).map (prod.snd ≫ prod.snd ≫ prod.snd : Q ⟶ OptionSyntax.obj Y) q
  let allowed := ConcreteNamedSubstitution.member x (ConcreteNamedSubstitution.freeVariables V σ π d old) = 0 ∨
    ConcreteNamedSubstitution.member y (ConcreteNamedSubstitution.freeVariables V σ π d replacement) = 0
  change optionCode T M Y ((F T M).map (S).quantifierSubstitutionResult q) =
    if y = x then ConcreteNamedSubstitution.ok
      (Coding.constructor true (SyntaxPolynomial.formulaExpression V π d)
        (quantifierInput (Arithmetic.pair y old)))
    else if allowed ∧ π₂ (optionCode T M Y child) = 1 then
      ConcreteNamedSubstitution.ok (Coding.constructor true (SyntaxPolynomial.formulaExpression V π d)
        (quantifierInput (Arithmetic.pair y (π₁ (optionCode T M Y child))))) else 0
  let names := (prod.lift (prod.snd ≫ prod.fst) (prod.fst ≫ prod.fst) : Q ⟶ V ⨯ V)
  have heq (b : Bool) (hb : (y = x) ↔ b = true) :
      (F T M).map (S).quantifierEquality q = (F T M).map (Two.constant Q b) q := by
    apply equalityTest_comp_point T M V names q b
    erw [model_lift_fst T M,model_lift_snd T M]
    exact hb
  have hcap := captureAllowed_point T M V σ π d q
  change (F T M).map (S).captureAllowed q =
    (F T M).map (Two.constant Q (if allowed then true else false)) q at hcap
  have hold : ((F T M).map (S).quantifierOriginal q).val =
      Coding.constructor true (SyntaxPolynomial.formulaExpression V π d)
        (quantifierInput (Arithmetic.pair y old)) := by
    change ((F T M).map (prod.lift (prod.snd ≫ prod.fst)
      (prod.snd ≫ prod.snd ≫ prod.fst) ≫ (S).quantifierConstructor) q).val = _
    rw [Functor.map_comp_apply]
    erw [CanonicalOperations.quantifier_value T M V σ π d,
      model_lift_fst T M,model_lift_snd T M]
    rfl
  let input := (prod.lift (prod.snd ≫ prod.fst) (prod.snd ≫ prod.snd ≫ prod.snd) :
    Q ⟶ V ⨯ OptionSyntax.obj Y)
  have hgood := optionCode_coefficient T M (S).quantifierConstructor
    (fun y body => Coding.constructor true (SyntaxPolynomial.formulaExpression V π d)
      (quantifierInput (Arithmetic.pair y body)))
    (fun z => CanonicalOperations.quantifier_value T M V σ π d z) ((F T M).map input q)
  erw [model_lift_fst T M,model_lift_snd T M] at hgood
  have hgood' : optionCode T M Y ((F T M).map (input ≫ OptionSyntax.coefficient (S).quantifierConstructor) q) =
      if π₂ (optionCode T M Y child) = 1 then
        ConcreteNamedSubstitution.ok (Coding.constructor true (SyntaxPolynomial.formulaExpression V π d)
          (quantifierInput (Arithmetic.pair y (π₁ (optionCode T M Y child))))) else 0 := by
    rw [Functor.map_comp_apply]
    by_cases hs : π₂ (optionCode T M Y child) = 1
    · erw [ite_eq_left hs] at hgood
      rw [ite_eq_left hs]
      convert hgood using 1 <;> rfl
    · erw [ite_eq_right hs] at hgood
      rw [ite_eq_right hs]
      convert hgood using 1
      rfl
  let other := Two.branch (S).captureAllowed OptionSyntax.fail
    (input ≫ OptionSyntax.coefficient (S).quantifierConstructor)
  have houter : (S).quantifierSubstitutionResult =
      Two.branch (S).quantifierEquality other ((S).quantifierOriginal ≫ coprod.inr) := rfl
  rw [houter]
  by_cases hyx : y = x
  · have hb := model_branch T M (S).quantifierEquality other ((S).quantifierOriginal ≫ coprod.inr)
      q true (heq true (iff_of_true hyx rfl))
    simp only [↓reduceIte] at hb
    erw [hb,(F T M).map_comp_apply (S).quantifierOriginal
      (coprod.inr (C := PredicateCategory T) («X» := ⊤_ (PredicateCategory T)) («Y» := Y)) q,
      optionCode_inr T M Y ((F T M).map (S).quantifierOriginal q),hold]
    simp only [hyx,↓reduceIte]
    rfl
  · have hb := model_branch T M (S).quantifierEquality other ((S).quantifierOriginal ≫ coprod.inr)
      q false (heq false (iff_of_false hyx Bool.false_ne_true))
    simp only [Bool.false_eq_true,↓reduceIte] at hb
    rw [hb]
    by_cases hc : allowed
    · have hcpoint : (F T M).map (S).captureAllowed q = (F T M).map (Two.constant Q true) q := by
        simpa only [hc,↓reduceIte] using hcap
      have hg := model_branch T M (S).captureAllowed OptionSyntax.fail
        (input ≫ OptionSyntax.coefficient (S).quantifierConstructor) q true hcpoint
      simp only [↓reduceIte] at hg
      erw [hg,hgood']
      by_cases hs : π₂ (optionCode T M Y child) = 1 <;>
        simp only [hyx,hc,hs,↓reduceIte,true_and]
    · have hcpoint : (F T M).map (S).captureAllowed q = (F T M).map (Two.constant Q false) q := by
        simpa only [hc,↓reduceIte] using hcap
      have hg := model_branch T M (S).captureAllowed OptionSyntax.fail
        (input ≫ OptionSyntax.coefficient (S).quantifierConstructor) q false hcpoint
      simp only [Bool.false_eq_true,↓reduceIte] at hg
      erw [hg,optionCode_fail T M (C := Y) q]
      simp only [hyx,hc,↓reduceIte,false_and]

/-- The same actual operation, in opaque scalar form for applying the
five separately proved coordinate equations. -/
theorem quantifierSubstitutionResult_coordinate_value (q : Obj T M Q) :
    optionCode T M Y ((F T M).map (S).quantifierSubstitutionResult q) =
      quantifierResultValue V σ π d
        ((F T M).map (prod.fst ≫ prod.fst : Q ⟶ V) q).val
        ((F T M).map (prod.snd ≫ prod.fst : Q ⟶ V) q).val
        ((F T M).map (prod.snd ≫ prod.snd ≫ prod.fst : Q ⟶ Y) q).val
        ((F T M).map (prod.fst ≫ prod.snd : Q ⟶ (S).algebra.a.1) q).val
        (optionCode T M Y ((F T M).map
          (prod.snd ≫ prod.snd ≫ prod.snd : Q ⟶ OptionSyntax.obj Y) q)) :=
  quantifierSubstitutionResult_value T V σ π d M q

end CategoricalEssentialIncompleteness.V46.ConcreteNamedComparison
