/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46DerivationStandardInduction

/-! # Conclusion induction through the original typed premises -/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticLists
namespace CategoricalEssentialIncompleteness.V46.SyntacticDerivation.StandardInduction
variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] {Fm : PredicateCategory T} {bound : ℕ}
variable (R : RulePresentation Fm bound)

/-- Read the kth prescribed premise at the actual rule label. The
source is the original rule-input pullback, not a shared formula fiber. -/
def typedPremise (i : Fin (bound + 1)) (k : Fin i.val) :
    R.ruleObject (derivationAlgebra T R).a i ⟶ Fm :=
  pullback.fst (R.premises i) (finitePowerMap (derivationAlgebra T R).a.hom i.val) ≫
    R.premises i ≫ finiteChild T Fm i.val k

theorem typedChild_conclusion (i : Fin (bound + 1)) (k : Fin i.val) :
    typedChild T R i k ≫ (derivationAlgebra T R).a.hom = typedPremise T R i k := by
  unfold typedChild ruleChildren typedPremise
  rw [Category.assoc,← finiteChild_natural,← Category.assoc,← pullback.condition]
  exact Category.assoc _ _ _

@[simp] theorem finiteChild_one (X : PredicateCategory T) (k : Fin 1) :
    finiteChild T X 1 k = 𝟙 X := by
  simp [finiteChild,PolynomialComparison.powerIso,powerProjection]

@[simp] theorem finiteChild_two_zero (X : PredicateCategory T) :
    finiteChild T X 2 0 = (prod.fst : X ⨯ X ⟶ X) := by
  simp [finiteChild,PolynomialComparison.powerIso,powerProjection,SyntaxPolynomial.power]
  change 𝟙 _ ≫ Fin.lastCases prod.snd (fun _ : Fin 1 => prod.fst ≫ 𝟙 X) (Fin.castSucc (0 : Fin 1)) = _
  simp only [Fin.lastCases_castSucc,Category.id_comp,Category.comp_id]

@[simp] theorem finiteChild_two_one (X : PredicateCategory T) :
    finiteChild T X 2 1 = (prod.snd : X ⨯ X ⟶ X) := by
  simp [finiteChild,PolynomialComparison.powerIso,powerProjection,SyntaxPolynomial.power]
  change 𝟙 _ ≫ Fin.lastCases prod.snd (fun _ : Fin 1 => prod.fst ≫ 𝟙 X) (Fin.last 1) = _
  simp only [Fin.lastCases_last,Category.id_comp]

variable [ℕ↓[ℒₒᵣ] ⊧* T]

/-- Rule closure of an external formula predicate implies that it holds
on every standard conclusion of the constructed derivation object. -/
theorem conclusion_induction (P : Obj T ℕ Fm → Prop)
    (step : ∀ (i : Fin (bound + 1))
      (r : Obj T ℕ (R.ruleObject (derivationAlgebra T R).a i)),
      (∀ k : Fin i.val, P ((F T ℕ).map (typedPremise T R i k) r)) →
        P ((F T ℕ).map (R.ruleConclusion (derivationAlgebra T R).a i) r)) :
    ∀ d : Obj T ℕ (derivationAlgebra T R).a.left,
      P ((F T ℕ).map (derivationAlgebra T R).a.hom d) := by
  apply nat_rule_induction T R
    (fun d => P ((F T ℕ).map (derivationAlgebra T R).a.hom d))
  intro i r ih
  rw [← Functor.map_comp_apply,derivationConstructor_conclusion]
  apply step i r
  intro k
  rw [← typedChild_conclusion,Functor.map_comp_apply]
  exact ih k

end CategoricalEssentialIncompleteness.V46.SyntacticDerivation.StandardInduction
