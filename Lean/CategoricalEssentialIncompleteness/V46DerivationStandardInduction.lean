/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46DerivationStandardInductionRank
public import Mathlib.CategoryTheory.Limits.Types.Coproducts
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-! # Rule induction on the constructed standard derivation codes

The model functor is used only to preserve isomorphisms and finite
coproducts. Well-founded induction uses the proved decrease of the actual
standard node count, without an assumption that the functor preserves
initial algebras.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticLists
namespace CategoricalEssentialIncompleteness.V46.SyntacticDerivation.StandardInduction
variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]

section Models
variable (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T]

theorem model_sigma_cases (n : ℕ) (A : Fin (n + 1) → PredicateCategory T)
    (z : Obj T M (∐ A)) :
    ∃ (i : Fin (n + 1)) (a : Obj T M (A i)), (F T M).map (Sigma.ι A i) a = z := by
  have h := isColimitOfHasCoproductOfPreservesColimit (F T M) A
  exact Cofan.inj_jointly_surjective_of_isColimit h z

variable {F₀ : PredicateCategory T} {bound : ℕ} (R : RulePresentation F₀ bound)

/-- The interpreted constructor is surjective because the constructed
algebra structure is an isomorphism; finite coproduct preservation then
exposes one original typed rule input. -/
theorem derivation_constructor_cases (d : Obj T M (derivationAlgebra T R).a.left) :
    ∃ (i : Fin (bound + 1)) (r : Obj T M (R.ruleObject (derivationAlgebra T R).a i)),
      (F T M).map (derivationConstructor T R i) r = d := by
  let : IsIso (derivationAlgebra T R).str :=
    Endofunctor.Algebra.Initial.str_isIso (derivationInitial T R)
  let e := (Over.forget F₀).mapIso (asIso (derivationAlgebra T R).str)
  let equiv := ((F T M).mapIso e).toEquiv
  let input := equiv.symm d
  have hd : (F T M).map (derivationAlgebra T R).str.left input = d :=
    equiv.apply_symm_apply d
  obtain ⟨i,r,hr⟩ := model_sigma_cases T M bound (R.ruleObject (derivationAlgebra T R).a) input
  refine ⟨i,r,?_⟩
  rw [derivationConstructor,Functor.map_comp_apply,hr]
  exact hd

end Models

section Standard
variable [ℕ↓[ℒₒᵣ] ⊧* T]
variable {F₀ : PredicateCategory T} {bound : ℕ} (R : RulePresentation F₀ bound)

/-- Any external predicate on standard derivation codes that is closed
under the actual typed constructors holds on the constructed carrier.
For the standard-code soundness application, T is PA. -/
theorem nat_rule_induction
    (P : Obj T ℕ (derivationAlgebra T R).a.left → Prop)
    (step : ∀ (i : Fin (bound + 1)) (r : Obj T ℕ (R.ruleObject (derivationAlgebra T R).a i)),
      (∀ k : Fin i.val, P ((F T ℕ).map (typedChild T R i k) r)) →
        P ((F T ℕ).map (derivationConstructor T R i) r)) :
    ∀ d : Obj T ℕ (derivationAlgebra T R).a.left, P d := by
  have h : ∀ n : ℕ, ∀ d : Obj T ℕ (derivationAlgebra T R).a.left, len d.val = n → P d := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro d hd
        obtain ⟨i,r,hr⟩ := derivation_constructor_cases T ℕ R d
        subst d
        apply step i r
        intro k
        apply ih (len ((F T ℕ).map (typedChild T R i k) r).val)
          (by simpa only [hd] using typed_children_smaller T R ℕ i r k)
          ((F T ℕ).map (typedChild T R i k) r) rfl
  exact fun d => h (len d.val) d rfl

end Standard
end CategoricalEssentialIncompleteness.V46.SyntacticDerivation.StandardInduction
