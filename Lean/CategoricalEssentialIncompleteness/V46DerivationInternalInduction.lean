/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46DerivationStandardInduction

/-! # Internal rule induction on numerical derivation codes -/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticLists

namespace CategoricalEssentialIncompleteness.V46.SyntacticDerivation.InternalInduction

open StandardInduction

variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
variable (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T]
variable {Fm : PredicateCategory T} {bound : ℕ} (R : RulePresentation Fm bound)

/-- A Pi-one predicate closed under the actual typed rule constructors
holds on every internal derivation code, including nonstandard codes. -/
theorem model_rule_induction (φ : 𝚷₁.Semiformula M 1)
    (step : ∀ (i : Fin (bound + 1))
      (r : Obj T M (R.ruleObject (derivationAlgebra T R).a i)),
      (∀ k : Fin i.val,
        φ.val.Eval ![((F T M).map (typedChild T R i k) r).val] id) →
      φ.val.Eval ![((F T M).map (derivationConstructor T R i) r).val] id) :
    ∀ d : Obj T M (derivationAlgebra T R).a.left, φ.val.Eval ![d.val] id := by
  let : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 := models_of_subtheory (U := T) inferInstance
  let Q : M → Prop := fun n =>
    ∀ d : Obj T M (derivationAlgebra T R).a.left,
      len d.val < n → φ.val.Eval ![d.val] id
  have hQ : 𝚷₁-Predicate Q := by
    let C : 𝚺₁.Semiformula M 1 := (derivationAlgebra T R).a.left.rew Rew.emb
    let L : 𝚺₁.Semiformula M 2 := lenDef.rew Rew.emb
    refine ⟨.mkPi “n. ∀ d l, !C.val d → !L.val l d → l < n → !φ.val d”, ?_⟩
    intro v
    simp [C, L, Q, Obj, PredicateInterpretation.Obj]
  have all : ∀ n : M, Q n := by
    intro n
    induction n using ISigma1.pi1_succ_induction
    · exact hQ
    case zero =>
      intro d hd
      exact False.elim (not_lt_zero hd)
    case succ n ih =>
      intro d hd
      obtain ⟨i, r, hr⟩ := derivation_constructor_cases T M R d
      subst d
      apply step i r
      intro k
      apply ih
      exact lt_of_lt_of_le (typed_children_smaller T R M i r k)
        (Arithmetic.lt_succ_iff_le.mp hd)
  intro d
  exact all (len d.val + 1) d (by simp)

end CategoricalEssentialIncompleteness.V46.SyntacticDerivation.InternalInduction
