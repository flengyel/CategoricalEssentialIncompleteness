/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerDerivationWordInductionRank
public import Mathlib.CategoryTheory.Limits.Types.Coproducts

/-! # External induction on the actual successful uniform derivations

The predicate is arbitrary and need not be uniformly enumerable. The
proof uses the literal tree rank. It does not infer preservation of
initiality by the underlying-set functor.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.RestrictionCategory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness.V46.Miller.Derivation.WordInduction
open SyntacticDerivation SyntacticSyntax
variable {P : Uniform.Family} {F : Total.TotalCategory P} {N : ℕ} (R : RulePresentation F N)
local notation "U" => (Total.underlying (P := P))
local notation "A" => wordAlgebra R

theorem constructor_cases (d : (U).obj (A).a.left) :
    ∃ (i : Fin (N+1)) (r : (U).obj (R.ruleObject (A).a i)),
      (U).map (constructor R i) r=d := by
  let : IsIso (A).str := Endofunctor.Algebra.Initial.str_isIso (wordInitial R)
  let e := (Over.forget F).mapIso (asIso (A).str)
  let j := ((U).mapIso e).toEquiv
  let input := j.symm d
  have hd : (U).map (A).str.left input=d := j.apply_symm_apply d
  obtain ⟨i,r,hr⟩ := Cofan.inj_jointly_surjective_of_isColimit
    (isColimitOfHasCoproductOfPreservesColimit (U) (R.ruleObject (A).a)) input
  change (U).map (Sigma.ι (R.ruleObject (A).a) i) r=input at hr
  refine ⟨i,r,?_⟩
  erw [constructor,CategoryTheory.Functor.map_comp_apply,hr]
  exact hd

/-- Every actual child tuple is ordered by its original finite power;
the nullary case has no induction premises. -/
theorem word_rule_induction (H : (U).obj (A).a.left → Prop)
    (step : ∀ (i : Fin (N+1)) (r : (U).obj (R.ruleObject (A).a i)),
      (∀ k : Fin i.val,H ((U).map (typedChild R i k) r)) →
        H ((U).map (constructor R i) r)) :
    ∀ d : (U).obj (A).a.left,H d := by
  have aux : ∀ n : ℕ,∀ d : (U).obj (A).a.left,FFL.FirstOrder.Arithmetic.len d.val=n → H d := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro d hd
      obtain ⟨i,r,hr⟩ := constructor_cases R d
      subst d
      apply step i r
      intro k
      exact ih (FFL.FirstOrder.Arithmetic.len ((U).map (typedChild R i k) r).val)
        (by simpa only [hd] using typed_children_smaller R i r k) _ rfl
  intro d
  exact aux (FFL.FirstOrder.Arithmetic.len d.val) d rfl

/-- Closure of any external formula property under the original typed
rules suffices for every actual constructed conclusion. -/
theorem conclusion_induction (H : (U).obj F → Prop)
    (step : ∀ (i : Fin (N+1)) (r : (U).obj (R.ruleObject (A).a i)),
      (∀ k : Fin i.val,H ((U).map (typedPremise R i k) r)) →
        H ((U).map (R.ruleConclusion (A).a i) r)) :
    ∀ d : (U).obj (A).a.left,H ((U).map (wordConclusion R) d) := by
  apply word_rule_induction R (fun d => H ((U).map (wordConclusion R) d))
  intro i r ih
  erw [← CategoryTheory.Functor.map_comp_apply,constructor_conclusion]
  apply step i r
  intro k
  erw [← typedChild_conclusion,CategoryTheory.Functor.map_comp_apply]
  exact ih k

end CategoricalEssentialIncompleteness.V46.Miller.Derivation.WordInduction
